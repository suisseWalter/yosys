/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *            (C) 2019  Eddie Hung <eddie@fpgeh.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/cost.h"
#include "kernel/ff.h"
#include "kernel/gzip.h"
#include "kernel/modtools.h"
#include "kernel/sigtools.h"
#include "kernel/timinginfo.h"
#include "kernel/yosys.h"
#include "libs/json11/json11.hpp"
#include "passes/techmap/libparse.h"
#include <charconv>
#include <deque>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct cell_delay_t {
	double delay;
	bool is_flipflop;
	vector<double> single_parameter_delay;
	vector<vector<double>> double_parameter_delay;
	vector<string> parameter_names;
};

struct StaWorker {
	Design *design;
	Module *module;
	SigMap sigmap;

	struct t_data {
		Cell *driver;
		IdString dst_port, src_port;
		vector<tuple<SigBit, int, IdString>> fanouts;
		SigBit backtrack;
		t_data() : driver(nullptr) {}
	};
	dict<SigBit, t_data> data;
	std::deque<SigBit> queue;
	struct t_endpoint {
		Cell *sink;
		IdString port;
		int required;
		t_endpoint() : sink(nullptr), required(0) {}
	};
	dict<SigBit, t_endpoint> endpoints;

	int maxarrival;
	SigBit maxbit;

	pool<SigBit> driven;

	StaWorker(RTLIL::Module *module) : design(module->design), module(module), sigmap(module), maxarrival(0)
	{
		TimingInfo timing;

		pool<IdString> unrecognised_cells;

		for (auto cell : module->cells()) {
			Module *inst_module = design->module(cell->type);
			if (!inst_module) {
				if (unrecognised_cells.insert(cell->type).second)
					log_warning("Cell type '%s' not recognised! Ignoring.\n", log_id(cell->type));
				continue;
			}

			if (!inst_module->get_blackbox_attribute()) {
				log_warning("Cell type '%s' is not a black- nor white-box! Ignoring.\n", log_id(cell->type));
				continue;
			}

			IdString derived_type = inst_module->derive(design, cell->parameters);
			inst_module = design->module(derived_type);
			log_assert(inst_module);

			if (!timing.count(derived_type)) {
				auto &t = timing.setup_module(inst_module);
				if (t.has_inputs && t.comb.empty() && t.arrival.empty() && t.required.empty())
					log_warning("Module '%s' has no timing arcs!\n", log_id(cell->type));
			}

			auto &t = timing.at(derived_type);
			if (t.comb.empty() && t.arrival.empty() && t.required.empty())
				continue;

			pool<std::pair<SigBit, TimingInfo::NameBit>> src_bits, dst_bits;

			for (auto &conn : cell->connections()) {
				auto rhs = sigmap(conn.second);
				for (auto i = 0; i < GetSize(rhs); i++) {
					const auto &bit = rhs[i];
					if (!bit.wire)
						continue;
					TimingInfo::NameBit namebit(conn.first, i);
					if (cell->input(conn.first)) {
						src_bits.insert(std::make_pair(bit, namebit));

						auto it = t.required.find(namebit);
						if (it == t.required.end())
							continue;
						auto r = endpoints.insert(bit);
						if (r.second || r.first->second.required < it->second.first) {
							r.first->second.sink = cell;
							r.first->second.port = conn.first;
							r.first->second.required = it->second.first;
						}
					}
					if (cell->output(conn.first)) {
						dst_bits.insert(std::make_pair(bit, namebit));
						auto &d = data[bit];
						d.driver = cell;
						d.dst_port = conn.first;
						driven.insert(bit);

						auto it = t.arrival.find(namebit);
						if (it == t.arrival.end())
							continue;
						const auto &s = it->second.second;
						if (cell->hasPort(s.name)) {
							auto s_bit = sigmap(cell->getPort(s.name)[s.offset]);
							if (s_bit.wire)
								data[s_bit].fanouts.emplace_back(bit, it->second.first, s.name);
						}
					}
				}
			}

			for (const auto &s : src_bits)
				for (const auto &d : dst_bits) {
					auto it = t.comb.find(TimingInfo::BitBit(s.second, d.second));
					if (it == t.comb.end())
						continue;
					data[s.first].fanouts.emplace_back(d.first, it->second, s.second.name);
				}
		}

		for (auto port_name : module->ports) {
			auto wire = module->wire(port_name);
			if (wire->port_input) {
				for (const auto &b : sigmap(wire)) {
					queue.emplace_back(b);
					driven.insert(b);
				}
				// All primary inputs to arrive at time zero
				wire->set_intvec_attribute(ID::sta_arrival, std::vector<int>(GetSize(wire), 0));
			}
			if (wire->port_output)
				for (const auto &b : sigmap(wire))
					if (b.wire)
						endpoints.insert(b);
		}
	}

	void run()
	{
		while (!queue.empty()) {
			auto b = queue.front();
			queue.pop_front();
			auto it = data.find(b);
			if (it == data.end())
				continue;
			const auto &src_arrivals = b.wire->get_intvec_attribute(ID::sta_arrival);
			log_assert(GetSize(src_arrivals) == GetSize(b.wire));
			auto src_arrival = src_arrivals[b.offset];
			for (const auto &d : it->second.fanouts) {
				const auto &dst_bit = std::get<0>(d);
				auto dst_arrivals = dst_bit.wire->get_intvec_attribute(ID::sta_arrival);
				if (dst_arrivals.empty())
					dst_arrivals = std::vector<int>(GetSize(dst_bit.wire), -1);
				else
					log_assert(GetSize(dst_arrivals) == GetSize(dst_bit.wire));
				auto &dst_arrival = dst_arrivals[dst_bit.offset];
				auto new_arrival = src_arrival + std::get<1>(d);
				if (dst_arrival < new_arrival) {
					auto dst_wire = dst_bit.wire;
					dst_arrival = std::max(dst_arrival, new_arrival);
					dst_wire->set_intvec_attribute(ID::sta_arrival, dst_arrivals);
					queue.emplace_back(dst_bit);

					data[dst_bit].backtrack = b;
					data[dst_bit].src_port = std::get<2>(d);

					auto it = endpoints.find(dst_bit);
					if (it != endpoints.end())
						new_arrival += it->second.required;
					if (new_arrival > maxarrival && driven.count(b)) {
						maxarrival = new_arrival;
						maxbit = dst_bit;
					}
				}
			}
		}

		auto b = maxbit;
		if (b == SigBit()) {
			log("No timing paths found.\n");
			return;
		}

		log("Latest arrival time in '%s' is %d:\n", log_id(module), maxarrival);
		auto it = endpoints.find(maxbit);
		if (it != endpoints.end() && it->second.sink)
			log("  %6d %s (%s.%s)\n", maxarrival, log_id(it->second.sink), log_id(it->second.sink->type), log_id(it->second.port));
		else {
			log("  %6d (%s)\n", maxarrival, b.wire->port_output ? "<primary output>" : "<unknown>");
			if (!b.wire->port_output)
				log_warning("Critical-path does not terminate in a recognised endpoint.\n");
		}
		auto jt = data.find(b);
		while (jt != data.end()) {
			int arrival = b.wire->get_intvec_attribute(ID::sta_arrival)[b.offset];
			if (jt->second.driver) {
				log("           %s\n", log_signal(b));
				log("  %6d %s (%s.%s->%s)\n", arrival, log_id(jt->second.driver), log_id(jt->second.driver->type),
				    log_id(jt->second.src_port), log_id(jt->second.dst_port));
			} else if (b.wire->port_input)
				log("  %6d   %s (%s)\n", arrival, log_signal(b), "<primary input>");
			else
				log_abort();
			b = jt->second.backtrack;
			jt = data.find(b);
		}

		std::map<int, unsigned> arrival_histogram;
		for (const auto &i : endpoints) {
			const auto &b = i.first;
			if (!driven.count(b))
				continue;

			if (!b.wire->attributes.count(ID::sta_arrival)) {
				log_warning("Endpoint %s.%s has no (* sta_arrival *) value.\n", log_id(module), log_signal(b));
				continue;
			}

			auto arrival = b.wire->get_intvec_attribute(ID::sta_arrival)[b.offset];
			if (arrival < 0) {
				log_warning("Endpoint %s.%s has no (* sta_arrival *) value.\n", log_id(module), log_signal(b));
				continue;
			}
			arrival += i.second.required;
			arrival_histogram[arrival]++;
		}
		// Adapted from https://github.com/YosysHQ/nextpnr/blob/affb12cc27ebf409eade062c4c59bb98569d8147/common/timing.cc#L946-L969
		if (arrival_histogram.size() > 0) {
			unsigned num_bins = 20;
			unsigned bar_width = 60;
			auto min_arrival = arrival_histogram.begin()->first;
			auto max_arrival = arrival_histogram.rbegin()->first;
			auto bin_size = std::max<unsigned>(1, ceil((max_arrival - min_arrival + 1) / float(num_bins)));
			std::vector<unsigned> bins(num_bins);
			unsigned max_freq = 0;
			for (const auto &i : arrival_histogram) {
				auto &bin = bins[(i.first - min_arrival) / bin_size];
				bin += i.second;
				max_freq = std::max(max_freq, bin);
			}
			bar_width = std::min(bar_width, max_freq);

			log("\n");
			log("Arrival histogram:\n");
			log(" legend: * represents %d endpoint(s)\n", max_freq / bar_width);
			log("         + represents [1,%d) endpoint(s)\n", max_freq / bar_width);
			for (int i = num_bins - 1; i >= 0; --i)
				log("(%6d, %6d] |%s%c\n", min_arrival + bin_size * (i + 1), min_arrival + bin_size * i,
				    std::string(bins[i] * bar_width / max_freq, '*').c_str(), (bins[i] * bar_width) % max_freq > 0 ? '+' : ' ');
		}
	}
};
struct Sta_Path {
	double delay;
	RTLIL::IdString wire;
	vector<Cell *> cells;
	Sta_Path(double d, RTLIL::IdString p, vector<Cell *> c) : delay(d), wire(p), cells(c) {}
	Sta_Path() : delay(0), wire(), cells() {}
	Sta_Path(const Sta_Path &other) : delay(other.delay), wire(other.wire), cells(other.cells) {}
	Hasher hash_into(Hasher h) const
	{
		// h.eat(delay); //the delay is not required for the hash, as it's a result of the cells.
		// h.eat(wire);
		for (auto &cell : cells)
			h.eat(cell->name);
		return h;
	}
	void add_delay(Cell *cell, dict<IdString, cell_delay_t> cell_delays)
	{
		if (cell == nullptr) {
			log_error("Cell is null, cannot add delay.\n");
		}
		if (!cell_delays.count(cell->type)) {
			// printf("Cell type %s not found in cell delay map.\n", cell->type.c_str());
			return; // return current delay if cell type not found
		}
		auto cell_delay = cell_delays.at(cell->type);
		// deal with parameterized delays.
		// extract width of ports from the cells:
		vector<double> widths;
		if (cell_delay.parameter_names.size() > 0) {
			for (auto &it : cell_delay.parameter_names) {
				RTLIL::IdString port_name;
				// TODO: there has to be a better way to do this
				if (it == "A") {
					port_name = ID::A;
				} else if (it == "B") {
					port_name = ID::B;
				} else if (it == "Y") {
					port_name = ID::Y;
				} else if (it == "Q") {
					port_name = ID::Q;
				} else if (it == "S") {
					port_name = ID::S;
				} else {
					port_name = ID(it);
				}
				if (cell->hasPort(port_name)) {
					int width = GetSize(cell->getPort(port_name));
					widths.push_back(width);
				} else {
					widths.push_back(0);
				}
			}
		} else {
			int width_a = cell->hasPort(ID::A) ? GetSize(cell->getPort(ID::A)) : 0;
			int width_b = cell->hasPort(ID::B) ? GetSize(cell->getPort(ID::B)) : 0;
			int width_y = cell->hasPort(ID::Y) ? GetSize(cell->getPort(ID::Y)) : 0;
			int width_q = cell->hasPort(ID::Q) ? GetSize(cell->getPort(ID::Q)) : 0;
			int max_width = max<int>({width_a, width_b, width_y, width_q});
			widths.push_back(max_width);
		}
		if (cell_delay.single_parameter_delay.size() > 0) {
			if (widths.size() != 1) {
				// we need to have exactly one parameter for single parameter delay.
				log_error("Cell %s has single parameter delay, but has %d parameters.\n", cell->name.c_str(), widths.size());
			}
			if (cell_delay.single_parameter_delay.size() > widths.at(0) - 1) {
				delay += cell_delay.single_parameter_delay.at(widths.at(0) - 1);
			} else {
				delay += cell_delay.single_parameter_delay.back();
			}
		} else if (cell_delay.double_parameter_delay.size() > 0) {
			if (widths.size() != 2) {
				// we need to have exactly two parameters for double parameter delay.
				log_error("Cell %s has double parameter delay, but has %d parameters.\n", cell->name.c_str(), widths.size());
			}
			int width_a = widths.at(1);
			int width_b = widths.at(0);
			if (width_a > 0 && width_b > 0) {
				if (cell_delay.double_parameter_delay.size() > width_a - 1 &&
				    cell_delay.double_parameter_delay.at(width_a - 1).size() > width_b - 1) {
					delay += cell_delay.double_parameter_delay.at(width_a - 1).at(width_b - 1);
				} else {
					delay += cell_delay.double_parameter_delay.back().back();
				}
			} else {
				log_error("Cell %s has double parameter delay, but has zero width parameters.\n", cell->name.c_str());
			}
		} else {
			delay += cell_delay.delay;
		}

		return;
	}
	bool operator==(const Sta_Path &other) const { return delay == other.delay && wire == other.wire && cells == other.cells; }
};
struct Sta2Worker {
	Design *design;
	std::deque<Sta_Path> queue;
	dict<IdString, cell_delay_t> cell_delays;
	std::map<RTLIL::IdString, std::pair<Sta_Path, Sta_Path>> analysed;
	pool<Sta_Path> analysed_max_paths;
	pool<Sta_Path> analysed_min_paths;
	std::map<RTLIL::IdString, double> cell_max_analysed;
	std::map<RTLIL::IdString, double> cell_min_analysed;
	std::map<RTLIL::Module *, ModWalker> modwalkers;

	Sta2Worker(RTLIL::Design *design, dict<IdString, cell_delay_t> cell_delay) : design(design), cell_delays(cell_delay) {}

	void run(RTLIL::Module *module, bool hold_violations, bool setup_violations)
	{
		auto modules = design->modules().to_vector();
		if (module != nullptr) {
			modules = {module};
		}
		printf("modules: %d \n", modules.size());
		for (auto module : modules) {
			SigMap sigmap(module);
			ModWalker modwalker(design);
			modwalker.setup(module);
			printf("module: %s \n", module->name.c_str());
			for (auto port : module->ports) {
				auto wire = module->wire(port);
				if (wire->port_input) {
					// printf("input port: %s \n", port.c_str());
					for (auto &bit : sigmap(wire)) {

						auto first_cells = modwalker.signal_consumers[bit];
						for (auto &f_cell : first_cells) {
							if (f_cell.cell == nullptr) {
								printf("no cell for input port %s \n", port.c_str());
								continue;
							}

							vector<Cell *> new_vector = {f_cell.cell};
							Sta_Path p(0, f_cell.cell->name, new_vector);
							p.add_delay(f_cell.cell, cell_delays);
							queue.push_back(p);
						}
					}
				}
			}
			for (auto cell : module->cells()) {
				//printf("cell: %s, %s, %u \n", cell->name.c_str(), cell->type.c_str(),
				//       (cell_delays.count(cell->type) ? cell_delays.at(cell->type).is_flipflop : 100));
				//  improve this detection to include FF from lib files.
				if (RTLIL::builtin_ff_cell_types().count(cell->type) ||
				    (cell_delays.count(cell->type) && cell_delays.at(cell->type).is_flipflop)) {
					vector<Cell *> new_vector;
					new_vector.push_back(cell);
					Sta_Path p(0, cell->name, new_vector);
					p.add_delay(cell, cell_delays);
					queue.push_back(p);
				} else {
					continue;
				}

				while (queue.size() > 0) {
					auto entry = queue.back();
					queue.pop_back();
					auto cell = entry.cells.back();

					// printf("analysing cell: %s %f \n", cell->name.c_str(), entry.delay);
					if (design->module(cell->type) == nullptr) {
						// printf("cell %s is just a cell. \n", cell->name.c_str());

					} else if (design->module(cell->type)->get_blackbox_attribute()) {
						
						if (!cell_delays.count(cell->type)) {
							//printf("cell %s is a blackbox without timing information of type %s. \n", cell->name.c_str(), cell->type.c_str());
							continue;
						} 
						
					}
					pool<RTLIL::IdString> analysed_cells;
					auto signals = modwalker.cell_outputs[cell];
					// printf("signals: %d \n", signals.size());
					for (auto sig : signals) {
						auto consumers = modwalker.signal_consumers[sig];
						// printf("consumers: %d \n", consumers.size());

						// figure out if we have reached a output cell.
						if (sig.wire->port_output) {
							// if we have reached a output port, print it.
							printf("output port: %s \n", sig.wire->name.c_str());
							if (analysed.count(sig.wire->name)) {
								if (analysed[sig.wire->name].second.delay < entry.delay) {
									// reached new maximum delay for this cell.
									analysed[sig.wire->name].second = entry;
								} else if (analysed[sig.wire->name].first.delay > entry.delay) {
									// reached new minimum delay for this cell.
									analysed[sig.wire->name].first = entry;
								}
							} else {
								analysed[sig.wire->name] = pair<Sta_Path, Sta_Path>(entry, entry);
							}
						}

						if (consumers.empty()) {
							// printf("no consumers for %s \n", cell->name.c_str());

							continue;
						}
						//printf("consumers: %d \n", consumers.size());
						Yosys::RTLIL::Cell *last_consumer = nullptr;
						for (auto &consumer_bit : consumers) {
							auto consumer = consumer_bit.cell;
							if (analysed_cells.count(consumer->name)) {
								// printf("already analysed cell %s \n", consumer->name.c_str());
								continue;
							}

							analysed_cells.insert(consumer->name);

							double delay = entry.delay + 1; // TODO fix this
							// if we have already reached this cell skip it if between max or min.
							if (cell_max_analysed.count(consumer->name) &&
							    cell_max_analysed[consumer->name] > entry.delay) {
								if (!hold_violations)
									continue; // if we are not looking for hold violations, skip this.
								if (cell_min_analysed.count(consumer->name) &&
								    cell_min_analysed[consumer->name] < entry.delay) {
									continue;
								} else {
									cell_min_analysed[consumer->name] = delay;
								}
							} else {
								cell_max_analysed[consumer->name] = delay;
							}

							Sta_Path new_entry(entry.delay, entry.wire, entry.cells);
							new_entry.cells.push_back(consumer);
							new_entry.add_delay(consumer, cell_delays);
							// we have found a cell that is connected.
							if (RTLIL::builtin_ff_cell_types().count(consumer->type) ||
							    (cell_delays.count(consumer->type) && cell_delays.at(consumer->type).is_flipflop)) {
								// check that we don't have a clk or rst port. In that case we don't want to include
								// this.
								//printf("found a FF: %s %f \n", consumer->name.c_str(), new_entry.delay);
								if (RTLIL::builtin_ff_cell_types().count(consumer->type)){
									FfData ff(nullptr, consumer);
									/* printf("sig: %d \n", sigmap(sig));
									printf("ff sig clk: %d \n", sigmap(ff.sig_clk).size());
									printf("ff sig clr: %d \n", sigmap(ff.sig_clr).size()); */
									if (sigmap(sig) == sigmap(ff.sig_clk)) {
										printf("analysing a clk, ignoring: %s \n", consumer->name.c_str());
										continue;
									}
									if (sigmap(ff.sig_clr).size() == 1 && sigmap(sig) == sigmap(ff.sig_clr)) {
										printf("analysing a rst , ignoring: %s \n", consumer->name.c_str());
										continue;
									}
								}
								if (analysed.count(entry.cells.front()->name)) {

									if (analysed[consumer->name].second.delay < new_entry.delay) {
										// reached new maximum delay for this cell.
										// printf("reached new max delay for %s: %f \n",
										// consumer->name.c_str(), new_entry.delay);
										analysed[consumer->name].second = new_entry;
										continue;
									} else if (analysed[consumer->name].first.delay > new_entry.delay) {
										// reached new minimum delay for this cell.
										// printf("reached new min delay for %s: %f \n",
										// consumer->name.c_str(), new_entry.delay);
										analysed[consumer->name].first = new_entry;
										continue;
									}
								} else {

									analysed[consumer->name] = pair<Sta_Path, Sta_Path>(new_entry, new_entry);
								}

								// printf("reached ff: %s %f \n", consumer->name.c_str(), entry.delay);
								/*for (auto interl_walked_cell : entry.second){
									printf("%s -> ", interl_walked_cell->name.c_str());
								}*/
								/* if (entry.delay > 40){
									printf("exiting \n");
									printf("delay: %f \n", entry.delay);
									printf("cell: %s \n", consumer->name.c_str());
									printf("cells: %u \n", entry.cells.size());
									exit(1);
								}  */
							} else {
								// check for loops.
								auto loop = false;
								for (auto &it : entry.cells) {
									if (it->name == consumer->name) {
										printf("loop detected: %s %s \n", cell->name.c_str(),
										       consumer->name.c_str());
										loop = true;
										break;
									}
								}
								if (loop)
									continue;
								/* printf("putting back on stack: %s %s %d %s %u \n", consumer->name.c_str(),
								cell->name.c_str(),
								       entry.cells.size(), entry.cells.front()->name.c_str(), queue.size()); // make a
								copy first
 */
								queue.push_back(new_entry);
								// printf("%u \n", queue.size());
							}
						}
					}
				}
			}
		}
		// print max and min of analysed paths.
		/* printf("analysed paths: %d \n", analysed.size());
		double max = 0;
		RTLIL::IdString max_cell;
		Sta_Path max_path;
		double min = 1000000;
		RTLIL::IdString min_cell;
		Sta_Path min_path;
		for (auto &it : analysed) {
			if (it.second.second.delay > max) {
				max = it.second.second.delay;
				max_cell = it.first;
				max_path = it.second.second;
			}
			if (it.second.first.delay < min) {
				min = it.second.first.delay;
				min_cell = it.first;
				min_path = it.second.first;
			}
		}

		log("max: ends at: %s, length: %f, #cells: %u \n", max_cell.c_str(), max, max_path.cells.size());
		log("path: ");
		for (auto &cell : max_path.cells) {
			log("%s -> \n", cell->name.c_str());
		}
		log("\n");
		log("min: ends at: %s, length: %f, #cells: %u \n", min_cell.c_str(), min, min_path.cells.size());
		log("path: ");
		for (auto &cell : min_path.cells) {
			log("%s -> \n", cell->name.c_str());
		}
		log("\n"); */
	}
};

void read_liberty_celldelay(dict<IdString, cell_delay_t> &cell_delay, string liberty_file)
{
	std::istream *f = uncompressed(liberty_file.c_str());
	yosys_input_files.insert(liberty_file);
	LibertyParser libparser(*f, liberty_file);
	delete f;

	for (auto cell : libparser.ast->children) {
		if (cell->id != "cell" || cell->args.size() != 1)
			continue;

		const LibertyAst *ar = cell->find("delay");
		bool is_flip_flop = cell->find("ff") != nullptr;
		vector<double> single_parameter_delay;
		vector<vector<double>> double_parameter_delay;
		vector<string> port_names;
		const LibertyAst *sar = cell->find("single_delay_parameterised");
		if (sar != nullptr) {
			for (const auto &s : sar->args) {
				double value = 0;
				auto [ptr, ec] = std::from_chars(s.data(), s.data() + s.size(), value);
				// ec != std::errc() means parse error, or ptr didn't consume entire string
				if (ec != std::errc() || ptr != s.data() + s.size())
					break;
				single_parameter_delay.push_back(value);
			}
			if (single_parameter_delay.size() == 0)
				printf("error: %s\n", sar->args[single_parameter_delay.size() - 1].c_str());
			// check if it is a double parameterised delay
		}
		const LibertyAst *dar = cell->find("double_delay_parameterised");
		if (dar != nullptr) {
			for (const auto &s : dar->args) {

				// printf("value: %s\n",sar->value.c_str());
				// printf("args1: %s\n",dar->args[0].c_str());

				vector<string> sub_array;
				std::string::size_type start = 0;
				std::string::size_type end = s.find_first_of(",", start);
				while (end != std::string::npos) {
					sub_array.push_back(s.substr(start, end - start));
					start = end + 1;
					end = s.find_first_of(",", start);
				}
				sub_array.push_back(s.substr(start, end));

				vector<double> cast_sub_array;
				for (const auto &s : sub_array) {
					double value = 0;
					auto [ptr, ec] = std::from_chars(s.data() + 1, s.data() + s.size(), value);
					if (ec != std::errc() || ptr != s.data() + s.size())
						break;
					cast_sub_array.push_back(value);
				}
				double_parameter_delay.push_back(cast_sub_array);
				if (cast_sub_array.size() == 0)
					printf("error: %s\n", s.c_str());
			}
		}
		const LibertyAst *par = cell->find("port_names");
		if (par != nullptr) {
			for (const auto &s : par->args) {
				port_names.push_back(s);
				printf("port_name: '%s'\n", s.c_str());
			}
		}

		if (ar != nullptr && !ar->value.empty()) {
			string prefix = cell->args[0].substr(0, 1) == "$" ? "" : "\\";
			cell_delay[prefix + cell->args[0]] = {atof(ar->value.c_str()), is_flip_flop, single_parameter_delay, double_parameter_delay,
							      port_names};
		}
	}
}

struct StaPass : public Pass {
	StaPass() : Pass("sta", "perform static timing analysis") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    sta [options] [selection]\n");
		log("\n");
		log("This command performs static timing analysis on the design. (Only considers\n");
		log("paths within a single module, so the design must be flattened.)\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing STA pass (static timing analysis).\n");
		RTLIL::Module *top_mod = design->top_module();
		dict<IdString, cell_delay_t> cell_delay;
		bool names = false;
		bool paths = false;
		double max_delay = 0;
		double min_delay = 0;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-liberty" && argidx + 1 < args.size()) {
				string liberty_file = args[++argidx];
				rewrite_filename(liberty_file);
				read_liberty_celldelay(cell_delay, liberty_file);
				continue;
			}
			if (args[argidx] == "-top" && argidx + 1 < args.size()) {
				if (design->module(RTLIL::escape_id(args[argidx + 1])) == nullptr)
					log_cmd_error("Can't find module %s.\n", args[argidx + 1].c_str());
				top_mod = design->module(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			if (args[argidx] == "-max_delay" && argidx + 1 < args.size()) {
				argidx++;
				max_delay = atof(args[argidx].c_str());
				continue;
			}
			if (args[argidx] == "-min_delay" && argidx + 1 < args.size()) {
				argidx++;
				min_delay = atof(args[argidx].c_str());
				continue;
			}
			if (args[argidx] == "-v") {
				log("verbose mode enabled.\n");
				names = true;
				continue;
			}
			if (args[argidx] == "-vv") {
				log("very verbose mode enabled.\n");
				names = true;
				paths = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		RTLIL::Design *new_design = new RTLIL::Design;
		auto modules = design->modules().to_vector();
		for (auto &mod : modules) {
			new_design->add(mod->clone());
			auto cells = new_design->module(mod->name)->cells().to_vector();
			for (auto &cell : cells) {
				cell->set_bool_attribute(ID::keep_hierarchy, false);
			}
		}
		Pass::call(new_design, "hierarchy -check -top " + top_mod->name.str());
		Pass::call(new_design, "flatten");
		// yosys dump -m -o "out/poststa.dump"
		Pass::call(new_design, "dump -m -o \"out/poststa.dump\"");
		// Pass::call(design, "opt_clean");
		// yosys hierarchy -check -top $top_design
		// Pass::call(new_design, "show -prefix \"\" -format svg " + top_mod->name.str() );

		printf("original design number of modules: %d \n", design->modules().size());

		Sta2Worker sta(new_design, cell_delay);

		sta.run(new_design->module(top_mod->name), min_delay, 1);

		// extract  all the paths longer then max_delay
		auto max_paths = pool<Sta_Path>();
		auto min_paths = pool<Sta_Path>();
		for (auto &it : sta.analysed) {
			if (it.second.second.delay > max_delay) {
				max_paths.insert(it.second.second);
			}
			if (it.second.first.delay < min_delay) {
				min_paths.insert(it.second.first);
			}
		}

		log("Number of paths longer than max delay %f: %d \n", max_delay, max_paths.size());
		log("Number of paths shorter than min delay %f: %d \n", min_delay, min_paths.size());
		//create a ordered version of max_delays and min_delays.
		auto ordered_max_paths = vector<Sta_Path>(max_paths.begin(), max_paths.end());
		auto ordered_min_paths = vector<Sta_Path>(min_paths.begin(), min_paths.end());
		std::sort(ordered_max_paths.begin(), ordered_max_paths.end(),
			  [](const Sta_Path &a, const Sta_Path &b) { return a.delay > b.delay; });
		std::sort(ordered_min_paths.begin(), ordered_min_paths.end(),
			  [](const Sta_Path &a, const Sta_Path &b) { return a.delay < b.delay; });
		if (names) {
			for (auto &it : ordered_max_paths) {
				log("max_path: start: %s, end: %s, delay: %f, cells: %u \n", it.cells.front()->name.c_str(),
				    it.cells.back()->name.c_str(), it.delay, it.cells.size());
			}
			for (auto &it : ordered_min_paths) {
				log("min_path: start: %s, end: %s, delay: %f, cells: %u \n", it.cells.front()->name.c_str(),
				    it.cells.back()->name.c_str(), it.delay, it.cells.size());
			}
		}
		if (paths) {
			for (auto &it : max_paths) {
				log("max_path: start: %s, end: %s, delay: %f, cells: %u \n", it.cells.front()->name.c_str(),
				    it.cells.back()->name.c_str(), it.delay, it.cells.size());
				for (auto &cell : it.cells) {
					log("  cell: %s -> \n", cell->name.c_str());
				}
			}
			for (auto &it : min_paths) {
				log("min_path: start: %s, end: %s, delay: %f, cells: %u \n", it.cells.front()->name.c_str(),
				    it.cells.back()->name.c_str(), it.delay, it.cells.size());
				for (auto &cell : it.cells) {
					log("  cell: %s -> \n", cell->name.c_str());
				}
			}
		}

		// print all the max and min paths.
		log("max paths: %d \n", sta.analysed_max_paths.size());
		for (auto &path : sta.analysed_max_paths) {
			log("max path: %s, delay: %f, cells: %u \n", path.wire.c_str(), path.delay, path.cells.size());
		}
		log("min paths: %d \n", sta.analysed_min_paths.size());
		for (auto &path : sta.analysed_min_paths) {
			log("min path: %s, delay: %f, cells: %u \n", path.wire.c_str(), path.delay, path.cells.size());
		}
		/*
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-TODO") {
				continue;
			}
			break;
		}
		*/
	}
} StaPass;

PRIVATE_NAMESPACE_END
