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

#include "kernel/ff.h"
#include "kernel/modtools.h"
#include "kernel/sigtools.h"
#include "kernel/timinginfo.h"
#include "kernel/yosys.h"
#include <deque>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

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
		Hasher hash_into(Hasher h) const
		{
			//h.eat(delay); //the delay is not required for the hash, as it's a result of the cells. 
			//h.eat(wire);
			for (auto &cell : cells)
				h.eat(cell->name);
			return h;
		}
		bool operator==(const Sta_Path &other) const
		{
			return delay == other.delay && wire == other.wire && cells == other.cells;
		}
	};
struct Sta2Worker {
	Design *design;
	std::deque<Sta_Path> queue;
	std::map<RTLIL::IdString, double> analysed;
	std::map<RTLIL::IdString, double> cell_max_analysed;
	std::map<RTLIL::IdString, double> cell_min_analysed;
	std::map<RTLIL::Module *, ModWalker> modwalkers;
	
	
	Sta2Worker(RTLIL::Design *design) : design(design) {}

	void run()
	{
		// iterate through all the ff/latches/input in the design and trace the outputs. to another ff/latch/output
		// printf("design: %s \n", design->top_module()->name.c_str());
		auto modules = design->modules();

		printf("modules: %d", modules.size());
		for (auto module : design->modules()) {
			SigMap sigmap(module);
			ModWalker modwalker(design);
			modwalker.setup(module);
			printf("module: %s \n", module->name.c_str());
			for (auto port : module->ports) {
				auto wire = module->wire(port);
				if (wire->port_input) {
					printf("input port: %s \n", port.c_str());
					for (auto &bit : sigmap(wire)) {

						auto first_cells = modwalker.signal_consumers[bit];
						for (auto &f_cell : first_cells) {
							if (f_cell.cell == nullptr) {
								printf("no cell for input port %s \n", port.c_str());
								continue;
							}

							vector<Cell *> new_vector = {f_cell.cell};
							Sta_Path p(0, f_cell.cell->name, new_vector);
							queue.push_back(p);
						}
					}
				}
			}
			for (auto cell : module->cells()) {
				printf("cell: %s \n", cell->name.c_str());
				// improve this detection to include FF from lib files.
				if (RTLIL::builtin_ff_cell_types().count(cell->type)) {
					vector<Cell *> new_vector;
					new_vector.push_back(cell);
					Sta_Path p(0, cell->name, new_vector);
					queue.push_back(p);
				}
			}

			while (queue.size() > 0) {
				auto entry = queue.back();
				queue.pop_back();
				auto cell = entry.cells.back();

				// printf("analysing cell: %s %f \n", cell->name.c_str(), entry.first);
				if (design->module(cell->type) == nullptr) {
					// printf("cell %s is just a cell. \n", cell->name.c_str());

				} else if (design->module(cell->type)->get_blackbox_attribute()) {
					printf("cell %s is a blackbox. \n", cell->name.c_str());
					continue;
				}

				auto signals = modwalker.cell_outputs[cell];
				for (auto sig : signals) {
					auto consumers = modwalker.signal_consumers[sig];
					// figure out if we have reached a output cell.
					if (sig.wire->port_output) {
							// if we have reached a output port, print it.
							printf("output port: %s \n", sig.wire->name.c_str());
						}
					
					
					if (consumers.empty()) {
						printf("no consumers for %s \n", cell->name.c_str());
						
						continue;
					}
					

					Yosys::RTLIL::Cell *last_consumer = nullptr;
					for (auto &consumer_bit : consumers) {

						auto consumer = consumer_bit.cell;
						if (consumer == last_consumer) {
							// skip the same consumer, this can happen if multiple bits are connected to the same cell.
							continue;
						}
						last_consumer = consumer;
						double delay = entry.delay + 1;
						// if we have already reached this cell skip it if between max or min.
						if (cell_max_analysed.count(consumer->name) && cell_max_analysed[consumer->name] > entry.delay) {
							/* printf("skipping %s, already reached with %f \n", consumer->name.c_str(),
							       cell_max_analysed[consumer->name]); */
							continue;
						} else {
							cell_max_analysed[consumer->name] = delay;
						}
						if (cell_min_analysed.count(consumer->name) && cell_min_analysed[consumer->name] < entry.delay) {
							/* printf("skipping %s, already reached with %f \n", consumer->name.c_str(),
							       cell_min_analysed[consumer->name]); */
							continue;
						} else {
							cell_min_analysed[consumer->name] = delay;
						}
						// we have found a cell that is connected.
						if (RTLIL::builtin_ff_cell_types().count(consumer->type)) {
							if (analysed.count(entry.cells.front()->name)) {
								analysed[consumer->name] = max(analysed[consumer->name], entry.delay);
							} else {
								analysed[consumer->name] = entry.delay;
							}
							printf("reached ff: %s %f \n", consumer->name.c_str(), entry.delay);
							/*for (auto interl_walked_cell : entry.second){
								printf("%s -> ", interl_walked_cell->name.c_str());
							}
							printf("\n");
							if (entry.first > 2){
								printf("exiting \n");
								exit(1);
							} */
						} else {
							// check for loops.
							auto loop = false;
							for (auto &it : entry.cells) {
								if (it->name == consumer->name) {
									printf("loop detected: %s %s \n", cell->name.c_str(), consumer->name.c_str());
									loop = true;
								}
							}
							if (loop)
								continue;
							// printf("putting back on stack: %s %s %d \n", consumer->name.c_str(), cell->name.c_str(),
							//        entry.second.size()); // make a copy first

							Sta_Path copy(entry.delay, entry.wire, entry.cells);
							copy.cells.push_back(consumer);
							copy.delay = delay;
							queue.push_back(copy);
							// printf("%u \n", queue.size());
						}
					}
				}
			}
		}

		// print max and min of analysed paths.
		printf("analysed paths: %d \n", analysed.size());
		double max = 0;
		RTLIL::IdString max_cell;
		double min = 1000000;
		RTLIL::IdString min_cell;
		for (auto &it : analysed) {
			if (it.second > max) {
				max = it.second;
				max_cell = it.first;
			}
			if (it.second < min) {
				min = it.second;
				min_cell = it.first;
			}
		}
		printf("max: %s %f \n", max_cell.c_str(), max);
		printf("min: %s %f \n", min_cell.c_str(), min);
	}
};

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

		Sta2Worker sta(design);
		sta.run();
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
