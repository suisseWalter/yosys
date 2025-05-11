/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#include <iterator>

#include "kernel/yosys.h"
#include "kernel/celltypes.h"
#include "passes/techmap/libparse.h"
#include "kernel/cost.h"
#include "kernel/gzip.h"
#include "libs/json11/json11.hpp"
#include <charconv>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct cell_area_t {
	double area;
	bool is_sequential;
	vector<double> single_parameter_area;
	vector<vector<double>> double_parameter_area;
	vector<string> parameter_names;
};

struct statdata_t {
#define STAT_INT_MEMBERS                                                                                                                             \
	X(num_wires)                                                                                                                                 \
	X(num_wire_bits)                                                                                                                             \
	X(num_pub_wires) X(num_pub_wire_bits) X(num_ports) X(num_port_bits) X(num_memories) X(num_memory_bits) X(num_cells) X(num_processes)

#define STAT_NUMERIC_MEMBERS STAT_INT_MEMBERS X(area) X(sequential_area)

#define X(_name) unsigned int _name;
	STAT_INT_MEMBERS
#undef X
	double area = 0;
	double sequential_area = 0;
	double local_area = 0;
	double instance_area = 0;
	int num_instances = 0;
	std::map<RTLIL::IdString, unsigned int, RTLIL::sort_by_id_str> num_instances_by_type;
	std::map<RTLIL::IdString, double, RTLIL::sort_by_id_str> instances_area_by_type;
	int num_local_cells = 0;
	std::map<RTLIL::IdString, unsigned int, RTLIL::sort_by_id_str> num_local_cells_by_type;
	std::map<RTLIL::IdString, double, RTLIL::sort_by_id_str> local_cells_area_by_type;
	string tech;

	std::map<RTLIL::IdString, unsigned int, RTLIL::sort_by_id_str> num_cells_by_type;
	std::map<RTLIL::IdString, double, RTLIL::sort_by_id_str> cells_area_by_type;
	std::set<RTLIL::IdString> unknown_cell_area;

	statdata_t operator+(const statdata_t &other) const
	{
		statdata_t sum = other;
#define X(_name) sum._name += _name;
		STAT_NUMERIC_MEMBERS
#undef X
		for (auto &it : num_cells_by_type)
			sum.num_cells_by_type[it.first] += it.second;
		return sum;
	}
	statdata_t operator*(unsigned int other) const
	{
		statdata_t sum = *this;
#define X(_name) sum._name *= other;
		STAT_NUMERIC_MEMBERS
#undef X
		for (auto &it : sum.num_cells_by_type)
			it.second *= other;
		return sum;
	}
	statdata_t add(const statdata_t &other)
	{
#define X(_name) _name += other._name;
		STAT_NUMERIC_MEMBERS
#undef X
		for (auto &it : other.num_cells_by_type) {
			if (num_cells_by_type.count(it.first))
				num_cells_by_type[it.first] += it.second;
			else
				num_cells_by_type[it.first] = it.second;
		}
		for (auto &it : other.instances_area_by_type) {
			if (instances_area_by_type.count(it.first))
				instances_area_by_type[it.first] += it.second;
			else
				instances_area_by_type[it.first] = it.second;
		}
		for (auto &it : other.cells_area_by_type) {
			if (cells_area_by_type.count(it.first))
				cells_area_by_type[it.first] += it.second;
			else
				cells_area_by_type[it.first] = it.second;
		}
		return *this;
	}

	statdata_t()
	{
#define X(_name) _name = 0;
		STAT_NUMERIC_MEMBERS
#undef X
	}

	statdata_t(cell_area_t &cell_data, string techname)
	{
		tech = techname;
		area = cell_data.area;
		if (cell_data.is_sequential) {
			sequential_area = cell_data.area;
		}
	}

	statdata_t(const RTLIL::Design *design, const RTLIL::Module *mod, bool width_mode, dict<IdString, cell_area_t> &cell_area, string techname)
	{
		tech = techname;

#define X(_name) _name = 0;
		STAT_NUMERIC_MEMBERS
#undef X
		// additional_cell_area

		for (auto wire : mod->selected_wires()) {
			if (wire->port_input || wire->port_output) {
				num_ports++;
				num_port_bits += wire->width;
			}

			if (wire->name.isPublic()) {
				num_pub_wires++;
				num_pub_wire_bits += wire->width;
			}

			num_wires++;
			num_wire_bits += wire->width;
		}

		for (auto &it : mod->memories) {
			if (!design->selected(mod, it.second))
				continue;
			num_memories++;
			num_memory_bits += it.second->width * it.second->size;
		}
		for (auto cell : mod->selected_cells()) {
			RTLIL::IdString cell_type = cell->type;
			if (width_mode) {
				if (cell_type.in(ID($not), ID($pos), ID($neg), ID($logic_not), ID($logic_and), ID($logic_or), ID($reduce_and),
						 ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool), ID($lut), ID($and), ID($or),
						 ID($xor), ID($xnor), ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx), ID($lt),
						 ID($le), ID($eq), ID($ne), ID($eqx), ID($nex), ID($ge), ID($gt), ID($add), ID($sub), ID($mul),
						 ID($div), ID($mod), ID($divfloor), ID($modfloor), ID($pow), ID($alu))) {
					int width_a = cell->hasPort(ID::A) ? GetSize(cell->getPort(ID::A)) : 0;
					int width_b = cell->hasPort(ID::B) ? GetSize(cell->getPort(ID::B)) : 0;
					int width_y = cell->hasPort(ID::Y) ? GetSize(cell->getPort(ID::Y)) : 0;
					cell_type = stringf("%s_%d", cell_type.c_str(), max<int>({width_a, width_b, width_y}));
				} else if (cell_type.in(ID($mux), ID($pmux)))
					cell_type = stringf("%s_%d", cell_type.c_str(), GetSize(cell->getPort(ID::Y)));
				else if (cell_type == ID($bmux))
					cell_type =
					  stringf("%s_%d_%d", cell_type.c_str(), GetSize(cell->getPort(ID::Y)), GetSize(cell->getPort(ID::S)));
				else if (cell_type == ID($demux))
					cell_type =
					  stringf("%s_%d_%d", cell_type.c_str(), GetSize(cell->getPort(ID::A)), GetSize(cell->getPort(ID::S)));
				else if (cell_type.in(ID($sr), ID($ff), ID($dff), ID($dffe), ID($dffsr), ID($dffsre), ID($adff), ID($adffe),
						      ID($sdff), ID($sdffe), ID($sdffce), ID($aldff), ID($aldffe), ID($dlatch), ID($adlatch),
						      ID($dlatchsr)))
					cell_type = stringf("%s_%d", cell_type.c_str(), GetSize(cell->getPort(ID::Q)));
			}

			if (!cell_area.empty()) {
				//check if cell_area provides a area calculator
				if (cell_area.count(cell->type)){
					cell_area_t cell_data = cell_area.at(cell->type);
					if (cell_data.single_parameter_area.size() > 0) {
						//assume that we just take the max of the A,B,Y ports
						
						int width_a = cell->hasPort(ID::A) ? GetSize(cell->getPort(ID::A)) : 0;
						int width_b = cell->hasPort(ID::B) ? GetSize(cell->getPort(ID::B)) : 0;
						int width_y = cell->hasPort(ID::Y) ? GetSize(cell->getPort(ID::Y)) : 0;
						int width_q = cell->hasPort(ID::Q) ? GetSize(cell->getPort(ID::Q)) : 0;
						int max_width = max<int>({width_a, width_b, width_y, width_q});
						if (!cell_area.count(cell_type)) {
							cell_area[cell_type]=cell_data;
						}
						if (cell_data.single_parameter_area.size() > max_width-1) {
							cell_area.at(cell_type).area = cell_data.single_parameter_area.at(max_width-1);
						} else {
							printf("too small single_parameter_area %s %d %f\n", cell_type.c_str(), max_width, cell_data.single_parameter_area.back());
							cell_area.at(cell_type).area = cell_data.single_parameter_area.back();
						}
						//printf("single_paramter_extraction %s %d %f\n", cell_type.c_str(), max_width, cell_area.at(cell_type).area);
						
					}
					vector<double> widths;
					if (cell_data.parameter_names.size() > 0) {
						for (auto &it : cell_data.parameter_names) {
							if (cell->hasPort(ID(it))) {
								int width = GetSize(cell->getPort(ID(it)));
								printf("width %s %s %d\n", cell_type.c_str(), it.c_str(), width);
								printf("port %s %d\n", cell->getPort(ID(it)).as_string().c_str(), width);
								widths.push_back(width);
							} else {
								widths.push_back(0);
							}
						}
						printf("widths %s %d %d\n", cell_type.c_str(), widths.size(), widths.at(0));
					}
					
					if (cell_data.double_parameter_area.size() > 0) {
						if (!cell_area.count(cell_type)) {
							cell_area[cell_type]=cell_data;
						}
						if (widths.size() == 2) {
							int width_a = widths.at(0);
							int width_b = widths.at(1);
							if (width_a > 0 && width_b > 0) {
								if (cell_data.double_parameter_area.size() > width_a - 1 && cell_data.double_parameter_area.at(width_a - 1).size() > width_b - 1) {
									cell_area.at(cell_type).area = cell_data.double_parameter_area.at(width_a - 1).at(width_b - 1);
								} else {
									printf("too small double_parameter_area %s %d %d %f\n", cell_type.c_str(), width_a, width_b, cell_data.double_parameter_area.back().back());
									cell_area.at(cell_type).area = cell_data.double_parameter_area.back().back();
								}
							} else {
								cell_area.at(cell_type).area = cell_data.area;
							}
						} else {
							printf("double_paramter_extraction %s %d %f\n", cell_type.c_str(), widths.size(), cell_area.at(cell_type).area);
						}
					}
				}



				if (cell_area.count(cell_type)) {
					cell_area_t cell_data = cell_area.at(cell_type);
					if (cell_data.is_sequential) {
						sequential_area += cell_data.area;
					}
					area += cell_data.area;
					num_cells++;
					num_cells_by_type[cell_type]++;
					cells_area_by_type[cell_type] += cell_data.area;
					local_cells_area_by_type[cell_type] += cell_data.area;
					local_area += cell_data.area;
					num_local_cells++;
					num_local_cells_by_type[cell_type]++;

				} else {
					unknown_cell_area.insert(cell_type);
				}
			} else {
				num_cells++;
				num_cells_by_type[cell_type]++;
				cells_area_by_type[cell_type] = 0;
				num_local_cells++;
				num_local_cells_by_type[cell_type]++;
				local_cells_area_by_type[cell_type] = 0;
			}
		}

		for (auto &it : mod->processes) {
			if (!design->selected(mod, it.second))
				continue;
			num_processes++;
		}
		RTLIL::IdString cell_name = mod->name;
		auto s = cell_name.str();

		if (unknown_cell_area.count(cell_name)) {
			printf("cell %s area: %f", cell_name.c_str(), cell_area.at(cell_name).area);
		}
	}

	unsigned int estimate_xilinx_lc()
	{
		unsigned int lut6_cnt = num_cells_by_type[ID(LUT6)];
		unsigned int lut5_cnt = num_cells_by_type[ID(LUT5)];
		unsigned int lut4_cnt = num_cells_by_type[ID(LUT4)];
		unsigned int lut3_cnt = num_cells_by_type[ID(LUT3)];
		unsigned int lut2_cnt = num_cells_by_type[ID(LUT2)];
		unsigned int lut1_cnt = num_cells_by_type[ID(LUT1)];
		unsigned int lc_cnt = 0;

		lc_cnt += lut6_cnt;

		lc_cnt += lut5_cnt;
		if (lut1_cnt) {
			int cnt = std::min(lut5_cnt, lut1_cnt);
			lut5_cnt -= cnt;
			lut1_cnt -= cnt;
		}

		lc_cnt += lut4_cnt;
		if (lut1_cnt) {
			int cnt = std::min(lut4_cnt, lut1_cnt);
			lut4_cnt -= cnt;
			lut1_cnt -= cnt;
		}
		if (lut2_cnt) {
			int cnt = std::min(lut4_cnt, lut2_cnt);
			lut4_cnt -= cnt;
			lut2_cnt -= cnt;
		}

		lc_cnt += lut3_cnt;
		if (lut1_cnt) {
			int cnt = std::min(lut3_cnt, lut1_cnt);
			lut3_cnt -= cnt;
			lut1_cnt -= cnt;
		}
		if (lut2_cnt) {
			int cnt = std::min(lut3_cnt, lut2_cnt);
			lut3_cnt -= cnt;
			lut2_cnt -= cnt;
		}
		if (lut3_cnt) {
			int cnt = (lut3_cnt + 1) / 2;
			lut3_cnt -= cnt;
		}

		lc_cnt += (lut2_cnt + lut1_cnt + 1) / 2;

		return lc_cnt;
	}

	unsigned int cmos_transistor_count(bool *tran_cnt_exact)
	{
		unsigned int tran_cnt = 0;
		auto &gate_costs = CellCosts::cmos_gate_cost();

		for (auto it : num_cells_by_type) {
			auto ctype = it.first;
			auto cnum = it.second;

			if (gate_costs.count(ctype))
				tran_cnt += cnum * gate_costs.at(ctype);
			else
				*tran_cnt_exact = false;
		}

		return tran_cnt;
	}

	void print_log_line(string name, unsigned int count_local, double area_local, unsigned int count_global, double area_global, int spacer = 0)
	{

		log(" %8.3G %8.3G %8.3G %8.3G %*s%-s \n", double(count_global), area_global, double(count_local), area_local, 2 * spacer, "", name.c_str());
	}

	void log_data(RTLIL::IdString mod_name, bool top_mod, bool global = false)
	{
		log(" %8s-%8s-%8s-%8s----%s\n", "+", "--------", "--------", "--------" , "Hierarchical number of cells, includes all the cells in instances aswell as directly in the module.");
		log(" %8s %8s-%8s-%8s----%s\n", "|", "+", "--------", "--------","Hierarchical  area, the area including all the instances in the module.");
		log(" %8s %8s %8s-%8s----%s\n", "|", "|", "+", "--------","Local number of cells, only the cells directly in the module.");
		log(" %8s %8s %8s %8s----%s\n", "|", "|", "|", "+","Local area, the area of the cells directly in the module. ");
		log(" %8s %8s %8s %8s \n", "|", "|", "|", "|");
		print_log_line("wires", 0, 0, num_wires, 0);
		print_log_line("wire bits", 0, 0, num_wire_bits, 0);
		print_log_line("public wires", 0, 0, num_pub_wires, 0);
		print_log_line("public wire bits", 0, 0, num_pub_wire_bits, 0);
		print_log_line("ports", 0, 0, num_ports, 0);
		print_log_line("port bits", 0, 0, num_port_bits, 0);
		print_log_line("memories", 0, 0, num_memories, 0);
		print_log_line("memory bits", 0, 0, num_memory_bits, 0);
		print_log_line("processes", 0, 0, num_processes, 0);
		print_log_line("cells", num_local_cells, local_area, num_cells, area);
		for (auto &it : num_cells_by_type)
			if (it.second) {
				auto name = string(log_id(it.first));
				print_log_line(name, num_local_cells_by_type.count(it.first) ? num_local_cells_by_type.at(it.first) : 0,
					       local_cells_area_by_type.count(it.first) ? local_cells_area_by_type.at(it.first) : 0, it.second,
					       cells_area_by_type.at(it.first), 1);
			}
		if (num_instances > 0) {
			print_log_line("instances", 0, 0, num_instances, instance_area);
			for (auto &it : num_instances_by_type)
				if (it.second)
					print_log_line(string(log_id(it.first)), 0, 0, it.second,
						       instances_area_by_type.count(it.first) ? instances_area_by_type.at(it.first) : 0, 1);
		}
		if (!unknown_cell_area.empty()) {
			log("\n");
			for (auto cell_type : unknown_cell_area)
				log("   Area for cell/instance type %s is unknown!\n", cell_type.c_str());
		}

		if (area != 0) {
			log("\n");
			log("   Chip area for %smodule '%s': %f\n", (top_mod) ? "top " : "", mod_name.c_str(), area);
			log("     of which used for sequential elements: %f (%.2f%%)\n", sequential_area, 100.0 * sequential_area / area);
		}

		if (tech == "xilinx") {
			log("\n");
			log("   Estimated number of LCs: %10u\n", estimate_xilinx_lc());
		}

		if (tech == "cmos") {
			bool tran_cnt_exact = true;
			unsigned int tran_cnt = cmos_transistor_count(&tran_cnt_exact);

			log("\n");
			log("   Estimated number of transistors: %10u%s\n", tran_cnt, tran_cnt_exact ? "" : "+");
		}
	}

	void log_data_json(const char *mod_name, bool first_module, bool global = false)
	{
		if (!first_module)
			log(",\n");
		log("      %s: {\n", json11::Json(mod_name).dump().c_str());
		log("         \"num_wires\":         %u,\n", num_wires);
		log("         \"num_wire_bits\":     %u,\n", num_wire_bits);
		log("         \"num_pub_wires\":     %u,\n", num_pub_wires);
		log("         \"num_pub_wire_bits\": %u,\n", num_pub_wire_bits);
		log("         \"num_ports\":         %u,\n", num_ports);
		log("         \"num_port_bits\":     %u,\n", num_port_bits);
		log("         \"num_memories\":      %u,\n", num_memories);
		log("         \"num_memory_bits\":   %u,\n", num_memory_bits);
		log("         \"num_processes\":     %u,\n", num_processes);
		log("         \"num_cells\":         %u,\n", global ? num_cells : num_local_cells);
		log("         \"num_instances\":       %u,\n", num_instances);
		if (area != 0) {
			log("         \"area\":              %f,\n", area);
			log("         \"sequential_area\":    %f,\n", sequential_area);
		}
		log("         \"num_cells_by_type\": {\n");
		bool first_line = true;
		for (auto &it : global ? num_cells_by_type : num_local_cells_by_type)
			if (it.second) {
				if (!first_line)
					log(",\n");
				log("            %s: %u", json11::Json(log_id(it.first)).dump().c_str(), it.second);
				first_line = false;
			}
		log(",\n");
		first_line = true;
		for (auto &it : num_instances_by_type)
			if (it.second) {
				if (!first_line)
					log(",\n");
				log("            %s: %u", json11::Json(log_id(it.first)).dump().c_str(), it.second);
				first_line = false;
			}
		log("\n");
		log("         }");
		if (tech == "xilinx") {
			log(",\n");
			log("         \"estimated_num_lc\": %u", estimate_xilinx_lc());
		}
		if (tech == "cmos") {
			bool tran_cnt_exact = true;
			unsigned int tran_cnt = cmos_transistor_count(&tran_cnt_exact);
			log(",\n");
			log("         \"estimated_num_transistors\": \"%u%s\"", tran_cnt, tran_cnt_exact ? "" : "+");
		}
		log("\n");
		log("      }");
	}
};

statdata_t hierarchy_worker(std::map<RTLIL::IdString, statdata_t> &mod_stat, RTLIL::IdString mod, int level, bool quiet = false)
{
	statdata_t mod_data = mod_stat.at(mod);

	for (auto &it : mod_data.num_instances_by_type) {
		if (mod_stat.count(it.first) > 0) {
			if (!quiet)
				mod_data.print_log_line(string(log_id(it.first)), mod_stat.at(it.first).num_local_cells,
							mod_stat.at(it.first).local_area, mod_stat.at(it.first).num_cells, mod_stat.at(it.first).area,
							level);
			hierarchy_worker(mod_stat, it.first, level + 1, quiet) * it.second;
		}
	}

	return mod_data;
}

statdata_t hierarchy_builder(const RTLIL::Design *design, const RTLIL::Module *top_mod, std::map<RTLIL::IdString, statdata_t> &mod_stat, bool width_mode,
			     dict<IdString, cell_area_t> &cell_area, string techname)
{
	if (top_mod == nullptr)
		top_mod = design->top_module();
	statdata_t mod_data(design, top_mod, width_mode, cell_area, techname);
	for (auto cell : top_mod->selected_cells()) {
		if (cell_area.count(cell->type) == 0) {
			if (design->has(cell->type)) {
				if (!(design->module(cell->type)->attributes.count(ID::blackbox))) {
					mod_data.add(hierarchy_builder(design, design->module(cell->type), mod_stat, width_mode, cell_area, techname));
					mod_data.num_instances_by_type[cell->type]++;
					mod_data.instances_area_by_type[cell->type] += mod_stat.at(cell->type).area;
					mod_data.instance_area += mod_stat.at(cell->type).area;
					mod_data.num_instances++;
					mod_data.unknown_cell_area.erase(cell->type);
					mod_data.num_cells -= mod_data.num_cells_by_type.erase(cell->type);
					mod_data.cells_area_by_type.erase(cell->type);
					mod_data.num_local_cells -= mod_data.num_local_cells_by_type.erase(cell->type);
					mod_data.local_cells_area_by_type.erase(cell->type);
				} else {
					// deal with blackbox cells
					mod_data.num_instances_by_type[cell->type]++;
					// some instances have their area as attribute
					if (design->module(cell->type)->attributes.count(ID::area)) {
						mod_data.instances_area_by_type[cell->type] +=
						  double(design->module(cell->type)->attributes.at(ID::area).as_int());
						mod_data.area += double(design->module(cell->type)->attributes.at(ID::area).as_int());
						mod_data.unknown_cell_area.erase(cell->type);
					}
					mod_data.num_instances++;
				}
			} else {
				// deal with unknown cells
			}
		}
	}
	mod_stat[top_mod->name] = mod_data;
	return mod_data;
}

void read_liberty_cellarea(dict<IdString, cell_area_t> &cell_area, string liberty_file)
{
	std::istream *f = uncompressed(liberty_file.c_str());
	yosys_input_files.insert(liberty_file);
	LibertyParser libparser(*f, liberty_file);
	delete f;

	for (auto cell : libparser.ast->children) {
		if (cell->id != "cell" || cell->args.size() != 1)
			continue;

		const LibertyAst *ar = cell->find("area");
		bool is_flip_flop = cell->find("ff") != nullptr;
		vector<double> single_parameter_area;
		vector<vector<double>> double_parameter_area;
		vector<string> port_names;
		const LibertyAst *sar = cell->find("single_area_parameterised");
		if (sar != nullptr ){
			for (const auto& s : sar->args) {
				double value = 0;
				auto [ptr, ec] = std::from_chars(s.data(), s.data() + s.size(), value);
				// ec != std::errc() means parse error, or ptr didn't consume entire string
				if (ec != std::errc() || ptr != s.data() + s.size())
					break;
				single_parameter_area.push_back(value);
			}
			if (single_parameter_area.size() == 0)
				printf("error: %s\n",sar->args[single_parameter_area.size()-1].c_str());
				//check if it is a double parameterised area
		}
		const LibertyAst *dar = cell->find("double_area_parameterised");
		if (dar != nullptr) {
			for (const auto& s : dar->args) {

				//printf("value: %s\n",sar->value.c_str());
				//printf("args1: %s\n",dar->args[0].c_str());

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
				for (const auto& s : sub_array) {
					double value = 0;
					auto [ptr, ec] = std::from_chars(s.data()+1, s.data() + s.size(), value);
					if (ec != std::errc() || ptr != s.data() + s.size())
						break;
					cast_sub_array.push_back(value);
				}
				double_parameter_area.push_back(cast_sub_array);
				if (cast_sub_array.size() == 0)
					printf("error: %s\n",s.c_str());
			}
		}
		const LibertyAst *par = cell->find("port_names");
		if (par != nullptr) {
			for (const auto& s : par->args) {
				port_names.push_back(s);
				printf("port_name: '%s'\n",s.c_str());
			}
		}

		if (ar != nullptr && !ar->value.empty()) {
			string prefix = cell->args[0].substr(0, 1) == "$" ? "" : "\\";
			cell_area[prefix + cell->args[0]] = {atof(ar->value.c_str()), is_flip_flop,single_parameter_area,double_parameter_area,port_names};
		}

	}
}

struct StatPass : public Pass {
	StatPass() : Pass("stat", "print some statistics") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    stat [options] [selection]\n");
		log("\n");
		log("Print some statistics (number of objects) on the selected portion of the\n");
		log("design.\n");
		log("\n");
		log("    -top <module>\n");
		log("        print design hierarchy with this module as top. if the design is fully\n");
		log("        selected and a module has the 'top' attribute set, this module is used\n");
		log("        default value for this option.\n");
		log("\n");
		log("    -liberty <liberty_file>\n");
		log("        use cell area information from the provided liberty file\n");
		log("\n");
		log("    -tech <technology>\n");
		log("        print area estimate for the specified technology. Currently supported\n");
		log("        values for <technology>: xilinx, cmos\n");
		log("\n");
		log("    -width\n");
		log("        annotate internal cell types with their word width.\n");
		log("        e.g. $add_8 for an 8 bit wide $add cell.\n");
		log("\n");
		log("    -json\n");
		log("        output the statistics in a machine-readable JSON format.\n");
		log("        this is output to the console; use \"tee\" to output to a file.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool width_mode = false, json_mode = false;
		RTLIL::Module *top_mod = nullptr;
		std::map<RTLIL::IdString, statdata_t> mod_stat;
		dict<IdString, cell_area_t> cell_area;
		string techname;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-width") {
				width_mode = true;
				continue;
			}
			if (args[argidx] == "-liberty" && argidx + 1 < args.size()) {
				string liberty_file = args[++argidx];
				rewrite_filename(liberty_file);
				read_liberty_cellarea(cell_area, liberty_file);
				continue;
			}
			if (args[argidx] == "-tech" && argidx + 1 < args.size()) {
				techname = args[++argidx];
				continue;
			}
			if (args[argidx] == "-top" && argidx + 1 < args.size()) {
				if (design->module(RTLIL::escape_id(args[argidx + 1])) == nullptr)
					log_cmd_error("Can't find module %s.\n", args[argidx + 1].c_str());
				top_mod = design->module(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			if (args[argidx] == "-json") {
				json_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!json_mode)
			log_header(design, "Printing statistics.\n");

		if (techname != "" && techname != "xilinx" && techname != "cmos" && !json_mode)
			log_cmd_error("Unsupported technology: '%s'\n", techname.c_str());

		if (json_mode) {
			log("{\n");
			log("   \"creator\": %s,\n", json11::Json(yosys_maybe_version()).dump().c_str());
			std::stringstream invocation;
			std::copy(args.begin(), args.end(), std::ostream_iterator<std::string>(invocation, " "));
			log("   \"invocation\": %s,\n", json11::Json(invocation.str()).dump().c_str());
			log("   \"modules\": {\n");
		}

		printf("building cell area\n");
		statdata_t top_stat = hierarchy_builder(design, top_mod, mod_stat, width_mode, cell_area, techname);
		
		printf("built hierarchy\n");
		bool first_module = true;
		for (auto mod : design->selected_modules()) {
			if (!top_mod && design->full_selection())
				if (mod->get_bool_attribute(ID::top))
					top_mod = mod;
			statdata_t data = mod_stat.at(mod->name);
			if (json_mode) {
				data.log_data_json(mod->name.c_str(), first_module);
				first_module = false;
			} else {
				log("\n");
				log("=== %s%s ===\n", log_id(mod->name), mod->is_selected_whole() ? "" : " (partially selected)");
				log("\n");
				data.log_data(mod->name, false);
			}
		}

		if (json_mode) {
			log("\n");
			log(top_mod == nullptr ? "   }\n" : "   },\n");
		}

		if (top_mod != nullptr) {
			if (!json_mode && GetSize(mod_stat) > 1) {
				log("\n");
				log("=== design hierarchy ===\n");
				log("\n");
				log(" %8s-%8s-%8s-%8s----%s\n", "+", "--------", "--------", "--------" , "Hierarchical number of cells, includes all the cells in instances aswell as directly in the module.");
				log(" %8s %8s-%8s-%8s----%s\n", "|", "+", "--------", "--------","Hierarchical  area, the area including all the instances in the module.");
				log(" %8s %8s %8s-%8s----%s\n", "|", "|", "+", "--------","Local number of cells, only the cells directly in the module.");
				log(" %8s %8s %8s %8s----%s\n", "|", "|", "|", "+","Local area, the area of the cells directly in the module. ");
				log(" %8s %8s %8s %8s \n", "|", "|", "|", "|");
				mod_stat[top_mod->name].print_log_line(log_id(top_mod->name), 0, 0, 0, mod_stat[top_mod->name].area);
			}

			statdata_t data = hierarchy_worker(mod_stat, top_mod->name, 0, /*quiet=*/json_mode);

			if (json_mode)
				data.log_data_json("design", true, true);
			else if (GetSize(mod_stat) > 1) {
				log("\n");
				data.log_data(top_mod->name, true, true);
			}

			design->scratchpad_set_int("stat.num_wires", data.num_wires);
			design->scratchpad_set_int("stat.num_wire_bits", data.num_wire_bits);
			design->scratchpad_set_int("stat.num_pub_wires", data.num_pub_wires);
			design->scratchpad_set_int("stat.num_pub_wire_bits", data.num_pub_wire_bits);
			design->scratchpad_set_int("stat.num_ports", data.num_ports);
			design->scratchpad_set_int("stat.num_port_bits", data.num_port_bits);
			design->scratchpad_set_int("stat.num_memories", data.num_memories);
			design->scratchpad_set_int("stat.num_memory_bits", data.num_memory_bits);
			design->scratchpad_set_int("stat.num_processes", data.num_processes);
			design->scratchpad_set_int("stat.num_cells", data.num_cells);
			design->scratchpad_set_int("stat.area", data.area);
		}

		if (json_mode) {
			log("\n");
			log("}\n");
		}

		log("\n");
	}
} StatPass;

PRIVATE_NAMESPACE_END
