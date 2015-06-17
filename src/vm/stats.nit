# Statistics of the VM (implementations, preexistance...)
module stats

import vm_optimizations

# Avoid to write same thing everytimes
private fun incr_specific_counters(cond: Bool, yes: String, no: String)
do
	if cond then
		pstats.inc(yes)
	else
		pstats.inc(no)
	end
end

# Avoid to write the same thing...
private fun incr_rst(rst_loaded: Bool, lbl: String)
do
	if not rst_loaded then pstats.inc("rst_unloaded_" + lbl)
end

redef class ToolContext
	# Enable print stats
	var stats_on = new OptionBool("Display statistics of model optimizing / preexistence after execution", "--mo-stats")

	# Enable print site state
	var print_site_state = new OptionBool("Display state of a MOSite (preexistence, impl)", "--site-state")

	redef init
	do
		super
		option_context.add_option(stats_on)
		option_context.add_option(print_site_state)
	end
end

redef class Sys
	# Preexist counters
	var pstats = new MOStats("first") is writable

	# Access to print_site_state from anywhere
	var print_site_state: Bool = false
end

redef class ModelBuilder
	redef fun run_virtual_machine(mainmodule, arguments)
	do
		sys.print_site_state = toolcontext.print_site_state.value
		
		super(mainmodule, arguments)
		
		if toolcontext.stats_on.value then 
			print(pstats.pretty)
			pstats.overview
			post_exec(mainmodule)
			pstats.overview
			# Meh...
		end
	end

	# At the end of execution, check if counters are rights, recompile all methods to get upper bound
	# of preexistence (see redef in vm_optimizations)
	fun post_exec(mainmodule: MModule)
	do
		# Recompile all active objet sites to get the upper bound of the preexistence
		# We don't need pstats counters with lower bound anymore, so we override it

		var old_counters = sys.pstats
		pstats = new MOStats("last")
		pstats.copy_data(old_counters)

		for site in pstats.analysed_sites do
			# WARN: this cast is always true for now, but we need to put preexist_analysed on MPropDef when we'll analysed attribute with body.
			site.lp.as(MMethodDef).preexist_analysed = false
			site.preexist_site
			site.impl = null
			site.get_impl(sys.vm)
			site.stats(sys.vm)
		end

		print(pstats.pretty)
	end
end

redef class VirtualMachine
	redef fun load_class(mclass)
	do
		if mclass.loaded then return

		super(mclass)

		pstats.inc("loaded_classes_explicits")
	end

	redef fun load_class_indirect(mclass)
	do
		if mclass.abstract_loaded then return

		super(mclass)

		if mclass.kind == abstract_kind and not mclass.mclass_type.is_primitive_type then
			pstats.inc("loaded_classes_abstracts")
		else
			pstats.inc("loaded_classes_implicits")
		end
	end
end

redef class ANewExpr
	redef fun generate_basic_blocks(ssa, old_block)
	do
		var sup = super
		pstats.inc("ast_new")
		return sup
	end
end

redef class ANode
	redef fun ast2mo
	do
		if is_primitive_node then
			pstats.inc("primitive_sites")
		else
			pstats.inc("nyi")
		end

		return super
	end
end

redef class AAttrPropdef
	# When the node encode accessors who are redefined, tell if it's already count as "attr_redef"
	var attr_redef_taken_into = false
end

redef class ASendExpr
	redef fun compile_ast(vm, lp)
	do
		super(vm, lp)
		if n_expr.mtype isa MNullType or n_expr.mtype == null then
			pstats.inc("lits")
		else if n_expr.mtype.as(not null).is_primitive_type then
			pstats.inc("primitive_sites")
		end
	end

	redef fun compile_ast_method(vm, lp, recv, node_ast, is_attribute)
	do
		super(vm, lp, recv, node_ast, is_attribute)

		# It's an accessors (with redefs) dispatch
		if is_attribute and not node_ast.as(AAttrPropdef).attr_redef_taken_into then 
			pstats.inc("attr_redef")
			node_ast.as(AAttrPropdef).attr_redef_taken_into = true
		end
	end
end

redef class AAsCastExpr
	redef fun compile_ast(vm, lp)
	do
		super(vm, lp)

		if n_expr.mtype isa MNullType or n_expr.mtype == null then
			pstats.inc("lits")
		else if n_expr.mtype.as(not null).is_primitive_type then
			pstats.inc("primitive_sites")
		else if n_type.mtype.as(not null).get_mclass(vm).as(not null).mclass_type.is_primitive_type then
			pstats.inc("primitive_sites")
		end
	end
end

redef class AAttrFormExpr
	redef fun compile_ast(vm, lp)
	do
		super(vm, lp)

		if n_expr.mtype isa MNullType or n_expr.mtype == null then
			pstats.inc("lits")
		else if n_expr.mtype.as(not null).is_primitive_type then
			pstats.inc("primitive_sites")
		end
	end
end

redef class AIsaExpr
	redef fun compile_ast(vm, lp)
	do
		super(vm, lp)
		
		if n_expr.mtype isa MNullType or n_expr.mtype == null then
			pstats.inc("lits")
		else if n_expr.mtype.as(not null).get_mclass(vm).as(not null).mclass_type.is_primitive_type then
			pstats.inc("primitive_sites")
		end
	end
end

redef class ABinopExpr
	# If a binary operation on primitives types return something (or test of equality), it's primitive
	# TODO: what about obj1 + obj2 ?
	redef fun ast2mo do
		pstats.inc("primitive_sites")
		return super
	end
end

# Stats of the optimizing model
class MOStats
	# List of analysed sites
	var analysed_sites = new List[MOSite]

	# Label to display on dump
	var lbl: String

	# Internal encoding of counters
	var map = new HashMap[String, Int]

	# Increment a counter
	fun inc(el: String) do map[el] += 1

	# Decrement a counter
	fun dec(el: String)
	do
		map[el] -= 1
		assert map[el] >= 0
	end
       
	# Get a value
	fun get(el: String): Int do return map[el]

	# Dump and format all values
	fun dump(prefix: String): String
	do
		var ret = ""

		for key, val in map do ret += "{prefix}{key}: {val}\n"

		return ret
	end

	# Make text csv file contains overview statistics
	fun overview
	do
		var buf: String
		var file = new FileWriter.open("mo-stats-{lbl}.csv")	

		file.write(", method, attribute, cast, total, rst null\n")
	
		var self_meth = map["method_self"]
		var self_attr = map["attribute_self"]
		var self_cast = map["cast_self"]
		var self_sum = self_meth + self_attr + self_cast

		file.write("self, {self_meth}, {self_attr}, {self_cast}, {self_sum}, \n")

		file.write("preexist, {map["method_preexist"]}, {map["attribute_preexist"]}, {map["cast_preexist"]}, {map["preexist"]}, \n")
		file.write("npreexist, {map["method_npreexist"]}, {map["attribute_npreexist"]}, {map["cast_npreexist"]}, {map["npreexist"]}, \n")

		buf = "{map["method_concretes"]},"
		buf += "{map["attribute_concretes"]},"
		buf += "{map["cast_concretes"]},"
		buf += "{map["concretes"]}"
		file.write("concretes,{buf},\n")

		buf = "{map["method_concretes_preexist"]},"
		buf += "{map["attribute_concretes_preexist"]},"
		buf += "{map["cast_concretes_preexist"]},"
		buf += "{map["concretes_preexist"]}"
		file.write("concretes preexist,{buf},\n")

		buf = "{map["method_concretes_npreexist"]},"
		buf += "{map["attribute_concretes_npreexist"]},"
		buf += "{map["cast_concretes_npreexist"]},"
		buf += "{map["concretes_npreexist"]}"
		file.write("concretes npreexist,{buf},\n")

		file.write("static, {map["method_static"]}, {map["attribute_static"]}, {map["cast_static"]}, {map["static"]}, {map["rst_unloaded_static"]}\n")

		buf = "{map["method_preexist_static"]},"
		buf += "{map["attribute_preexist_static"]},"
		buf += "{map["cast_preexist_static"]},"
		buf += "{map["static_preexist"]},"
		buf += "{map["rst_unloaded_static_pre"]}"
		file.write("static preexist, {buf}\n")

		buf = "{map["method_npreexist_static"]},"
		buf += "{map["attribute_npreexist_static"]},"
		buf += "{map["cast_npreexist_static"]},"
		buf += "{map["static_npreexist"]},"
		buf += "{map["rst_unloaded_static_npre"]}"
		file.write("static npreexist, {buf}\n")

		file.write("sst, {map["method_sst"]}, {map["attribute_sst"]}, {map["cast_sst"]}, {map["sst"]}, {map["rst_unloaded_sst"]}\n")

		buf = "{map["method_preexist_sst"]},"
		buf += "{map["attribute_preexist_sst"]},"
		buf += "{map["cast_preexist_sst"]},"
		buf += "{map["sst_preexist"]},"
		buf += "{map["rst_unloaded_sst_pre"]}"
		file.write("sst preexist, {buf}\n")

		buf = "{map["method_npreexist_sst"]},"
		buf += "{map["attribute_npreexist_sst"]},"
		buf += "{map["cast_npreexist_sst"]},"
		buf += "{map["sst_npreexist"]},"
		buf += "{map["rst_unloaded_sst_npre"]}"
		file.write("sst npreexist, {buf}\n")

		file.write("ph, {map["method_ph"]}, {map["attribute_ph"]}, {map["cast_ph"]}, {map["ph"]}, {map["rst_unloaded_ph"]}\n")

		buf = "{map["method_preexist_ph"]},"
		buf += "{map["attribute_preexist_ph"]},"
		buf += "{map["cast_preexist_ph"]},"
		buf += "{map["ph_preexist"]},"
		buf += "{map["rst_unloaded_ph_pre"]}"
		file.write("ph preexist, {buf}\n")

		buf = "{map["method_npreexist_ph"]},"
		buf += "{map["attribute_npreexist_ph"]},"
		buf += "{map["cast_npreexist_ph"]},"
		buf += "{map["ph_npreexist"]},"
		buf += "{map["rst_unloaded_ph_npre"]}"
		file.write("ph npreexist, {buf}\n")

		file.write("null, {map["method_null"]}, {map["attribute_null"]}, {map["cast_null"]}, {map["null"]}, {map["rst_unloaded_null"]}\n")

		buf = "{map["method_preexist_null"]},"
		buf += "{map["attribute_preexist_null"]},"
		buf += "{map["cast_preexist_null"]},"
		buf += "{map["null_preexist"]},"
		buf += "{map["rst_unloaded_null_pre"]}"
		file.write("null preexist, {buf}\n")

		buf = "{map["method_npreexist_null"]},"
		buf += "{map["attribute_npreexist_null"]},"
		buf += "{map["cast_npreexist_null"]},"
		buf += "{map["null_npreexist"]},"
		buf += "{map["rst_unloaded_null_npre"]}"
		file.write("null npreexist, {buf}\n")

		file.write("\n\n")

		var optimizable_inline = map["method_preexist_static"] + map["attribute_preexist_sst"] + map["cast_preexist_static"] + map["cast_preexist_sst"]
		file.write("optimisable inline,{optimizable_inline}\n")

		var no_optimizable = map["method_npreexist_static"] + map["attribute_npreexist_sst"] + map["cast_npreexist_sst"] + map["cast_npreexist_static"]
		file.write("non optimisable inline,{no_optimizable}\n")

		var no_inline = map["method_ph"] + map["method_sst"] + map["attribute_ph"] + map["cast_ph"]
		file.write("non inline,{no_inline}\n")

		file.write("\n\n")

		# from new
		
		file.write("from new,{map["method_sites_from_new"]}, {map["attribute_sites_from_new"]},{map["cast_sites_from_new"]},{map["sites_from_new"]}\n")
		
		# from method return
		
		buf = "{map["method_sites_from_meth_return"]},"
		buf += "{map["attribute_sites_from_meth_return"]},"
		buf += "{map["cast_sites_from_meth_return"]},"
		buf += "{map["sites_from_meth_return"]}"
		file.write("from return,{buf}\n")

		buf = "{map["method_sites_from_meth_return_cuc_null"]},"
		buf += "{map["attribute_sites_from_meth_return_cuc_null"]},"
		buf += "{map["cast_sites_from_meth_return_cuc_null"]},"
		buf += "{map["sites_from_meth_return_cuc_null"]}"
		file.write("from return cuc null,{buf}\n")

		buf = "{map["method_sites_from_meth_return_cuc_pos"]},"
		buf += "{map["attribute_sites_from_meth_return_cuc_pos"]},"
		buf += "{map["cast_sites_from_meth_return_cuc_pos"]},"
		buf += "{map["sites_from_meth_return_cuc_pos"]}"
		file.write("from return cuc pos,{buf}\n")

		# from read site

		buf = "{map["method_sites_from_read"]},"
		buf += "{map["attribute_sites_from_read"]},"
		buf += "{map["cast_sites_from_read"]},"
		buf += "{map["sites_from_read"]}"
		file.write("from readsite,{buf}\n")

		# cuc

		file.write("\n")

		var living_propdefs = new HashSet[MMethodDef]
		for site in analysed_sites do
			if site isa MOCallSite then
				for lp in site.pattern.gp.living_mpropdefs do
					# The hashset make duplicates if the site is already in (!!!??!!)
					if not living_propdefs.has(site.lp) then
						living_propdefs.add(lp)
					end
				end
			end
		end

		var cuc_pos = 0
		var cuc_null = 0

		for propdef in living_propdefs do
			if propdef.callers.length > 0 then
				if propdef.callers.first.cuc == 0 then
					cuc_null += 1
				else 
					cuc_pos += 1
				end
			end
		end

		file.write("callers cuc pos, {cuc_pos}\n")
		file.write("callers cuc null, {cuc_null}\n")

		file.close
	end

	# Pretty format
	fun pretty: String
	do
		var ret = "" 

		ret += "\n------------------ MO STATS {lbl} ------------------\n"
		ret += dump("\t")
		ret += "--------------------------------------------------------\n"

		return ret
	end

	# Copy counters who not depends of the world state
	fun copy_data(counters: MOStats)
	do
		map["loaded_classes_explicits"] = counters.get("loaded_classes_explicits")
		map["loaded_classes_implicits"] = counters.get("loaded_classes_implicits")
		map["loaded_classes_abstracts"] = counters.get("loaded_classes_abstracts")
		map["primitive_sites"] = counters.get("primitive_sites")
		map["nyi"] = counters.get("nyi")
		map["lits"] = counters.get("lits")
		map["ast_new"] = counters.get("ast_new")
		map["attr_redef"] = counters.get("attr_redef")
		map["sites_final"] = counters.get("sites_final")
		analysed_sites.add_all(counters.analysed_sites)
	end

	init
	do
		# inrc when a class is explicitly (with a "new" keyword) loaded
		map["loaded_classes_explicits"] = 0

		# inrc when a class is loaded as super-class (abstract excluded) of a loaded class (implicit or explicit)
		map["loaded_classes_implicits"] = 0

		# incr when a class is abstract and loaded as super-class
		map["loaded_classes_abstracts"] = 0

		# incr when compile a instantiation site
		map["ast_new"] = 0
			
		# incr when the site depends at least of one return expression
		map["sites_from_meth_return"] = 0
		map["sites_from_meth_return_cuc_pos"] = 0
		map["sites_from_meth_return_cuc_null"] = 0
		map["method_sites_from_meth_return"] = 0
		map["method_sites_from_meth_return_cuc_pos"] = 0
		map["method_sites_from_meth_return_cuc_null"] = 0
		map["attribute_sites_from_meth_return"] = 0
		map["attribute_sites_from_meth_return_cuc_pos"] = 0
		map["attribute_sites_from_meth_return_cuc_null"] = 0
		map["cast_sites_from_meth_return"] = 0
		map["cast_sites_from_meth_return_cuc_pos"] = 0
		map["cast_sites_from_meth_return_cuc_null"] = 0

		# incr when the site depends at least of one new expression
		map["sites_from_new"] = 0
		map["method_sites_from_new"] = 0
		map["attribute_sites_from_new"] = 0
		map["cast_sites_from_new"] = 0

		# incr when the site depends at least of one attr read expression
		map["sites_from_read"] = 0
		map["method_sites_from_read"] = 0
		map["attribute_sites_from_read"] = 0
		map["cast_sites_from_read"] = 0

		# incr when the site depends of at least of one return expression or one new expression
		map["sites_handle_by_extend_preexist"] = 0

		# incr when the site is on leaf gp on global model
		map["sites_final"] = 0
		
		# incr when site is on integer, char, string (not added into the MO)
		map["primitive_sites"] = 0

		# incr when the ast site is an unkown case (not added into the MO)
		map["nyi"] = 0

		# never use. Maybe usefull for enum if Nit add it (this cass should not be added into the MO)
		map["lits"] = 0

		# incr if a site is preexist
		map["preexist"] = 0

		# incr if a site isn't preexist
		map["npreexist"] = 0

		map["static"] = 0
		map["static_preexist"] = 0
		map["static_npreexist"] = 0
		map["sst"] = 0
		map["sst_preexist"] = 0
		map["sst_npreexist"] = 0
		map["ph"] = 0
		map["ph_preexist"] = 0
		map["ph_npreexist"] = 0
		map["null"] = 0
		map["null_preexist"] = 0
		map["null_npreexist"] = 0

		# incr if construct MO node to access on attribute as MOCallSite
		# because it's an accessors with redefinitions
		# If it's incr, some meth_* counters will be incr too, as regular method call
		map["attr_redef"] = 0

		map["concretes"] = 0
		map["concretes_preexist"] = 0
		map["concretes_npreexist"] = 0

		# access to self receiver
		map["self"] = 0

		map["rst_unloaded_static"] = 0
		map["rst_unloaded_static_pre"] = 0
		map["rst_unloaded_static_npre"] = 0
		map["rst_unloaded_sst"] = 0
		map["rst_unloaded_sst_pre"] = 0
		map["rst_unloaded_sst_npre"] = 0
		map["rst_unloaded_ph"] = 0
		map["rst_unloaded_ph_pre"] = 0
		map["rst_unloaded_ph_npre"] = 0
		map["rst_unloaded_null"] = 0
		map["rst_unloaded_null_pre"] = 0
		map["rst_unloaded_null_npre"] = 0

		map["method"] = 0
		map["method_preexist"] = 0
		map["method_npreexist"] = 0
		map["method_self"] = 0
		map["method_concretes"] = 0
		map["method_concretes_preexist"] = 0
		map["method_concretes_npreexist"] = 0
		map["method_static"] = 0
		map["method_preexist_static"] = 0
		map["method_npreexist_static"] = 0
		map["method_sst"] = 0
		map["method_preexist_sst"] = 0
		map["method_npreexist_sst"] = 0
		map["method_ph"] = 0
		map["method_preexist_ph"] = 0
		map["method_npreexist_ph"] = 0
		map["method_null"] = 0
		map["method_preexist_null"] = 0
		map["method_npreexist_null"] = 0

		map["attribute"] = 0
		map["attribute_preexist"] = 0
		map["attribute_npreexist"] = 0
		map["attribute_self"] = 0
		map["attribute_concretes"] = 0
		map["attribute_concretes_preexist"] = 0
		map["attribute_concretes_npreexist"] = 0
		map["attribute_static"] = 0
		map["attribute_preexist_static"] = 0
		map["attribute_npreexist_static"] = 0
		map["attribute_sst"] = 0
		map["attribute_preexist_sst"] = 0
		map["attribute_npreexist_sst"] = 0
		map["attribute_ph"] = 0
		map["attribute_preexist_ph"] = 0
		map["attribute_npreexist_ph"] = 0
		map["attribute_null"] = 0
		map["attribute_preexist_null"] = 0
		map["attribute_npreexist_null"] = 0

		map["cast"] = 0
		map["cast_preexist"] = 0
		map["cast_npreexist"] = 0
		map["cast_self"] = 0
		map["cast_concretes"] = 0
		map["cast_concretes_preexist"] = 0
		map["cast_concretes_npreexist"] = 0
		map["cast_static"] = 0
		map["cast_preexist_static"] = 0
		map["cast_npreexist_static"] = 0
		map["cast_sst"] = 0
		map["cast_preexist_sst"] = 0
		map["cast_npreexist_sst"] = 0
		map["cast_ph"] = 0
		map["cast_preexist_ph"] = 0
		map["cast_npreexist_ph"] = 0
		map["cast_null"] = 0
		map["cast_preexist_null"] = 0
		map["cast_npreexist_null"] = 0

		map["call_with_cuc_pos"] = 0
		map["call_with_cuc_null"] = 0
	end
end

redef class MOSite
	# Type of the site (method, attribute or cast)
	var site_type: String is noinit

	# Count the implementation of the site
	fun stats(vm: VirtualMachine)
	do
		incr_preexist(vm)
		incr_from_site
		incr_concrete_site(vm)
		incr_self
		incr_rst_unloaded(vm)
		incr_type_impl(vm)

		if print_site_state then
			var buf = "site {self}\n"
			buf += "\tpattern: {pattern2str}\n"
			buf += "\tlp: {lp.mclassdef.name}::{lp.name}\n"
			buf += "\tlocation: {ast.location}\n"
			buf += "\tpreexist/mutable: {expr_recv.is_pre}/{expr_recv.is_nper}\n"
			buf += "\timpl: {get_impl(vm)}\n"
			print(buf)
		end
	end

	# Print the pattern (RST/GP or target class for subtype test)
	fun pattern2str: String is abstract

	#
	fun incr_preexist(vm: VirtualMachine) do 
		var pre = expr_recv.is_pre

		incr_specific_counters(pre, "preexist", "npreexist")
		incr_specific_counters(pre, "{site_type}_preexist", "{site_type}_npreexist")
	end

	#
	fun incr_type_impl(vm: VirtualMachine)
	do
		var impl = get_impl(vm)
		var pre = expr_recv.is_pre

		pstats.inc(site_type)

		if impl isa StaticImpl then
			pstats.inc("{site_type}_static")
			pstats.inc("static")
			incr_specific_counters(pre, "static_preexist", "static_npreexist")
			incr_specific_counters(pre, "{site_type}_preexist_static", "{site_type}_npreexist_static")
		else if impl isa SSTImpl then
			pstats.inc("{site_type}_sst")
			pstats.inc("sst")
			incr_specific_counters(pre, "sst_preexist", "sst_npreexist")
			incr_specific_counters(pre, "{site_type}_preexist_sst", "{site_type}_npreexist_sst")
		else if impl isa PHImpl then
			pstats.inc("{site_type}_ph")
			pstats.inc("ph")
			incr_specific_counters(pre, "ph_preexist", "ph_npreexist")
			incr_specific_counters(pre, "{site_type}_preexist_ph", "{site_type}_npreexist_ph")
		else if impl isa NullImpl then
			pstats.inc("{site_type}_null")
			pstats.inc("null")
			incr_specific_counters(pre, "null_preexist", "null_npreexist")
			incr_specific_counters(pre, "{site_type}_preexist_null", "{site_type}_npreexist_null")
		else
			abort
		end
	end

	# WARN : this partition is not exclusive
	fun incr_from_site
	do
		var dep_trace = new DependencyTrace(expr_recv)

		dep_trace.trace

		if dep_trace.from_new then
			pstats.inc("sites_from_new")
			pstats.inc("{site_type}_sites_from_new")
		end

		if dep_trace.from_return then
			pstats.inc("sites_from_meth_return")
			pstats.inc("{site_type}_sites_from_meth_return")
			incr_specific_counters(dep_trace.cuc_null, "{site_type}_sites_from_meth_return_cuc_null", "{site_type}_sites_from_meth_return_cuc_pos")
			incr_specific_counters(dep_trace.cuc_null, "sites_from_meth_return_cuc_null", "sites_from_meth_return_cuc_pos")
		end

		if dep_trace.from_read then
			pstats.inc("sites_from_read")
			pstats.inc("{site_type}_sites_from_read")
		end
	end

	#
	fun incr_concrete_site(vm: VirtualMachine)
	do
		if get_concretes.length > 0 then
			var pre = expr_recv.is_pre

			pstats.inc("concretes")
			pstats.inc("{site_type}_concretes")
			incr_specific_counters(pre, "concretes_preexist", "concretes_npreexist")
			incr_specific_counters(pre, "{site_type}_concretes_preexist", "{site_type}_concretes_npreexist")
		end
	end

	#
	fun incr_self
	do
		if expr_recv isa MOParam and expr_recv.as(MOParam).offset == 0 then 
			pstats.inc("self")
			pstats.inc("{site_type}_self")
		end
	end

	#
	fun incr_rst_unloaded(vm: VirtualMachine)
	do
		var rst_loaded = pattern.rst.get_mclass(vm).as(not null).abstract_loaded

		if not rst_loaded then
			var impl = get_impl(vm)
			var pre = expr_recv.is_pre

			if impl isa StaticImpl then
				pstats.inc("rst_unloaded_static")
				incr_specific_counters(pre, "rst_unloaded_static_pre", "rst_unloaded_static_npre")
			else if impl isa SSTImpl then
				pstats.inc("rst_unloaded_sst")
				incr_specific_counters(pre, "rst_unloaded_sst_pre", "rst_unloaded_sst_npre")
			else if impl isa PHImpl then
				pstats.inc("rst_unloaded_ph")
				incr_specific_counters(pre, "rst_unloaded_ph_pre", "rst_unloaded_ph_npre")
			else if impl isa NullImpl then
				pstats.inc("rst_unloaded_null")
				incr_specific_counters(pre, "rst_unloaded_null_pre", "rst_unloaded_null_npre")
			else 
				abort
			end
		end
	end
end

redef class MOPropSite
	redef fun pattern2str do return "{pattern.rst}::{pattern.gp}"
end

redef class MOCallSite
	redef var site_type = "method"
end

redef class MOAttrSite
	redef var site_type = "attribute"
end

redef class MOSubtypeSite
	redef fun pattern2str do return "{pattern.rst}->{pattern.target}"

	redef var site_type = "cast"
end

redef class MPropDef
	redef fun compile(vm)
	do
		super

		if self isa MMethodDef then
			for site in self.mosites do
				site.stats(vm)
				pstats.analysed_sites.add(site)
			end
		end
	end
end

# Tell where the expression of a site comes from
class DependencyTrace
	# from a new expression
	var from_new = false

	# from a return method expression
	var from_return = false

	# from a read attribute expression
	var from_read = false

	# cuc is null ? usefull only when it comes from a method
	var cuc_null = true

	# the expression to trace
	var expr: MOExpr

	# trace the dependencies (entry point) 
	fun trace do trace_internal(expr)

	# trace the dependencies (internal function)
	fun trace_internal(expr: MOExpr)
	do
		if expr isa MONew then
			from_new = true
		else if expr isa MOCallSite then
			from_return = true
			if expr.pattern.cuc > 0 then cuc_null = false
		else if expr isa MOReadSite then
			from_read = true
		else if expr isa MOSSAVar then
			trace_internal(expr.dependency)
		else if expr isa MOPhiVar then
			for dep in expr.dependencies do trace_internal(dep)
		end
	end
end
