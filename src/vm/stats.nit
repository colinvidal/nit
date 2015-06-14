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

	redef init
	do
		super
		option_context.add_option(stats_on)
	end
end

redef class Sys
	# Preexist counters
	var pstats = new MOStats("first") is writable
end

redef class ModelBuilder
	redef fun run_virtual_machine(mainmodule, arguments)
	do
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
		pstats.copy_static_data(old_counters)

		for site in pstats.analysed_sites do
			site.preexist_site
			site.impl = null
			site.get_impl(interpreter)
			site.stats(interpreter)
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
		var file = new FileWriter.open("mo-stats-{lbl}.csv")	

		file.write(", method, attribute, cast, total, rst null\n")
	
		var self_meth = map["meth_self"]
		var self_attr = map["attr_self"]
		var self_cast = map["cast_self"]
		var self_sum = self_meth + self_attr + self_cast
		file.write("self, {self_meth}, {self_attr}, {self_cast}, {self_sum}, {map["rst_unloaded_self"]}\n")

		var rst_null_pre_sum = map["rst_unloaded_static_pre"] + map["rst_unloaded_sst_pre"]
		var rst_null_npre_sum = map["rst_unloaded_ph"] + map["rst_unloaded_static_npre"] + map["rst_unloaded_sst_npre"]
		file.write("preexist, {map["meth_preexist"]}, {map["attr_preexist"]}, {map["cast_preexist"]}, {map["preexist"]}, {rst_null_pre_sum}\n")
		file.write("npreexist, {map["meth_npreexist"]}, {map["attr_npreexist"]}, {map["cast_npreexist"]}, {map["npreexist"]}, {rst_null_npre_sum}\n")

		var concretes_meth = map["meth_concretes_receivers"]
		var concretes_attr = map["attr_concretes_receivers"]
		var concretes_cast = map["cast_concretes_receivers"]
		var concretes_sum = concretes_meth + concretes_attr + concretes_cast
		var concretes_rst_null_sum = map["rst_unloaded_concretes_pre"] + map["rst_unloaded_concretes_npre"]
		file.write("concretes, {concretes_meth}, {concretes_attr}, {concretes_cast}, {concretes_sum}, {concretes_rst_null_sum}\n")

		var concretes_pre_meth = map["meth_concretes_preexist"]
		var concretes_pre_attr = map["attr_concretes_preexist"]
		var concretes_pre_cast = map["cast_concretes_preexist"]
		var concretes_pre_total = concretes_pre_meth + concretes_pre_attr + concretes_pre_cast
		file.write("preexist concretes, {concretes_pre_meth}, {concretes_pre_attr}, {concretes_pre_cast}, {concretes_pre_total}, {map["rst_unloaded_concretes_pre"]}\n")

		var concretes_npre_meth = map["meth_concretes_npreexist"]
		var concretes_npre_attr = map["attr_concretes_npreexist"]
		var concretes_npre_cast = map["cast_concretes_npreexist"]
		var concretes_npre_total = concretes_npre_meth + concretes_npre_attr + concretes_npre_cast
		file.write("npreexist concretes, {concretes_npre_meth}, {concretes_npre_attr}, {concretes_npre_cast}, {concretes_npre_total}, {map["rst_unloaded_concretes_npre"]}\n")

		var meth_static = map["meth_preexist_static"] + map["meth_npreexist_static"]
		var cast_static = map["cast_preexist_static"] + map["cast_npreexist_static"]
		var rst_null_static = map["rst_unloaded_static_pre"] + map["rst_unloaded_static_npre"]
		file.write("static, {meth_static}, 0, {cast_static}, {map["impl_static"]},{rst_null_static}\n")

		file.write("static preexist, {map["meth_preexist_static"]}, 0, {map["cast_preexist_static"]}, {map["preexist_static"]}, {map["rst_unloaded_static_pre"]}\n")

		var sum_npre_static = map["meth_npreexist_static"] + map["cast_npreexist_static"]
		file.write("static npreexist, {map["meth_npreexist_static"]}, 0, {map["cast_npreexist_static"]}, {sum_npre_static}, {map["rst_unloaded_static_npre"]}\n")

		var meth_sst = map["meth_preexist_sst"] + map["meth_npreexist_sst"]
		var attr_sst = map["attr_preexist_sst"] + map["attr_npreexist_sst"]
		var cast_sst = map["cast_preexist_sst"] + map["cast_npreexist_sst"]
		var rst_null_sst = map["rst_unloaded_sst_pre"] + map["rst_unloaded_sst_npre"]
		file.write("sst, {meth_sst}, {attr_sst}, {cast_sst}, {map["impl_sst"]}, {rst_null_sst}\n")
	
		var sum_pre_sst = map["meth_preexist_sst"] + map["attr_preexist_sst"] + map["cast_preexist_sst"]
		file.write("sst preexist, {map["meth_preexist_sst"]}, {map["attr_preexist_sst"]}, {map["cast_preexist_sst"]}, {sum_pre_sst}, {map["rst_unloaded_sst_pre"]}\n")

		var sum_npre_sst = map["meth_npreexist_sst"] + map["attr_npreexist_sst"] + map["cast_npreexist_sst"]
		file.write("sst npreexist, {map["meth_npreexist_sst"]}, {map["attr_npreexist_sst"]}, {map["cast_npreexist_sst"]}, {sum_npre_sst}, {map["rst_unloaded_sst_npre"]}\n")

		file.write("ph, {map["meth_ph"]}, {map["attr_ph"]}, {map["cast_ph"]}, {map["impl_ph"]}, {map["rst_unloaded_ph"]}\n")

		var optimization_inline = map["preexist_static"] + map["attr_preexist_sst"] + map["cast_preexist_sst"] + map["cast_preexist_static"]
		file.write(",,,,,,,\n")
	
		var sum_pic_null_method = map["pic_unloaded_method_pre"] + map["pic_unloaded_method_npre"]
		var sum_pic_null_attribute = map["pic_unloaded_attribute_pre"] + map["pic_unloaded_attribute_npre"]
		var sum_pic_null_cast = map["pic_unloaded_cast_pre"] + map["pic_unloaded_cast_npre"]

		file.write("pic null, {sum_pic_null_method}, {sum_pic_null_attribute}, {sum_pic_null_cast}\n")
		file.write("pic null pre,{map["pic_unloaded_method_pre"]},{map["pic_unloaded_attribute_pre"]},{map["pic_unloaded_cast_pre"]}\n")
		file.write("pic null npre,{map["pic_unloaded_method_npre"]},{map["pic_unloaded_attribute_npre"]},{map["pic_unloaded_cast_npre"]}\n")


		file.write(",,,,,,,\n")
		file.write("optimisable inline,,,,{optimization_inline},{map["rst_unloaded_optimizable_inline"]}\n")

		var cant_optimize = map["meth_npreexist_static"] + map["attr_npreexist_sst"] + map["cast_npreexist_sst"] + map["cast_npreexist_static"]
		file.write("non optimisable inline,,,,{cant_optimize},{map["rst_unloaded_non_optimizable_inline"]}\n")

		var not_inline_subject = map["impl_ph"] + meth_sst
		file.write("non inline,,,,{not_inline_subject},{map["rst_unloaded_other"]}\n")

		file.write(",,,,,,,\n")
		file.write("from new,{map["sites_from_new"]}\n")
		file.write("from return,{map["sites_from_meth_return"]}\n")

		
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

	# Copy all values that are counted statically (eg. when we do ast -> mo)
	fun copy_static_data(counters: MOStats)
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
		
		# incr when compute an implementation
		map["impl_static"] = 0
		map["impl_sst"] = 0
		map["impl_ph"] = 0
	
		# incr when the site depends at least of one return expression
		map["sites_from_meth_return"] = 0

		# incr when the site depends at least of one new expression
		map["sites_from_new"] = 0
		
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

		# incr if a site is preexist and it implementation is static
		map["preexist_static"] = 0

		# incr if a pic is unloaded
		# the value of this must be <= of rst_unloaded
		map["pic_unloaded_method_pre"] = 0
		map["pic_unloaded_method_npre"] = 0
		map["pic_unloaded_attribute_pre"] = 0
		map["pic_unloaded_attribute_npre"] = 0
		map["pic_unloaded_cast_pre"] = 0
		map["pic_unloaded_cast_npre"] = 0

		# incr if a rst is unloaded
		map["rst_unloaded_self"] = 0
		map["rst_unloaded_static_pre"] = 0
		map["rst_unloaded_static_npre"] = 0
		map["rst_unloaded_sst_pre"] = 0
		map["rst_unloaded_sst_npre"] = 0
		map["rst_unloaded_ph"] = 0
		map["rst_unloaded_concretes_pre"] = 0
		map["rst_unloaded_concretes_npre"] = 0
		map["rst_unloaded_optimizable_inline"] = 0
		map["rst_unloaded_non_optimizable_inline"] = 0
		map["rst_unloaded_other"] = 0

		map["attr"] = 0
		map["attr_self"] = 0
		map["attr_concretes_receivers"] = 0
		map["attr_concretes_preexist"] = 0
		map["attr_concretes_npreexist"] = 0
		map["attr_read"] = 0
		map["attr_write"] = 0
		map["attr_preexist"] = 0
		map["attr_npreexist"] = 0
		map["attr_preexist_sst"] = 0
		map["attr_npreexist_sst"] = 0
		map["attr_ph"] = 0 
		# incr if construct MO node to access on attribute as MOCallSite
		# because it's an accessors with redefinitions
		# If it's incr, some meth_* counters will be incr too, as regular method call
		map["attr_redef"] = 0

		map["cast"] = 0
		map["cast_self"] = 0
		map["cast_concretes_receivers"] = 0
		map["cast_concretes_preexist"] = 0
		map["cast_concretes_npreexist"] = 0
		map["cast_preexist"] = 0
		map["cast_npreexist"] = 0
		map["cast_preexist_static"] = 0
		map["cast_npreexist_static"] = 0
		map["cast_preexist_sst"] = 0
		map["cast_npreexist_sst"] = 0
		map["cast_ph"] = 0

		map["meth"] = 0
		map["meth_self"] = 0
		map["meth_concretes_receivers"] = 0
		map["meth_concretes_preexist"] = 0
		map["meth_concretes_npreexist"] = 0
		map["meth_preexist"] = 0
		map["meth_npreexist"] = 0
		map["meth_preexist_static"] = 0
		map["meth_npreexist_static"] = 0
		map["meth_preexist_sst"] = 0
		map["meth_npreexist_sst"] = 0
		map["meth_ph"] = 0
	end
end


redef class MOSite
	# Type of the site (method, attribute or cast)
	var site_type: String is noinit

	# Count the implementation of the site
	fun stats(vm: VirtualMachine)
	do
		incr_preexist
		incr_from_site
		incr_concrete_site
		incr_self
		incr_rst_unloaded(vm)
		incr_type_impl(vm)
	end

	#
	fun incr_preexist do incr_specific_counters(expr_recv.is_pre, "preexist", "npreexist")

	#
	fun incr_type_impl(vm: VirtualMachine)
	do
		var impl = get_impl(vm)

		pstats.inc(site_type)

		if impl isa StaticImpl then
			pstats.inc("{site_type}_static")
			incr_specific_counters(expr_recv.is_pre, "{site_type}_preexist_static", "{site_type}_npreexist_static")
		else if impl isa SSTImpl then
			pstats.inc("{site_type}_sst")
			incr_specific_counters(expr_recv.is_pre, "{site_type}_preexist_sst", "{site_type}_npreexist_sst")
		else if impl isa PHImpl then
			pstats.inc("{site_type}_ph")
			incr_specific_counters(expr_recv.is_pre, "{site_type}_preexist_ph", "{site_type}_npreexist_ph")
		else if impl isa NullImpl then
			pstats.inc("{site_type}_null")
			incr_specific_counters(expr_recv.is_pre, "{site_type}_preexist_null", "{site_type}_npreexist_null")
		else
			abort
		end
	end

	#
	fun incr_from_site
	do
		# WARN : this partition is not exclusive

		if expr_recv.is_from_monew then
			pstats.inc("sites_from_new")
		else if expr_recv.is_from_mocallsite then
			pstats.inc("sites_from_meth_return")
		else if expr_recv.is_from_moparam then
			pstats.inc("sites_from_param")
		else
			abort
		end
	end

	#
	fun incr_concrete_site
	do
		if get_concretes.length > 0 then
			pstats.inc("concretes")
			incr_specific_counters(expr_recv.is_pre, "concretes_preexist", "concretes_npreexist")
		end
	end

	#
	fun incr_self
	do
		if expr_recv isa MOParam and expr_recv.as(MOParam).offset == 0 then pstats.inc("self")
	end

	#
	fun incr_rst_unloaded(vm: VirtualMachine)
	do
		var rst_loaded = pattern.rst.get_mclass(vm).as(not null).abstract_loaded

		if not rst_loaded then
			var is_pre = expr_recv.is_pre

			if self isa StaticImpl then
				incr_specific_counters(is_pre, "rst_unloaded_static_pre", "rst_unloaded_static_npre")
			else if self isa SSTImpl then
				incr_specific_counters(is_pre, "rst_unloaded_sst_pre", "rst_unloaded_sst_npre")
			else if self isa PHImpl then
				pstats.inc("rst_unloaded_ph")
			else if self isa NullImpl then
				pstats.inc("rst_unloaded_null")
			else 
				abort
			end
		end
	end
end

redef class MOCallSite
	redef var site_type = "method"
end

redef class MOAttrSite
	redef var site_type = "attribute"
end

redef class MOSubtypeSite
	redef var site_type = "cast"
end

redef class APropdef
	redef fun compile(vm)
	do
		super

		if mpropdef isa MMethodDef then
			for site in mpropdef.as(MMethodDef).mosites do

			print("stats")
				site.stats(vm)
				pstats.analysed_sites.add(site)
			end
		end
	end
end
