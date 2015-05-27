# Statistics of the VM (implementations, preexistance...)
module stats

import vm_optimizations

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
	var pstats = new MOStats("LOWER") is writable

	# Preexist counters (withs transitions)
	var pstats_trans = new MOStats("REGULAR")
end

redef class ModelBuilder
	redef fun run_virtual_machine(mainmodule: MModule, arguments: Array[String])
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
		var loaded_cls = 0
		for cls in mainmodule.model.mclasses do if cls.loaded then loaded_cls += 1

		# Check if number of loaded classes by the VM matches with the counter
		var analysed_cls = pstats.get("loaded_classes_implicits")
		analysed_cls += pstats.get("loaded_classes_explicits")
		analysed_cls += pstats.get("loaded_classes_abstracts")
		if loaded_cls != analysed_cls then
			print("WARNING: numbers of loaded classes in [model: {loaded_cls}] [vm: {analysed_cls}]")
		end

		var compiled_methods = new List[MMethodDef]

		# Check if number of static callsites who preexists matches with the counter
		var preexist_static = 0

		for mprop in mainmodule.model.mproperties do
			if not mprop isa MMethod then continue
			for meth in mprop.mpropdefs do
				compiled_methods.add(meth)
				for site in meth.mosites do
					# Force to recompile the site (set the better allowed optimization)
					site.expr_recv.preexist_expr

					# Actually, we MUST use get_impl, but it needs to have vm as argument
					if site.impl isa StaticImpl and site.expr_recv.is_pre then
						preexist_static += 1
					else if site.pattern.impl isa StaticImpl and site.expr_recv.is_pre then
						preexist_static += 1
					end
				end
			end
		end

		if preexist_static != pstats.get("preexist_static") then
			print("WARNING: preexist_static {pstats.get("preexist_static")} is actually {preexist_static }")
		end

		# Recompile all active methods to get the upper bound of the preexistance
		# We don't need pstats counters with lower bound anymore

		var old_counters = sys.pstats
		pstats = new MOStats("UPPER")
		pstats.copy_static_data(old_counters)

		while compiled_methods.length != 0 do
			var m = compiled_methods.pop
			m.compiled = false
			m.preexist_all(interpreter)
		end
		print(pstats.pretty)
	end
end

redef class MMethodDef
	redef fun preexist_all(vm: VirtualMachine)
	do
		if not super(vm) then return false

		for site in mosites do
			var recv = site.expr_recv

			if recv.is_from_monew then pstats.inc("sites_from_new")
			if recv.is_from_mocallsite then pstats.inc("sites_from_meth_return")
			if recv.is_from_monew or recv.is_from_mocallsite then pstats.inc("sites_handle_by_extend_preexist")

			var is_pre = recv.is_pre
			var impl = site.get_impl(vm)
			var is_concretes = site.get_concretes.length > 0

			var is_self_recv = false
			if recv isa MOParam and recv.offset == 0 then is_self_recv = true

			if recv.is_pre then
				pstats.inc("preexist")
				if site.get_impl(vm) isa StaticImpl then pstats.inc("preexist_static")
			else
				pstats.inc("npreexist")
			end

			# attr_*
			if site isa MOAttrSite then
				if is_self_recv then pstats.inc("attr_self")

				if impl isa SSTImpl then
					incr_specific_counters(is_pre, "attr_preexist_sst", "attr_npreexist_sst")
					pstats.inc("impl_sst")
				else if impl isa PHImpl then 
					pstats.inc("attr_ph")
					pstats.inc("impl_ph")
				end

				if site isa MOReadSite then
					pstats.inc("attr_read")
				else
					pstats.inc("attr_write")
				end

				pstats.inc("attr")
				incr_specific_counters(is_pre, "attr_preexist", "attr_npreexist")
				if is_concretes then
					pstats.inc("attr_concretes_receivers")
					incr_specific_counters(is_pre, "attr_concretes_preexist", "attr_concretes_npreexist")
				end

			# cast_*
			else if site isa MOSubtypeSite then
				if is_self_recv then pstats.inc("cast_self")

				if impl isa StaticImpl then
					incr_specific_counters(is_pre, "cast_preexist_static", "cast_npreexist_static")
					pstats.inc("impl_static")
				else if impl isa SSTImpl then
					incr_specific_counters(is_pre, "cast_preexist_sst", "cast_npreexist_sst")
					pstats.inc("impl_sst")
				else
					pstats.inc("cast_ph")
					pstats.inc("impl_ph")
				end

				pstats.inc("cast")
				incr_specific_counters(is_pre, "cast_preexist", "cast_npreexist")
				if is_concretes then
					pstats.inc("cast_concretes_receivers")
					incr_specific_counters(is_pre, "cast_concretes_preexist", "cast_concretes_npreexist")
				end

			# meth_*
			else if site isa MOCallSite then
				if is_self_recv then pstats.inc("meth_self")

				if impl isa StaticImpl then
					incr_specific_counters(is_pre, "meth_preexist_static", "meth_npreexist_static")
					pstats.inc("impl_static")
				else if impl isa SSTImpl then
					incr_specific_counters(is_pre, "meth_preexist_sst", "meth_npreexist_sst")
					pstats.inc("impl_sst")
				else
					pstats.inc("meth_ph")
					pstats.inc("impl_ph")
				end

				pstats.inc("meth")
				incr_specific_counters(is_pre, "meth_preexist", "meth_npreexist")
				if is_concretes then 
					pstats.inc("meth_concretes_receivers")
					incr_specific_counters(is_pre, "meth_concretes_preexist", "meth_concretes_npreexist")
				end
			end
		end
		return true
	end

	# Avoid to write same thing everytimes in the previous function
	private fun incr_specific_counters(is_pre: Bool, yes: String, no: String)
	do
		if is_pre then
			pstats.inc(yes)
		else
			pstats.inc(no)
		end
	end
end

redef class VirtualMachine
	redef fun load_class(mclass)
	do
		if mclass.loaded then return

		super(mclass)

		if mclass.kind == abstract_kind and not mclass.mclass_type.is_primitive_type then
			pstats.inc("loaded_classes_abstracts")
		else
			pstats.inc("loaded_classes_explicits")
		end
	end
end

redef class ANewExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		var sup = super(vm, old_block)
		if not recvtype.is_primitive_type then pstats.inc("ast_new")
		return sup
	end
end

redef class ANode
	redef fun ast2mo: nullable MOExpr
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
	redef fun compile_ast(vm: VirtualMachine, lp: MMethodDef)
	do
		super(vm, lp)
		if n_expr.mtype isa MNullType or n_expr.mtype == null then
			pstats.inc("lits")
		else if n_expr.mtype.is_primitive_type then
			pstats.inc("primitive_sites")
		end
	end

	redef fun compile_ast_method(vm: VirtualMachine, lp: MMethodDef, recv: MOExpr, node_ast: ANode, is_attribute: Bool)
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
		else if n_expr.mtype.is_primitive_type then
			pstats.inc("primitive_sites")
		else if n_type.mtype.get_mclass(vm).mclass_type.is_primitive_type then
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
		else if n_expr.mtype.is_primitive_type then
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
		else if n_expr.mtype.get_mclass(vm).mclass_type.is_primitive_type then
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
		var file = new FileWriter.open("mo_stats_{lbl}.csv")	

		file.write(", method, attribute, cast, total\n")
	
		var self_meth = map["meth_self"]
		var self_attr = map["attr_self"]
		var self_cast = map["cast_self"]
		var self_sum = self_meth + self_attr + self_cast
		file.write("self, {self_meth}, {self_attr}, {self_cast}, {self_sum}\n")
		file.write("preexist, {map["meth_preexist"]}, {map["attr_preexist"]}, {map["cast_preexist"]}, {map["preexist"]}\n")
		file.write("npreexist, {map["meth_npreexist"]}, {map["attr_npreexist"]}, {map["cast_npreexist"]}, {map["npreexist"]}\n")

		var concretes_meth = map["meth_concretes_receivers"]
		var concretes_attr = map["attr_concretes_receivers"]
		var concretes_cast = map["cast_concretes_receivers"]
		var concretes_sum = concretes_meth + concretes_attr + concretes_cast
		file.write("concretes, {concretes_meth}, {concretes_attr}, {concretes_cast}, {concretes_sum}\n")

		var concretes_pre_meth = map["meth_concretes_preexist"]
		var concretes_pre_attr = map["attr_concretes_preexist"]
		var concretes_pre_cast = map["cast_concretes_preexist"]
		var concretes_pre_total = concretes_pre_meth + concretes_pre_attr + concretes_pre_cast
		file.write("preexist concretes, {concretes_pre_meth}, {concretes_pre_attr}, {concretes_pre_cast}, {concretes_pre_total}\n")

		var concretes_npre_meth = map["meth_concretes_npreexist"]
		var concretes_npre_attr = map["attr_concretes_npreexist"]
		var concretes_npre_cast = map["cast_concretes_npreexist"]
		var concretes_npre_total = concretes_npre_meth + concretes_npre_attr + concretes_npre_cast
		file.write("npreexist concretes, {concretes_npre_meth}, {concretes_npre_attr}, {concretes_npre_cast}, {concretes_npre_total}\n")

		var meth_static = map["meth_preexist_static"] + map["meth_npreexist_static"]
		var cast_static = map["cast_preexist_static"] + map["cast_npreexist_static"]
		file.write("static, {meth_static}, 0, {cast_static}, {map["impl_static"]}\n")

		file.write("static preexist, {map["meth_preexist_static"]}, 0, {map["cast_preexist_static"]}, {map["preexist_static"]}\n")

		var sum_npre_static = map["meth_npreexist_static"] + map["cast_npreexist_static"]
		file.write("static npreexist, {map["meth_npreexist_static"]}, 0, {map["cast_npreexist_static"]}, {sum_npre_static}\n")

		var meth_sst = map["meth_preexist_sst"] + map["meth_npreexist_sst"]
		var attr_sst = map["attr_preexist_sst"] + map["attr_npreexist_sst"]
		var cast_sst = map["cast_preexist_sst"] + map["cast_npreexist_sst"]
		file.write("sst, {meth_sst}, {attr_sst}, {cast_sst}, {map["impl_sst"]}\n")
	
		var sum_pre_sst = map["meth_preexist_sst"] + map["attr_preexist_sst"] + map["cast_preexist_sst"]
		file.write("sst preexist, {map["meth_preexist_sst"]}, {map["attr_preexist_sst"]}, {map["cast_preexist_sst"]}, {sum_pre_sst}\n")

		var sum_npre_sst = map["meth_npreexist_sst"] + map["attr_npreexist_sst"] + map["cast_npreexist_sst"]
		file.write("sst npreexist, {map["meth_npreexist_sst"]}, {map["attr_npreexist_sst"]}, {map["cast_npreexist_sst"]}, {sum_npre_sst}\n")

		file.write("ph, {map["meth_ph"]}, {map["attr_ph"]}, {map["cast_ph"]}, {map["impl_ph"]}\n")

		var optimization_inline = map["preexist_static"] + map["attr_preexist_sst"] + map["cast_preexist_sst"]
		file.write(",,,,,\n")
		file.write("optimisable inline,,,,{optimization_inline}\n")

		var cant_optimize = map["meth_npreexist_static"] + map["attr_npreexist_sst"] + map["cast_npreexist_sst"]
		file.write("non optimisable inline,,,,{cant_optimize}\n")

		var not_inline_subject = map["impl_ph"] + map["meth_sst"]
		file.write("non inline,,,,{not_inline_subject}")
		
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
		# decr (on regular counters) when implementation is reset
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
		# decr (on regular counters) if the preexistance of the receiver is reset
		map["preexist"] = 0

		# incr if a site isn't preexist
		# decr (on regular counters) if the preexistance of the receiver is reset
		map["npreexist"] = 0

		# incr if a site is preexist and it implementation is static
		# decr (on regular counters) if the preexistance of the receiver is reset
		map["preexist_static"] = 0

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