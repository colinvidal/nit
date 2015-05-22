# Intermediate representation of nit program running inside the VM
module model_optimizations

import ssa

redef class ToolContext
	# Disable inter-procedural analysis and 'new' cases
	var disable_preexistence_extensions = new OptionBool("Disable preexistence extensions", "--no-preexist-ext")

	# Enable traces of analysis
	var trace_on = new OptionBool("Display the trace of model optimizing / preexistence analysis", "--mo-trace")

	# Enable print stats
	var stats_on = new OptionBool("Display statistics of model optimizing / preexistence after execution", "--mo-stats")

	redef init
	do
		super
		option_context.add_option(disable_preexistence_extensions)
		option_context.add_option(trace_on)
		option_context.add_option(stats_on)
	end
end

redef class Sys
	# Display trace if --mo-trace is set
	fun trace(buf: String) do if trace_on then print(buf)

	# Tell if trace is enabled
	var trace_on: Bool

	# Tell if preexistence extensions are disabled
	var disable_preexistence_extensions: Bool

	# Preexist counters
	var pstats = new MOStats("LOWER") is writable

	# Preexist counters (withs transitions)
	var pstats_trans = new MOStats("REGULAR")
end

redef class ModelBuilder
	redef fun run_virtual_machine(mainmodule: MModule, arguments: Array[String])
	do
		sys.trace_on = toolcontext.trace_on.value
		sys.disable_preexistence_extensions = toolcontext.disable_preexistence_extensions.value

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
	end
end

# Pattern of instantiation sites
class MONewPattern
	# Class associated to the pattern
	var cls: MClass

	# MONew expressions using this pattern
	var newexprs = new List[MONew]

	# Tell if the class is loaded
	fun is_loaded: Bool
	do
		return cls.loaded
	end
end

# Pattern of objects sites
abstract class MOSitePattern
	# Type of the sites that refer to this pattern
	type S: MOSite

	# Static type of the receiver
	var rst: MType

	# List of expressions that refers to this pattern
	var sites = new List[S]

	# Implementation of the pattern (used if site as not concerte receivers list)
	var impl: nullable Implementation is noinit

	# Add a site
	fun add_site(site: S) is abstract

	# Get implementation, compute it if not exists
	fun get_impl(vm: VirtualMachine): Implementation
	do
		if impl == null then compute_impl(vm)
		return impl.as(not null)
	end

	# Compute the implementation
	private fun compute_impl(vm: VirtualMachine) is abstract
end

# Pattern of subtype test sites
class MOSubtypeSitePattern
	super MOSitePattern

	redef type S: MOSubtypeSite

	# Static type of the target
	var target: MType

	redef fun add_site(site) do
		assert not sites.has(site)

		sites.add(site)
		site.pattern = self
	end

	# For now, subtype test are not optimized at all
	# WARNING: must be checked
	redef fun compute_impl(vm)
	do 
		var pos_cls = rst.get_mclass(vm).get_position_methods(target.get_mclass(vm).as(not null))
		
		if pos_cls > 0 then
			impl = new SSTImpl(true, pos_cls)
		else
			impl = new PHImpl(false, target.get_mclass(vm).color)
		end
	end

end

# Pattern of properties sites (method call / attribute access)
abstract class MOPropSitePattern
	super MOSitePattern

	# Type of global properties
	type GP: MProperty

	# Type of local properties
	type LP: MPropDef

	redef type S: MOPropSite

	# The global property
	var gp: GP

	# Candidates local properties owning by the GP
	var lps = new List[LP]

	redef fun add_site(site)
	do
		assert not sites.has(site)

		sites.add(site)
		site.pattern = self
		for lp in gp.loaded_lps do add_lp(lp)
	end

	# Add a candidate LP
	fun add_lp(lp: LP)
	do
		if not lps.has(lp) then
			lps.add(lp)
			lp.callers.add(self)
			if impl != null and impl.is_mutable then impl = null
			for site in sites do site.init_impl
		end
	end

	# Determine an implementation with pic/rst
	redef fun compute_impl(vm)
	do
		if not rst.get_mclass(vm).loaded then
			impl = new PHImpl(false, gp.offset)
			return
		end

		var pos_cls = rst.get_mclass(vm).get_position_methods(gp.intro_mclassdef.mclass)

		if gp.intro_mclassdef.mclass.is_instance_of_object(vm) then
			impl = new SSTImpl(false, pos_cls + gp.offset)
		else if lps.length == 1 then
			# The method is an intro or a redef
			impl = new StaticImplProp(true, lps.first)
		else if pos_cls > 0 then
			impl = new SSTImpl(true, pos_cls + gp.offset)
		else
			impl = new PHImpl(false, gp.offset) 
		end
	end
end

# Pattern of expression sites (method call / read attribute)
abstract class MOExprSitePattern
	super MOPropSitePattern

	redef type S: MOExprSite
end

# Pattern of method call
class MOCallSitePattern
	super MOExprSitePattern

	redef type GP: MMethod

	redef type LP: MMethodDef

	redef type S: MOCallSite
end

# Common subpattern of all attributes (read/write)
abstract class MOAttrPattern
	super MOPropSitePattern

	# Because the AST gives callsites with MMethod and MMethodDef for accessors,
	# we can't down the bound to MAttribute/MAttributeDef...

	# redef type GP: MAttribute

	# redef type LP: MAttributeDef
	
	redef fun compute_impl(vm)
	do
		if not rst.get_mclass(vm).loaded then
			impl = new PHImpl(false, gp.offset)
			return
		end

		var pos_cls = rst.get_mclass(vm).get_position_methods(gp.intro_mclassdef.mclass)

		if gp.intro_mclassdef.mclass.is_instance_of_object(vm) then
			impl = new SSTImpl(false, pos_cls + gp.offset)
		else if pos_cls > 0 then
			# Like the MOSiteAttr::compute_impl, we don't make static dispatch as it's an attribute access
			impl = new SSTImpl(true, pos_cls + gp.offset)
		else
			impl = new PHImpl(false, gp.offset) 
		end
	end
end

# Pattern of read attribute
class MOReadSitePattern
	super MOExprSitePattern
	super MOAttrPattern

	redef type S: MOReadSite
end

# Pattern of write attribute
class MOWriteSitePattern
	super MOAttrPattern

	redef type S: MOWriteSite
end

redef class MProperty
	# Type of owning local properties
	type LP: MPropDef
	
	# Local properties who belongs this global property currently loaded
	var loaded_lps = new List[LP]
end

redef class MPropDef
	# Type of the patterns who can use this local property
	type P: MOPropSitePattern

	# List of patterns who use this local property
	var callers = new List[P]
end

redef class MMethod
	redef type LP: MMethodDef
end

redef class MMethodDef
	# See MOAttrPattern, same problem...
	# redef type P: MOCallSitePattern

	# Tell if the method has been compiled at least one time (not in MMethodDef because attribute can have blocks)
	var compiled = false is writable
	
	# Return expression of the method (null if procedure)
	var return_expr: nullable MOExpr is writable

	# List of instantiations sites in this local property 
	var monews = new List[MONew]

	# List of object sites in this local property
	var mosites = new List[MOSite]
end

# Root hierarchy of expressions
abstract class MOExpr
	# Tell if the expression comes from MONew
	fun is_from_monew: Bool do return false

	# Tell if the expression comes from MOCallSite (return of method)
	fun is_from_mocallsite: Bool do return false
end

# MO of variables
abstract class MOVar
	super MOExpr

	# The offset of the variable in it environment, or the position of parameter
	var offset: Int

	# Compute concrete receivers (see MOCallSite / MOSite)
	fun compute_concretes(concretes: List[MClass]): Bool is abstract

	#
	fun valid_and_add_dep(dep: MOExpr, concretes: List[MClass]): Bool
	do
		if dep isa MONew then
			var cls = dep.pattern.cls
			if not concretes.has(cls) then concretes.add(cls)
			return true
		end
		return false
	end
end

# MO of variables with only one dependency
class MOSSAVar
	super MOVar

	# the expression that variable depends
	var dependency: MOExpr

	redef fun compute_concretes(concretes) do return valid_and_add_dep(dependency, concretes)

	redef fun is_from_monew do return dependency.is_from_monew

	redef fun is_from_mocallsite do return dependency.is_from_mocallsite
end

# MO of variable with multiples dependencies
class MOPhiVar
	super MOVar

	# List of expressions that variable depends
	var dependencies: List[MOExpr]

	redef fun compute_concretes(concretes)
	do
		for dep in dependencies do
			if not valid_and_add_dep(dep, concretes) then return false
		end
		return true
	end

	redef fun is_from_monew
	do
		for dep in dependencies do
			if dep.is_from_monew then return true
		end

		return false
	end

	redef fun is_from_mocallsite
	do
		for dep in dependencies do
			if dep.is_from_mocallsite then return true
		end

		return false
	end
end

# MO of each parameters given to a call site
class MOParam
	super MOVar

	redef fun compute_concretes(concretes) do return false
end

# MO of instantiation sites
class MONew
	super MOExpr

	# The local property containing this site 
	var lp: MMethodDef

	# The pattern of this site
	var pattern: MONewPattern is writable, noinit

	redef fun is_from_monew do return true
end

# MO of literals
class MOLit
	super MOExpr
end

# Root hierarchy of objets sites
abstract class MOSite
	# The type of the site pattern associated to this site
	type P: MOSitePattern

	# The expression of the receiver
	var expr_recv: MOExpr

	# The local property containing this expression
	var lp: MPropDef

	# The pattern using by this expression site
	var pattern: P is writable, noinit

	# Implementation of the site (null if can't determine concretes receivers)
	var impl: nullable Implementation is noinit

	# List of concretes receivers if ALL receivers can be statically and with intra-procedural analysis determined
	private var concretes_receivers: nullable List[MClass] is noinit

	# Compute the concretes receivers.
	# If return null, drop the list (all receivers can't be statically and with intra-procedural analysis determined)
	private fun compute_concretes
	do
		if expr_recv isa MOVar then
			if not expr_recv.as(MOVar).compute_concretes(concretes_receivers.as(not null)) then
				concretes_receivers.clear
			end
		end
	end

	# Get concretes receivers (or return empty list)
	fun get_concretes: List[MClass]
	do
		if concretes_receivers == null then
			concretes_receivers = new List[MClass]
			compute_concretes
		end
		return concretes_receivers.as(not null)
	end

	# Get the implementation of the site
	fun get_impl(vm: VirtualMachine): Implementation
	do
		if get_concretes.length == 0 then
			return pattern.get_impl(vm)
		else
			if impl == null then compute_impl(vm)
			return impl.as(not null)
		end
	end

	# Initialise the implementation decision
	fun init_impl do impl = null

	# Compute the implementation with rst/pic
	private fun compute_impl(vm: VirtualMachine) is abstract
end

# MO of a subtype test site
class MOSubtypeSite
	super MOSite

	redef type P: MOSubtypeSitePattern

	# Static type on which the test is applied
	var target: MType

	# Call this method ONLY if we are sure that target is loaded
	redef fun compute_impl(vm)
	do
		if not target.get_mclass(vm).loaded then
			# The PHImpl here is mutable because it can be switch to a 
			# lightweight implementation when the class will be loaded
			impl = new PHImpl(false, pattern.rst.get_mclass(vm).color)
			return
		end

		var pos_cls = pattern.rst.get_mclass(vm).get_position_methods(target.get_mclass(vm).as(not null))

		if get_concretes.length == 1 then
			impl = new StaticImplSubtype(true,
			vm.inter_is_subtype_ph(target.get_mclass(vm).vtable.id,
			pattern.rst.get_mclass(vm).vtable.mask,
			pattern.rst.get_mclass(vm).vtable.internal_vtable))		
		else if pos_cls > 0 then
			impl = new SSTImpl(true, pos_cls)
		else
			impl = new PHImpl(false, target.get_mclass(vm).color) 
		end
	end

	redef fun get_impl(vm)
	do
		# We must be sure that the target class is loaded to make a static impl
		var target_cls = target.get_mclass(vm)

		if get_concretes.length == 0 and target_cls != null and target_cls.loaded then
			compute_impl(vm)
			return impl.as(not null)
		else
			return pattern.get_impl(vm)
		end
	end
end

# MO of global properties sites
abstract class MOPropSite
	super MOSite

	redef type P: MOPropSitePattern

	redef fun compute_impl(vm)
	do
		var gp = pattern.gp

		if not pattern.rst.get_mclass(vm).loaded then
			# The PHImpl here is mutable because it can be switch to a 
			# lightweight implementation when the class will be loaded
			impl = new PHImpl(false, gp.offset)
			return
		end

		var pos_cls = pattern.rst.get_mclass(vm).get_position_methods(gp.intro_mclassdef.mclass)

		if gp.intro_mclassdef.mclass.is_instance_of_object(vm) then
			impl = new SSTImpl(false, pos_cls + gp.offset)
		else if get_concretes.length == 1 then
			var cls = get_concretes.first
			impl = new StaticImplProp(true,
			vm.method_dispatch_ph(cls.vtable.internal_vtable,
			cls.vtable.mask,
			gp.intro_mclassdef.mclass.vtable.id, 
			gp.offset))
		else if unique_meth_pos_concrete then
			# SST immutable because it can't be more than these concretes receiver statically
			impl = new SSTImpl(false, pos_cls + gp.offset)
		else
			impl = new PHImpl(false, gp.offset) 
		end
	end
	
	# Each concrete receiver has unique method position
	private fun unique_meth_pos_concrete: Bool
	do
		var gp = pattern.gp

		for recv in get_concretes do
			if not recv.loaded then return false
			if recv.get_position_methods(gp.intro_mclassdef.mclass) < 0 then return false
		end

		return true
	end
end

# MO of object expression
abstract class MOExprSite
	super MOPropSite
	super MOExpr

	redef type P: MOExprSitePattern
end

# MO of attribute access
abstract class MOAttrSite
	super MOPropSite

	redef type P: MOAttrPattern

	redef fun compute_impl(vm)
	do
		var gp = pattern.gp

		if not pattern.rst.get_mclass(vm).loaded then
			# The PHImpl here is mutable because it can be switch to a 
			# lightweight implementation when the class will be loaded
			impl = new PHImpl(false, gp.offset)
			return
		end

		var pos_cls = pattern.rst.get_mclass(vm).get_position_methods(gp.intro_mclassdef.mclass)

		if gp.intro_mclassdef.mclass.is_instance_of_object(vm) then
			impl = new SSTImpl(false, pos_cls + gp.offset)
		else if unique_meth_pos_concrete then
			# SST immutable because it can't be more than these concretes receiver statically
			# We don't check if there is one or more concrete type, because we can't make a static dispatch
			# on attribute
			impl = new SSTImpl(false, pos_cls + gp.offset)
		else
			impl = new PHImpl(false, gp.offset) 
		end
	end
end

# MO of method call
class MOCallSite
	super MOExprSite

	redef type P: MOCallSitePattern

	# Values of each arguments
	var given_args = new List[MOExpr]

	redef fun is_from_mocallsite do return true
end

# MO of read attribute
class MOReadSite
	super MOExprSite
	super MOAttrSite

	redef type P: MOReadSitePattern

	# Tell if the attribute is immutable, useless at the moment
	var immutable = false
end

# MO of write attribute
class MOWriteSite
	super MOAttrSite

	redef type P: MOWriteSitePattern

	# Value to assign to the attribute
#	var arg: MOExpr
end

# Root of type implementation (sst, ph, static)
abstract class Implementation
	# Is is a mutable implementation ?
	var is_mutable: Bool
end

# Commons properties on object mecanism implementations (sst, ph)
abstract class ObjectImpl
	super Implementation

	# The (global if SST, relative if PH) offset of the property
	var offset: Int
end

# SST implementation
class SSTImpl super ObjectImpl end

# Perfect hashing implementation
class PHImpl
	super ObjectImpl
end

# Common class for static implementation between subtypes, attr, meth.
abstract class StaticImpl
	super Implementation
end

# Static implementation (used only for method call)
class StaticImplProp
	super StaticImpl

	# The called lp
	var lp: MPropDef
end

# Static implementation (used only for subtype tests)
class StaticImplSubtype
	super StaticImpl

	# Is subtype ?
	var is_subtype: Bool
end

redef class MClass
	# List of patterns of MOPropSite
	var sites_patterns = new List[MOPropSitePattern]

	# Pattern of MONew of self
	var new_pattern = new MONewPattern(self)

	# List of patterns of subtypes test
	var subtype_pattern = new List[MOSubtypeSitePattern]

	# Detect new branches added by a loading class
	# Add introduces and redifines local properties
	fun handle_new_class
	do	
		var redefs = new List[MMethodDef]

		# mclassdef.mpropdefs contains intro & redef methods
		for classdef in mclassdefs do
			for i in [0..classdef.mpropdefs.length - 1] do
				var mdef = classdef.mpropdefs[i]
				if mdef isa MMethodDef then
					# Add the method implementation in loadeds implementations of the associated gp
					mdef.mproperty.loaded_lps.add(mdef)
					if not mdef.is_intro then
						# There is a new branch
						redefs.add(mdef)
					end
				end
			end
		end

		# For each class who know one of the redefs methods, tell the pattern there is a new branch
		for lp in redefs do
			for parent in ordering do
				for p in parent.sites_patterns do
					if p.gp == lp.mproperty then 
						if not sites_patterns.has(p) then sites_patterns.add(p)
						p.add_lp(lp)
					end
				end
			end
		end
	end

	# `self` is an instance of object
	fun is_instance_of_object(vm:VirtualMachine): Bool
	do
		return self.in_hierarchy(vm.mainmodule).greaters.length == 1
	end

	# Create (if not exists) and set a pattern for object subtype sites
	fun set_subtype_pattern(site: MOSubtypeSite, rst: MType)
	do
		var pattern: nullable MOSubtypeSitePattern = null

		for p in subtype_pattern do
			if p.rst == rst and p.target == site.target then
				pattern = p
				break
			end
		end

		if pattern == null then
			pattern = new MOSubtypeSitePattern(rst, site.target)
			subtype_pattern.add(pattern)
		end

		pattern.add_site(site)
	end

	# Create (if not exists) and set a pattern for objet prop sites
	fun set_site_pattern(site: MOPropSite, rst: MType, gp: MProperty)
	do
		var pattern: nullable MOPropSitePattern = null

		for p in sites_patterns do
			if p isa MOCallSitePattern and not site isa MOCallSite then
				continue
			else if p isa MOReadSitePattern and not site isa MOReadSite then
				continue
			else if p isa MOWriteSitePattern and not site isa MOWriteSite then
				continue
			end

			if p.gp == gp and p.rst == rst then
				pattern = p
				break
			end
		end

		if pattern == null then 
			if site isa MOCallSite then
				pattern = new MOCallSitePattern(rst, gp.as(MMethod))
			else if site isa MOReadSite then
				pattern = new MOReadSitePattern(rst, gp)
			else if site isa MOWriteSite then
				pattern = new MOWriteSitePattern(rst, gp)
			else
				abort
			end

			sites_patterns.add(pattern.as(not null))
		end

		pattern.add_site(site)
	end

	# Add newsite expression in the NewPattern assocociated to this class
	fun set_new_pattern(newsite: MONew)
	do
		new_pattern.newexprs.add(newsite)
		newsite.pattern = new_pattern
	end
end

redef class VirtualMachine
	# The top of list is the type of the receiver that will be used after new_frame
	var next_receivers = new List[MType]
end

redef class MType
	# True if self is a primitive type
	fun is_primitive_type: Bool
	do
		if self.to_s == "Int" then return true
		if self.to_s == "nullable Int" then return true
		if self.to_s == "String" then return true
		if self.to_s == "nullable String" then return true
		if self.to_s == "Char" then return true
		if self.to_s == "nullable Char" then return true
		if self.to_s == "Bool" then return true
		return false
	end

	# Get the class of the type
	fun get_mclass(vm: VirtualMachine): nullable MClass
	do
		if self isa MNullType then
			return null
		else if self isa MNotNullType then
			return self.mtype.get_mclass(vm)
		else if self isa MClassType then
			return self.mclass
		else if self isa MNullableType then
			return self.mtype.get_mclass(vm)
		else if (self isa MVirtualType or self isa MParameterType) and need_anchor then
			var anchor: MClassType
			var anchor_type = vm.next_receivers.last
			
			if anchor_type isa MNullableType then
				anchor = anchor_type.mtype.as(MClassType)
			else
				anchor = anchor_type.as(MClassType)
			end
			
			return anchor_to(vm.mainmodule, anchor).get_mclass(vm)
		else
			# NYI
			abort
		end
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

		file.write(", meth, attr, cast, total\n")
	
		var self_meth = map["meth_self"]
		var self_attr = map["attr_self"]
		var self_cast = map["cast_self"]
		var self_sum = self_meth + self_attr + self_cast
		file.write("self, {self_meth}, {self_attr}, {self_cast}, {self_sum}\n")
		file.write("pre, {map["meth_preexist"]}, {map["attr_preexist"]}, {map["cast_preexist"]}, {map["preexist"]}\n")
		file.write("npre, {map["meth_npreexist"]}, {map["attr_npreexist"]}, {map["cast_npreexist"]}, {map["npreexist"]}\n")

		var concretes_meth = map["meth_concretes_receivers"]
		var concretes_attr = map["attr_concretes_receivers"]
		var concretes_cast = map["cast_concretes_receivers"]
		var concretes_sum = concretes_meth + concretes_attr + concretes_cast
		file.write("concretes, {concretes_meth}, {concretes_attr}, {concretes_cast}, {concretes_sum}\n")

		var meth_static = map["meth_preexist_static"] + map["meth_npreexist_static"]
		var cast_static = map["cast_preexist_static"] + map["cast_npreexist_static"]
		file.write("static, {meth_static}, 0, {cast_static}, {map["impl_static"]}\n")

		file.write("static-pre, {map["meth_preexist_static"]}, 0, {map["cast_preexist_static"]}, {map["preexist_static"]}\n")

		var sum_npre_static = map["meth_npreexist_static"] + map["cast_npreexist_static"]
		file.write("static-npre, {map["meth_npreexist_static"]}, 0, {map["cast_npreexist_static"]}, {sum_npre_static}\n")

		var meth_sst = map["meth_preexist_sst"] + map["meth_npreexist_sst"]
		var attr_sst = map["attr_preexist_sst"] + map["attr_npreexist_sst"]
		var cast_sst = map["cast_preexist_sst"] + map["cast_npreexist_sst"]
		file.write("sst, {meth_sst}, {attr_sst}, {cast_sst}, {map["impl_sst"]}\n")
	
		var sum_pre_sst = map["meth_preexist_sst"] + map["attr_preexist_sst"] + map["cast_preexist_sst"]
		file.write("sst-pre, {map["meth_preexist_sst"]}, {map["attr_preexist_sst"]}, {map["cast_preexist_sst"]}, {sum_pre_sst}\n")

		var sum_npre_sst = map["meth_npreexist_sst"] + map["attr_npreexist_sst"] + map["cast_npreexist_sst"]
		file.write("sst-npre, {map["meth_npreexist_sst"]}, {map["attr_npreexist_sst"]}, {map["cast_npreexist_sst"]}, {sum_npre_sst}\n")

		file.write("ph, {map["meth_ph"]}, {map["attr_ph"]}, {map["cast_ph"]}, {map["impl_ph"]}\n")
		
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
		map["meth_preexist"] = 0
		map["meth_npreexist"] = 0
		map["meth_preexist_static"] = 0
		map["meth_npreexist_static"] = 0
		map["meth_preexist_sst"] = 0
		map["meth_npreexist_sst"] = 0
		map["meth_ph"] = 0
	end
end


