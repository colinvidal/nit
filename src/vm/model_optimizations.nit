# Intermediate representation of nit program running inside the VM
module model_optimizations

import virtual_machine

redef class Sys
	#
	fun dprint(buf: String)
	do
#		print(buf)
	end
end

# Root hierarchy of patterns
abstract class MOPattern
end

# Pattern of instantiation sites
class MONewPattern
	super MOPattern

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

# Pattern of a callsite
class MOSitePattern
	super MOPattern

	# Static type of the receiver
	var rst: MType

	# Global property called
	var gp: MMethod

	# Local properties candidates (a subset of gp.loaded_lps)
	var lps = new List[MMethodDef]

	# Implementation of the callsite determined by rst/pic
	private var impl: nullable Implementation is noinit

	# Exprsites using this pattern
	var exprsites = new List[MOExprSite]

	# Add a new exprsite on the pattern
	fun add_exprsite(exprsite: MOExprSite)
	do
		exprsites.add(exprsite)
		exprsite.pattern = self

		# Get all lps of the gp of the pattern if there are defined on a subclass of the rst
		# Tell to each added lps that this pattern can be a caller
		for lp in gp.loaded_lps do
#			if vm.is_subtype(lp.mclassdef.mclass.mclass_type, rst) then
				add_lp(lp)
#			end
		end
	end

	# Determine an implementation with pic/rst only
	private fun compute_impl(vm: VirtualMachine)
	do
		if gp.intro_mclassdef.mclass.is_instance_of_object(vm) then
			impl = new SSTImpl(false, gp.absolute_offset)
		else if lps.length == 1 then
			# The method is an intro or a redef
			impl = new StaticImpl(true, lps.first)
#		else if gp_pos_unique(vm) then
#			impl = new SSTImpl(true, gp.absolute_offset)
		else
			impl = new PHImpl(false, gp.offset) 
		end
	end

	private fun gp_pos_unique(vm: VirtualMachine): Bool
	do
		for expr in exprsites do
			if rst.get_mclass(vm) == null then
				return false
			else
				var cls = rst.get_mclass(vm) 
				if not cls.has_unique_method_pos(gp) then return false
			end
		end

		return true
	end

	# Add a new callee
	fun add_lp(lp: MMethodDef)
	do
#		dprint("add lp {lp} in pattern {self}")
		if not lps.has(lp) then
			lps.add(lp)
			lp.callers.add(self)
			if impl != null and impl.is_mutable then impl = null
			for expr in exprsites do expr.init_impl
		end
	end

	# Get implementation, compute it if not exists
	fun get_impl(vm: VirtualMachine): Implementation
	do
		if impl == null then compute_impl(vm)
		return impl.as(not null)
	end

	# True if a lp is compatible with self pattern (eg. if the lp has
	# the gp of self and if rst of lp is a subtype of rst of the pattern)
#	fun compatibl_with(vm: VirtualMachine, lp: MPropDef): Bool
#	do
##		dprint("compatible_with sub:{lp.mclassdef.mclass.mclass_type} ({lp.mclassdef.mclass.loaded}) sup:{rst} ({rst.as(MClassType).mclass.loaded})")
#		if vm.is_subtype(lp.mclassdef.mclass.mclass_type, rst) then
#			if gp == lp.mproperty then return true
#		end
#		return false
#	end

	# Add a new branch on the pattern
	fun handle_new_branch(lp: MMethodDef)
	do
#		dprint("pattern handle_new_branch")
		add_lp(lp)
	end
end

redef class MMethod
	# Local properties who belongs this global property currently loaded
	var loaded_lps = new List[MMethodDef]
end

redef class MMethodDef
	# Tell if the method has been compiled at least one time
	var compiled = false is writable

	# List of callers of this local property
	var callers = new List[MOSitePattern]

	# Return expression of the method (null if procedure)
	var return_expr: nullable MOExpr is writable

	# List of instantiations sites in this local property 
	var monews = new List[MONew]

	# List of object sites in this local property
	var mosites = new List[MOSite]
end

# Root hierarchy of expressions
abstract class MOExpr
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
end

# MO of each parameters given to a call site
class MOParam
	super MOVar

	redef fun compute_concretes(concretes) do return false
end

# MO of instantiation sites
class MONew
	super MOExpr

	# The local property containing this expression
	var lp: MMethodDef

	# The pattern of this expression
	var pattern: MONewPattern is writable, noinit
end

# MO of literals
class MOLit
	super MOExpr
end

# Root hierarchy of objets sites
abstract class MOSite
	# The expression of the receiver
	var expr_recv: MOExpr

	# The local property containing this expression
	var lp: MMethodDef

	# The pattern using by this expression site
	var pattern: MOSitePattern is writable, noinit

	# Implementation of the site (null if can't determine concretes receivers)
	private var impl: nullable Implementation is noinit

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
	private fun compute_impl(vm: VirtualMachine)
	do
		var gp = pattern.gp

		if gp.intro_mclassdef.mclass.is_instance_of_object(vm) then
			impl = new SSTImpl(false, gp.absolute_offset)
		else if get_concretes.length == 1 then
			var cls = get_concretes.first
			if cls.loaded then
				impl = new StaticImpl(true,
				vm.method_dispatch_ph(cls.vtable.internal_vtable,
				cls.vtable.mask,
				gp.intro_mclassdef.mclass.vtable.id, 
				gp.offset))
			else
				# The PHImpl here is mutable because it can be switch to a 
				# lightweight implementation when the class will be loaded
				impl = new PHImpl(true, gp.offset)
			end
		else if unique_meth_pos_concrete then
			# SST immutable because it can't be more than these concretes receiver statically
			impl = new SSTImpl(false, gp.absolute_offset)
		else
			impl = new PHImpl(false, gp.offset) 
		end
	end

	# Each concrete receiver has unique method position
	private fun unique_meth_pos_concrete: Bool
	do
		for recv in get_concretes do
			if not recv.loaded then return false
			if not recv.has_unique_method_pos(lp.mproperty) then return false
		end
		return true
	end

end

# MO of a subtype test site
class MOSubtypeSite
	super MOSite

	# Static type on which the test is applied
	var target: MType
end

# MO of global properties sites
abstract class MOPropSite
	super MOSite
end

# MO of object expression
abstract class MOExprSite
	super MOPropSite
	super MOExpr

end

# MO of attribute access
abstract class MOAttrSite
	super MOPropSite
end

# MO of method call
class MOCallSite
	super MOExprSite

	# Values of each arguments
	var given_args = new List[MOExpr]
end

# MO of read attribute
class MOReadSite
	super MOExprSite
	super MOAttrSite

	# Tell if the attribute is immutable
	var immutable = false
end

# MO of write attribute
class MOWriteSite
	super MOAttrSite

	# Value to assign to the attribute
	var arg: MOExpr
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

# Static implementation (used only for method call)
class StaticImpl
	super Implementation

	# The called method implementation
	var meth: MMethodDef
end

redef class MClass
	# List of patterns of MOExprSite
	var sites_patterns = new List[MOSitePattern]

	# Pattern of MONew of self
	var new_pattern = new MONewPattern(self)

	# Linearization of classes hierarchy
	var ordering: nullable Array[MClass]

	# Tell if in all loaded subclasses, this class has a method group on unique position
	fun has_unique_method_pos(meth: MMethod): Bool
	do
		var pic = meth.intro_mclassdef.mclass

		if not pic.loaded then return false
	
		if pic.positions_methods[self] == -1 then return false
		for cls, pos in positions_methods do if pos == -1 then return false
	
		return true
	end

	# Detect new branches added by a loading class
	# Add introduces and redifines local properties
	fun handle_new_branch	
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
						# Tell the patterns using this method there is a new branch
#						vm.handle_new_branch(mdef)
						redefs.add(mdef)
					end
				end
			end
		end

		for lp in redefs do
			for parent in ordering do
				for p in parent.sites_patterns do
					if p.gp == lp.mproperty then 
						if not sites_patterns.has(p) then sites_patterns.add(p)
						p.handle_new_branch(lp)
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

	# Get a copy of a linearization
	redef fun superclasses_ordering(v)
	do
		if ordering == null then ordering = super(v)
		return ordering.as(not null)
	end

	# Create (if not exists) and set a pattern for exprsites
	fun set_site_pattern(exprsite: MOExprSite, rst: MType, gp: MMethod)
	do
		var pattern: nullable MOSitePattern = null

		for p in sites_patterns do
			if p.gp == gp and p.rst == rst then
				pattern = p
				break
			end
		end

		if pattern == null then 
			pattern = new MOSitePattern(rst, gp)
			sites_patterns.add(pattern)
		end

		pattern.add_exprsite(exprsite)
#		dprint("ASendExpr pattern.exprsites: {pattern.exprsites}"s
	end

	# Add newsite expression in the NewPattern assocociated to this class
	fun set_new_pattern(newsite: MONew)
	do
		new_pattern.newexprs.add(newsite)
		newsite.pattern = new_pattern
	end
end

redef class VirtualMachine
	# List of patterns of MOExprSite
#	var sites_patterns = new List[MOSitePattern]

	# List of patterns of MONew
	var new_patterns = new List[MONewPattern]


#	# For tests only, to remove !
#	fun debug_if_not_internal(module_str: String): Bool
#	do
#		if module_str == "kernel" then return false
#		if module_str == "string" then return false
#		if module_str == "numeric" then return false
#		return true
#	end

#	# Handle new local property for update optimizing model
#	fun handle_new_branch(lp: MMethodDef)
#	do
##		if debug_if_not_internal(lp.mclassdef.mmodule.to_s) then dprint("new branch {lp.mclassdef} redefines {lp.name}")
#
#		# For each patterns in lp.gp with classdef of the lp <: pattern.rst
#		var compatibles_patterns = new List[MOSitePattern]
#		for p in sites_patterns do
#			if p.compatibl_with(self, lp) then compatibles_patterns.add(p)
#		end
##		if compatibles_patterns.length == 0 then dprint("no compatible patterns for {lp}")
#
#		for p in compatibles_patterns do p.handle_new_branch(lp)
#	end

	redef fun create_class(mclass)
	do
		# Get all superclasses loaded implicitly by mclass
		var implicit_loaded = new List[MClass]
		for cls in mclass.superclasses_ordering(self) do
			if not cls.loaded then implicit_loaded.add(cls)
		end

		super(mclass)

		for cls in implicit_loaded do
#			cls.handle_new_branch(self)
			cls.handle_new_branch
		end
	end
end

redef class MType
	# True if self is a primitive type
	fun is_primitive_type: Bool
	do
		if self.to_s == "Int" then return true
		if self.to_s == "nullable Int" then return true
		if self.to_s == "String" then return true
		if self.to_s == "nullable String" then return true
		return false
	end

	# Get the class of the type
	fun get_mclass(vm: nullable VirtualMachine): nullable MClass
	do
		if self isa MNullType then
			return null
		else if self isa MClassType then
			return self.mclass
		else if self isa MNullableType then
			return self.mtype.as(MClassType).mclass
		else if need_anchor then
			var anchor: MClassType
			var anchor_type = vm.frame.arguments.first.mtype
			
			if anchor_type isa MNullableType then
				anchor = anchor_type.mtype.as(MClassType)
			else
				anchor = anchor_type.as(MClassType)
			end
			
#			return anchor_to(vm.as(not null).mainmodule, anchor).as(MClassType).mclass
			return anchor_to(vm.as(not null).mainmodule, anchor).get_mclass(vm)
		else
			# NYI
			abort
		end
	end
end

