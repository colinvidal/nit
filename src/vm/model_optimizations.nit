# Intermediate representation of nit program running inside the VM
module model_optimizations

import virtual_machine

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
class MOExprSitePattern
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
	fun add_exprsite(vm: VirtualMachine, exprsite: MOExprSite)
	do
		# Get all lps of the gp of the pattern if there are defined on a subclass of the rst
		# Tell to each added lps that this pattern can be a caller
		for lp in gp.loaded_lps do
			if vm.is_subtype(lp.mclassdef.mclass.mclass_type, rst) then
				add_lp(lp)
			end
		end
		
		exprsites.add(exprsite)
		exprsite.pattern = self
	end

	# Determine an implementation with pic/rst only
	private fun compute_impl(vm: VirtualMachine)
	do
		# si gp intro par object -> sst immutable
		# sinon si |lps| == 1 -> static mutable
		# sinon si position methode invariante du rst dans le pic et pour tous les sous-types chargés du rst -> sst mutable
		# sinon -> ph immutable
	
		if gp.intro_mclassdef.mclass.is_instance_of_object(vm) then
			impl = new SSTImpl(false, gp.absolute_offset)
		else if lps.length == 1 then
			# The method is an intro or a redef
			impl = new StaticImpl(true, lps.first)
		else if rst.as(MClassType).mclass.has_unique_method_pos(gp) then 
			impl = new SSTImpl(true, gp.absolute_offset)
		else
			impl = new PHImpl(gp.offset) 
		end
	end

	# Add a new callee
	fun add_lp(lp: MMethodDef)
	do
		if not lps.has(lp) then
			lps.add(lp)
			lp.callers.add(self)
			if impl != null and impl.is_mutable then impl = null
		end

		for expr in exprsites do expr.init_impl
	end

	# Get implementation, compute it if not exists
	fun get_impl(vm: VirtualMachine): Implementation
	do
		if impl == null then compute_impl(vm)
		return impl.as(not null)
	end

	# True if a lp is compatible with self pattern (eg. if the lp has
	# the gp of self and if rst of lp is a subtype of rst of the pattern)
	fun compatibl_with(vm: VirtualMachine, lp: MPropDef): Bool
	do
		if vm.is_subtype(lp.mclassdef.mclass.mclass_type, rst) then
			if gp == lp.mproperty then return true
		end
		return false
	end

	# Add a new branch on the pattern
	fun handle_new_branch(lp: MMethodDef)
	do
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
	var callers = new List[MOExprSitePattern]

	# Return expression of the method (null if procedure)
	var return_expr: nullable MOExpr is writable

	# List of expressions in this local property (without MOExprSite)
	# eg. attr.baz()
	var moexprs = new List[MOExpr]

	# List of site expressions in this local property
	# eg. a.foo().bar(), variable, instantiation site 
	var moexprsites = new List[MOExprSite]

	# List of object site in this local property (without MOExprSite)
	# eg. subtype test, write attribute
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

	# The expression of the receiver
	var expr_recv: MOExpr

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
end

# MO of object expression
abstract class MOExprSite
	super MOPropSite
	super MOExpr

	# The local property containing this expression
	var lp: MMethodDef

	# The pattern using by this expression site
	var pattern: MOExprSitePattern is writable, noinit
	
	# Implementation of the site (null if can't determine concretes receivers)
	private var impl: nullable Implementation is noinit

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
		# si gp intro par object -> sst immutable
		# sinon si |concretes| == 1 -> static mutable
		# sinon si position methode invariante dans le pic tous les recv et tous les sous-types du receveur -> sst mutable
		# sinon -> ph immutable

		var gp = pattern.gp

		if gp.intro_mclassdef.mclass.is_instance_of_object(vm) then
			impl = new SSTImpl(false, gp.absolute_offset)
		else if get_concretes.length == 1 then
			var cls = get_concretes.first
			if cls.loaded then
				impl = new StaticImpl(true, vm.method_dispatch_ph(cls.vtable.internal_vtable, cls.vtable.mask,
				gp.intro_mclassdef.mclass.vtable.id, gp.offset))
			else
				impl = new PHImpl(gp.offset)
			end
		else if unique_meth_pos_concrete then
			impl = new SSTImpl(true, gp.absolute_offset)
		else
			impl = new PHImpl(gp.offset) 
		end
	end

	# Each concrete receiver has unique method position
	private fun unique_meth_pos_concrete: Bool
	do
		for recv in get_concretes do
			if not recv.has_unique_method_pos(lp.mproperty) then return false
		end
		return true
	end
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

	# PH implementation is always immutable
	init(offset: Int)
	do
		super(false, offset)
	end
end

# Static implementation (used only for method call)
class StaticImpl
	super Implementation

	# The called method implementation
	var meth: MMethodDef
end

redef class MClass
	# Tell if in all loaded subclasses, this class has a method group on unique position
	fun has_unique_method_pos(meth: MMethod): Bool
	do
		var pic = meth.intro_mclassdef.mclass

		if not pic.loaded then return false
		

		print("has_unique_method_pos pic:{pic} self:{self} positions_methods:{pic.positions_methods[self]}")

		if pic.positions_methods[self] == -1 then return false
		for cls, pos in positions_methods do if pos == -1 then return false
	
		return true
	end

	redef fun make_vt(vm)
	do
		super

		# add introduces and redifines local properties
		# mclassdef.mpropdefs contains intro & redef methods
		for classdef in mclassdefs do
			for i in [1..classdef.mpropdefs.length - 1] do
				var mdef = classdef.mpropdefs[i]
				if mdef isa MMethodDef then
					# Add the method implementation in the loaded metods of the associated global property
					mdef.mproperty.loaded_lps.add(mdef)
					if not mdef.is_intro then
						# Tell the patterns using this method there is a new branch
						vm.handle_new_branch(mdef)
					end
				end
			end
		end
	end

	# `self` is an instance of object
	fun is_instance_of_object(vm:VirtualMachine): Bool
	do
		return self.in_hierarchy(vm.mainmodule).greaters.length == 1
#		return name == "Object"
	end
end

redef class VirtualMachine
	# List of patterns of MOExprSite
	var exprsites_patterns = new List[MOExprSitePattern]

	# List of patterns of MONew
	var new_patterns = new List[MONewPattern]

	# Create (if not exists) and set a pattern for exprsites
	fun set_exprsite_pattern(exprsite: MOExprSite, cs: CallSite)
	do
		var pattern: nullable MOExprSitePattern = null

		for p in exprsites_patterns do
			if p.gp == cs.mproperty and p.rst == cs.recv then
				pattern = p
				break
			end
		end

		if pattern == null then 
			pattern = new MOExprSitePattern(cs.recv, cs.mproperty)
			exprsites_patterns.add(pattern)
		end

		pattern.add_exprsite(self, exprsite)
	end

	# Create (if not exists) and set a pattern for newsites
	fun set_new_pattern(newsite: MONew, cls: MClass)
	do
		var pattern: nullable MONewPattern = null

		for p in new_patterns do
			if p.cls == cls then
				pattern = p
				break
			end
		end

		if pattern == null then
			pattern = new MONewPattern(cls)
			new_patterns.add(pattern)
		end

		pattern.newexprs.add(newsite)
		newsite.pattern = pattern
	end

	# For tests only, to remove !
	fun debug_if_not_internal(module_str: String): Bool
	do
		if module_str == "kernel" then return false
		if module_str == "string" then return false
		if module_str == "numeric" then return false
		return true
	end

	# Handle new local property for update optimizing model
	fun handle_new_branch(lp: MMethodDef)
	do
		if debug_if_not_internal(lp.mclassdef.mmodule.to_s) then print("new branch {lp.mclassdef} redefines {lp.name}")

		# For each patterns in lp.gp with classdef of the lp <: pattern.rst
		var compatibles_patterns = new List[MOExprSitePattern]
		for p in exprsites_patterns do
			if p.compatibl_with(self, lp) then compatibles_patterns.add(p)
		end

		for p in compatibles_patterns do p.handle_new_branch(lp)
	end

end
