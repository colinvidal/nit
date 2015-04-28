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
	var impl: Implementation is noinit

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
	fun compute_impl
	do
		if lps.length == 1 then
			# The method is an intro or a redef
			if lps.first.mproperty.intro_mclassdef.name == "Object" then
				impl = new SSTImpl(false, gp.absolute_offset)
			else
				impl = new StaticImpl(true, lps.first)
			end
		else
			var pic = gp.intro_mclassdef
			
			# TODO: light way (other that is_subtype(new Object)) to test if the class is Object ?
			if pic.name == "Object" then
				impl = new SSTImpl(false, gp.absolute_offset)
			else if pic.mclass.is_position_unique then 
				impl = new SSTImpl(true, gp.absolute_offset)
			else
				impl = new PHImpl(false, gp.offset) 
			end
		end

		print("PATTERN IMPL {rst} {gp} => {impl} {impl.is_mutable}")
	end

	# Add a new callee
	fun add_lp(lp: MMethodDef)
	do
		if not lps.has(lp) then
			lps.add(lp)
			lp.callers.add(self)
			compute_impl
		end
	end

	init
	do
		print("NEW PATTERN {rst} {gp}")
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
	var concretes_receivers = new List[MClass]

	# Compute the concretes receivers. If return null, drop the list (all receivers can't be statically and with intra-procedural analysis determined)
	fun compute_concretes: Bool
	do
		if expr_recv isa MOVar then
			if expr_recv.as(MOVar).compute_concretes(concretes_receivers) then
				return true
			else
				concretes_receivers.clear
			end
		end

		return false
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

	redef var is_mutable = false
end

# Static implementation (used only for method call)
class StaticImpl
	super Implementation

	# The called method implementation
	var meth: MMethodDef
end

redef class MClass
	# Tell if in all loaded subclasses, this class has a method group on unique position
	fun is_position_unique: Bool
	do
		for cls, pos in positions_methods do
			if cls.loaded and pos == -1 then return false
		end

		return true
	end
end
