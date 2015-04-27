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

	# Exprsites using this pattern
	var exprsites = new List[MOExprSite]

	# Add a new exprsite on the pattern
	fun add_exprsite(vm: VirtualMachine, exprsite: MOExprSite)
	do
		# Get all lps of the gp of the pattern if there are defined on a subclass of the rst
		# Tell to each added lps that this pattern can be a caller
		for lp in gp.loaded_lps do
			if vm.is_subtype(lp.mclassdef.mclass.mclass_type, rst) then
				if not lps.has(lp) then
					lps.add(lp)
					lp.callers.add(self)
				end
			end
		end
		
		exprsites.add(exprsite)
		exprsite.pattern = self
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
end

# MO of variables with only one dependency
class MOSSAVar
	super MOVar

	# the expression that variable depends
	var dependency: MOExpr
end

# MO of variable with multiples dependencies
class MOPhiVar
	super MOVar

	# List of expressions that variable depends
	var dependencies: List[MOExpr]
end

# MO of each parameters given to a call site
class MOParam
	super MOVar
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
