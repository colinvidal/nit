# Intermediate representation of nit program running inside the VM
module model_optimizations

import virtual_machine

# Pattern of a callsite
class MOPattern
	# Static type of the receiver
	var rst: MType

	# Global property called
	var gp: MProperty

	# Local properties candidates
	var lps = new List[MMethodDef]

	# CallSite using this pattern
	var callsites = new List[CallSite]

	# Add a callsite using this pattern, and the candidate LP if didn't already known
	fun add_callsite(cs: CallSite): nullable MOPattern
	do
		if cs.recv == rst and cs.mproperty == gp then
			if not lps.has(cs.mpropdef) then
				lps.add(cs.mpropdef)
			end

			if not callsites.has(cs) then
				callsites.add(cs)
			end

			return self
		end

		return null
	end
end

# Root hierarchy
abstract class MOExpr
end

# MO of variables
abstract class MOVar
	super MOExpr

	# The offset of the variable in it environment, of the position of parameter
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

	# Tell if the class is loaded 
	var loaded: Bool
end

# MO of literals
class MOLit
	super MOExpr
end

# MO of a object site (method call, subtype test, attribute access)
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

	# The pattern of the expression
	var pattern: MOPattern
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
