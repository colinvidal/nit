# Intermediate representation of nit program running inside the VM
module intermediate_representation

import compiler::abstract_compiler

# Root hierarchy
class IRExpr
end

# IR of variables
class IRVar
	super IRExpr

	# The offset of the variable in it environment, of the position of parameter
	var offset: Int
end

# IR of variables with only one dependency
class IRSSAVar
	super IRVar

	# the expression that variable depends
	var dependency: IRExpr
end

# IR of variable with multiples dependencies
class IRPhiVar
	super IRVar

	# List of expressions that variable depends
	var dependencies: List[IRExpr]
end

# IR of each parameters given to a call site
class IRParam
	super IRVar
end

# IR of instantiation sites
class IRNew
	super IRExpr

	# Tell if the class is loaded 
	var loaded: Bool
end

# IR of literals
class IRLit
	super IRExpr
end

# IR of a object site (method call, subtype test, attribute access)
class IRSite
end

# IR of a subtype test site
class IRSubtypeSite
	super IRSite

	# Static type on which the test is applied
	var target: MType
end

# IR of global properties sites
class IRPropSite
	super IRSite

	# Global property of the expression
	var gp: MProperty

	# Static type of the receiver
	var st: MType
end

# IR of object expression
class IRExprSite
	super IRPropSite
	super IRExpr
end

# IR of attribute access
class IRAttrSite
	super IRPropSite
end

# IR of method call
class IRCallSite
	super IRExprSite

	# Values of each arguments
	var given_args: List[IRExpr]
end

# IR of read attribute
class IRReadSite
	super IRExprSite
	super IRAttrSite
end

# IR of write attribute
class IRWriteSite
	super IRAttrSite

	# Value to assign to the attribute
	var arg: IRExpr
end
