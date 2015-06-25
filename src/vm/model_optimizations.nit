# Intermediate representation of nit program running inside the VM
module model_optimizations

import compilation

redef class ToolContext
	# Enable traces of analysis
	var trace_on = new OptionBool("Display the trace of model optimizing / preexistence analysis", "--mo-trace")

	redef init
	do
		super
		option_context.add_option(trace_on)
	end
end

redef class Sys
	# Display trace if --mo-trace is set
	fun trace(buf: String) do if trace_on then print(buf)

	# Tell if trace is enabled
	var trace_on: Bool

	# Hashmap used for clone AST to MO
	var ast2mo_clone_table = new HashMap[AExpr, MOEntity]
end

redef class ModelBuilder
	redef fun run_virtual_machine(mainmodule: MModule, arguments: Array[String])
	do
		sys.trace_on = toolcontext.trace_on.value
		super(mainmodule, arguments)
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

	# Add a site
	fun add_site(site: S) is abstract
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
	var callees = new List[LP]

	redef fun add_site(site)
	do
		assert not sites.has(site)

		sites.add(site)
		site.pattern = self
	end

	# Number of calls on uncompiled methods
	var cuc = 0

	# Add a new method on this pattern
	fun add_lp(mpropdef: LP)
	do
		callees.add(mpropdef)
		mpropdef.callers.add(self)
		cuc += 1
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

	#
	init(rst: MType, gp: MMethod)
	do
		self.rst = rst
		self.gp = gp

		var rsc = rst.get_mclass(sys.vm).as(not null)

		if not rsc.abstract_loaded then return

		for lp in gp.living_mpropdefs do
			if lp.mclassdef.mclass.ordering.has(rsc) then
				add_lp(lp)
			end
		end
	end
end

# Common subpattern of all attributes (read/write)
abstract class MOAttrPattern
	super MOPropSitePattern

	redef type GP: MAttribute

	redef type LP: MAttributeDef
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
	
	# Type of the pattern
	type PATTERN: MOPropSitePattern

	# List of patterns using this gp
	var patterns = new List[PATTERN] is lazy
end

redef class MPropDef
	# Type of the patterns who can use this local property
	type P: MOPropSitePattern

	# List of patterns who use this local property
	var callers = new List[P]

	# Compile the property
	fun compile_mo
	do
		for pattern in callers do
			pattern.cuc -= 1
		end
	end
end

redef class MMethod
	redef type LP: MMethodDef

	redef type PATTERN: MOCallSitePattern

	redef fun add_propdef(mpropdef)
	do
		super

		var ordering = mpropdef.mclassdef.mclass.ordering

		for pattern in patterns do
			var rsc = pattern.rst.get_mclass(sys.vm)

			if rsc.abstract_loaded and ordering.has(rsc) then
				pattern.add_lp(mpropdef)
			end
		end
	end
end

redef class MMethodDef
	redef type P: MOCallSitePattern
	
	# Return expression of the method (null if procedure)
	var return_expr: nullable MOExpr is writable

	# An object is never return if return_expr is not a MOVar
	fun return_expr_is_object: Bool do return return_expr isa MOVar

	# List of instantiations sites in this local property 
	var monews = new List[MONew]

	# List of object sites in this local property
	var mosites = new List[MOSite]
end

# Root hierarchy of MO entities
abstract class MOEntity
end

# Root hierarchy of expressions
abstract class MOExpr
	super MOEntity
end

# MO of variables
abstract class MOVar
	super MOExpr

	# The Variable objet refered by this node
	var variable: Variable

	# The offset of the variable in it environment, or the position of parameter
	var offset: Int

	# True if the variable is a parameter
	var parameter: Bool

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

	# The local property containing this site 
	var lp: MMethodDef

	# The pattern of this site
	var pattern: MONewPattern is writable, noinit
end

# MO of literals
class MOLit
	super MOExpr
end

# MO of primitives
class MOPrimitive
	super MOExpr
end

# Root hierarchy of objets sites
abstract class MOSite
	super MOEntity

	# The AST node where this site comes from
	var ast: AExpr 

	# The type of the site pattern associated to this site
	type P: MOSitePattern

	# The expression of the receiver
	var expr_recv: MOExpr is noinit

	# The local property containing this expression
	var lp: MPropDef

	# The pattern using by this expression site
	var pattern: P is writable, noinit

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

# MO of a subtype test site
class MOSubtypeSite
	super MOSite

	redef type P: MOSubtypeSitePattern

	# Static type on which the test is applied
	var target: MType
end

# MO of global properties sites
abstract class MOPropSite
	super MOSite

	redef type P: MOPropSitePattern
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
end

# MO of method call
class MOCallSite
	super MOExprSite

	redef type P: MOCallSitePattern

	# Values of each arguments
	var given_args = new List[MOExpr]
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
end

# MO of null
class MONull
	super MOLit
end

redef class MClass
	# List of patterns of MOPropSite
	var sites_patterns = new List[MOPropSitePattern]

	# Pattern of MONew of self
	var new_pattern = new MONewPattern(self)

	# List of patterns of subtypes test
	var subtype_pattern = new List[MOSubtypeSitePattern]

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
				pattern = new MOReadSitePattern(rst, gp.as(MAttribute))
			else if site isa MOWriteSite then
				pattern = new MOWriteSitePattern(rst, gp.as(MAttribute))
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
	
	redef fun new_frame(node, mpropdef, args)
	do
		next_receivers.push(args.first.mtype)
		var ret = super(node, mpropdef, args)
		next_receivers.pop
		return ret
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

redef class AExpr
	# Clone a AST expression to a MOEntity
	# `mpropdef` is the local property containing this expression (or expression-site)
	# Return a MOEntity it's already created (already in the clone table).
	# Otherwise, create it, set it in clone table, set it's dependencies, return it.
	fun ast2mo(mpropdef: MPropDef): MOEntity is abstract

	# Return the MOEntity if it's already on clone table
	fun get_mo_from_clone_table: nullable MOEntity
	do
		if sys.ast2mo_clone_table.has_key(self) then
			return sys.ast2mo_clone_table[self]
		end
		return null
	end
end

redef class AAttrExpr
	redef fun ast2mo(mpropdef)
	do
		var mo_entity = get_mo_from_clone_table
		if mo_entity != null then return mo_entity

		if self isa AAttrAssignExpr or self isa AAttrReassignExpr then
			# AAttrReassignExpr is not a subtype of AAttrAssignExpr, so we must do a checktype herebefore.
			var write_site = new MOWriteSite(self, mpropdef)
			sys.ast2mo_clone_table[self] = write_site
			write_site.expr_recv = n_expr.ast2mo(mpropdef).as(MOExpr)
			return write_site
		else
			# Read attribute access (or test to know if the attribute is set)
			var read_site = new MOReadSite(self, mpropdef)
			sys.ast2mo_clone_table[self] = read_site
			read_site.expr_recv = n_expr.ast2mo(mpropdef).as(MOExpr)
			return read_site
		end
	end
end

redef class AIsaExpr
	redef fun compile_ast(vm: VirtualMachine, lp: MMethodDef)
	do
		var ignore = false

		if n_expr.mtype isa MNullType or n_expr.mtype == null then
			# Ignore litterals cases of the analysis
			ignore = true
		else if n_expr.mtype.get_mclass(vm).mclass_type.is_primitive_type then
			# Ignore primitives cases of the analysis
			ignore = true
		end

		var recv = n_expr.ast2mo

		if recv != null and not ignore then
			var most = new MOSubtypeSite(self, recv, lp, cast_type.as(not null))
			var recv_class = n_expr.mtype.get_mclass(vm).as(not null)
			recv_class.set_subtype_pattern(most, recv_class.mclass_type)
			lp.mosites.add(most)
		end
	end

	redef fun ast2mo(mproperty)
	do
		var mo_entity = get_mo_from_clone_table
		if mo_entity != null then return mo_entity


	end
end

redef class AAsCastExpr
	redef fun compile_ast(vm: VirtualMachine, lp: MMethodDef)
	do
		var ignore = false

		if n_expr.mtype isa MNullType or n_expr.mtype == null then
			# Ignore litterals cases of the analysis
			ignore = true
		else if n_expr.mtype.is_primitive_type then
			# Ignore primitives cases of the analysis
			ignore = true
		else if n_type.mtype.get_mclass(vm).mclass_type.is_primitive_type then
			ignore = true
			# Sometimes, the cast come from a generic RST that is not resolve,
			# so, if the model allow a cast to a primitive type, the receiver have a primitive type
		end

		var recv = n_expr.ast2mo

		if recv != null and not ignore then
			var moattr = new MOSubtypeSite(self, recv, lp, n_type.mtype.as(not null))
			var recv_class = n_expr.mtype.get_mclass(vm).as(not null)
			recv_class.set_subtype_pattern(moattr, recv_class.mclass_type)
		end
	end
end

redef class Variable
	# Represents the view of the variable in the optimizing representation
	var movar: nullable MOVar

	# Create (if doesn't exists) the movar corresponding to AST node, and return it
	fun get_movar(node: AExpr): nullable MOVar
	do
		if movar == null then
			if node isa ASelfExpr then
				movar = new MOParam(self, 0)
			else if node isa AVarExpr then
				# A variable read
				if node.variable.parameter then
					movar = new MOParam(self, node.variable.position)
				else if node.variable.dep_exprs.length == 1 then
#				if node.variable.dep_exprs.length == 1 then
					if node.variable.parameter then
						movar = new MOParam(self, node.variable.position)
					else
						var mo = node.variable.dep_exprs.first.ast2mo
						if mo != null then movar = new MOSSAVar(self, node.variable.position, mo)
					end
				else if node.variable.dep_exprs.length > 1 then
					var phi = new List[MOExpr]
					for a_expr in node.variable.dep_exprs do
						var mo = a_expr.ast2mo
						if mo != null then phi.add(mo)
					end

					if phi.length == 1 then
						movar = new MOSSAVar(self, node.variable.position, phi.first)
					else if phi.length > 1 then
						movar = new MOPhiVar(self, node.variable.position, phi)
						trace("MOPhiVar AST phi len: {phi.length} | node.variable.dep_exprs: {node.variable.dep_exprs}")
					end
				end
			end
		end
		return movar
	end
end

redef class ANewExpr
	# Represent the view of the new expression in the optimizing reprenstation
	var monew: nullable MONew

	redef fun generate_basic_blocks(ssa, old_block)
	do
		var sup = super

		# Int, String, and Number are abstract, so we can't instantiate them with "new" keyword.
		# Is there others primitives types we can do a "new" on it ? If not, remove this test.
		if not recvtype.is_primitive_type then
			monew = new MONew(ssa.propdef.mpropdef.as(MMethodDef))
			ssa.propdef.mpropdef.as(MMethodDef).monews.add(monew.as(not null))
			recvtype.mclass.set_new_pattern(monew.as(not null))
		end

		return sup
	end

	redef fun ast2mo do return monew
end

#redef class ANode
#	# True if self is a primitive node
#	fun is_primitive_node: Bool
#	do
#		if self isa AIntExpr then return true
#		if self isa ACharExpr then return true
#		if self isa ANullExpr then return true
#		if self isa AStringFormExpr then return true
#		if self isa ATrueExpr then return true
#		if self isa AFalseExpr then return true
#		if self isa ASuperstringExpr then return true
#		return false
#	end
#
#	# Convert AST node into MOExpression
#	fun ast2mo: nullable MOExpr
#	do
#		if not is_primitive_node then trace("WARN: NYI {self}")
#		return null
#	end
#end

redef class ASelfExpr
	redef fun ast2mo
	do
		return variable.get_movar(self)
	end
end

redef class AVarExpr
	redef fun ast2mo
	do
		return variable.get_movar(self)
	end
end

redef class APropdef
#	# List of ast node to compile
#	var to_compile = new List[AToCompile]
#
#	# list of return expression of the optimizing model
#	# Null if this fuction is a procedure
#	var mo_dep_exprs: nullable MOExpr = null
#
	# Force to compute the implementation of the site when AST node is compiled
	redef fun compile(vm)
	do
		super

		if self isa AMethPropdef then
			for site in object_sites do
				site.ast2mo_site(self)
			end

			mpropdef.as(MMethodDef).return_expr = returnvar.get_movar(self)

			mpropdef.compile_mo
		end
		
#			# Generate MO for sites inside the propdef
#			for expr in to_compile do expr.compile_ast(vm, mpropdef.as(MMethodDef))
#
#			# Generate MO for return of the propdef
#			if returnvar.dep_exprs.length == 1 then
#				var moexpr = returnvar.dep_exprs.first.ast2mo
#				if moexpr != null then 
#					mo_dep_exprs = new MOSSAVar(returnvar, returnvar.position, moexpr)
#				else
#					mo_dep_exprs = new MOPrimitive
#				end
#			else if returnvar.dep_exprs.length > 1 then
#				var deps = new List[MOExpr]
#				for a_expr in returnvar.dep_exprs do
#					var moexpr = a_expr.ast2mo
#					if moexpr != null then deps.add(moexpr)
#				end
#
#				if deps.length == 1 then
#					mo_dep_exprs = new MOSSAVar(returnvar, returnvar.position, deps.first)
#				else if deps.length > 1 then
#					mo_dep_exprs = new MOPhiVar(returnvar, returnvar.position, deps)
#				else
#					mo_dep_exprs = new MOPrimitive
#				end
#			end
#
#			mpropdef.as(MMethodDef).return_expr = mo_dep_exprs
#		end

#		mpropdef.compile(vm)
	end
end

redef class ASendExpr
	redef fun ast2mo
	do
		return mocallsite
	end

	# Compile this ast node in MOCallSite after SSA
	redef fun compile_ast(vm: VirtualMachine, lp: MMethodDef)
	do
#		print("[model_optimizations] compile_ast of {self} in {lp}")
		var ignore = false

		if n_expr.mtype isa MNullType or n_expr.mtype == null then
			# Ignore litterals cases of the analysis
			ignore = true
		else if n_expr.mtype.is_primitive_type then
			# Ignore primitives cases of the analysis
			ignore = true
		end

		var recv = n_expr.ast2mo

		if recv != null and not ignore then
			var cs = callsite.as(not null)

			# Static dispatch of global model to known if we handle method call of attribute access
			var has_redef = cs.mproperty.mpropdefs.length > 1
			var node_ast = vm.modelbuilder.mpropdef2node(cs.mpropdef)
			var is_attribute = node_ast isa AAttrPropdef

			if is_attribute and not has_redef then
				compile_ast_accessor(vm, lp, recv, node_ast.as(not null))
			else
				compile_ast_method(vm, lp, recv, node_ast.as(not null), is_attribute)
			end
		end
	end

	# Unique LP, simple attr access, make it as a real attribute access (eg. _attr)
	fun compile_ast_accessor(vm: VirtualMachine, lp: MMethodDef, recv: MOExpr, node_ast: ANode)
	do
		var moattr: MOAttrSite
		var params_len = callsite.as(not null).msignature.mparameters.length

		if params_len == 0 then
			# The node is a MOReadSite
			moattr = new MOReadSite(self, recv, lp)
		else
			# The node is a MOWriteSite
			assert params_len == 1
			moattr = new MOWriteSite(self, recv, lp)
		end

		var recv_class = n_expr.mtype.get_mclass(vm).as(not null)

		var gp = node_ast.as(AAttrPropdef).mpropdef.mproperty

		recv_class.set_site_pattern(moattr, recv_class.mclass_type, gp)
		lp.mosites.add(moattr)
	end

	# Real methods calls, and accessors with multiples LPs
	fun compile_ast_method(vm: VirtualMachine, lp: MMethodDef, recv: MOExpr, node_ast: ANode, is_attribute: Bool)
	do
		var cs = callsite.as(not null)

		# Null cases are already eliminated, to get_mclass can't return null
		var recv_class = cs.recv.get_mclass(vm).as(not null)

		# If recv_class was a formal type, and now resolved as in primitive, we ignore it
		if not recv_class.mclass_type.is_primitive_type  then
			mocallsite = new MOCallSite(self, recv, lp)
			var mocs = mocallsite.as(not null)

			lp.mosites.add(mocs)
			recv_class.set_site_pattern(mocs, recv_class.mclass_type, cs.mproperty)

			# Expressions arguments given to the method called
			for arg in raw_arguments do
				var moexpr = arg.ast2mo
				if moexpr != null then mocallsite.given_args.add(moexpr)
			end
		end
	end
end

redef class AParExpr
	redef fun ast2mo do return n_expr.ast2mo
end

redef class ANotExpr
	redef fun ast2mo do return n_expr.ast2mo
end
