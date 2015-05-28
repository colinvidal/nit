# This file is part of NIT ( http://www.nitlanguage.org ).
#
# Copyright 2015 Julien Pagès <julien.pages@lirmm.fr>
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Optimization of the nitvm, compute implementations
module vm_optimizations

import preexistence

redef class VirtualMachine
	# Add optimization of the method dispatch
	redef fun callsite(callsite: nullable CallSite, arguments: Array[Instance]): nullable Instance
	do
		var initializers = callsite.mpropdef.initializers
		if initializers.is_empty then return send_optimize(callsite.as(not null), arguments)

		var recv = arguments.first
		var i = 1
		for p in initializers do
			if p isa MMethod then
				var args = [recv]
				for x in p.intro.msignature.mparameters do
					args.add arguments[i]
					i += 1
				end
				self.send(p, args)
			else if p isa MAttribute then
				assert recv isa MutableInstance
				write_attribute(p, recv, arguments[i])
				i += 1
			else abort
		end
		assert i == arguments.length

		return send_optimize(callsite.as(not null), [recv])
	end

	# Try to have the most efficient implementation of the method dispatch
	fun send_optimize(callsite: CallSite, args: Array[Instance]): nullable Instance
	do
		var recv = args.first
		var mtype = recv.mtype
		var ret = send_commons(callsite.mproperty, args, mtype)
		if ret != null then return ret

		if callsite.status == 0 then callsite.optimize(recv)

		var propdef
		if callsite.status == 1 then
			propdef = method_dispatch_sst(recv.vtable.internal_vtable, callsite.offset)
		else
			propdef = method_dispatch_ph(recv.vtable.internal_vtable, recv.vtable.mask,
				callsite.id, callsite.offset)
		end

		#TODO : we need recompilations here
		callsite.status = 0
		return self.call(propdef, args)
	end
end

redef class AAttrFormExpr
	super AToCompile

	# Position of the attribute in attribute table
	#
	# The relative position of this attribute if perfect hashing is used,
	# The absolute position of this attribute if SST is used
	var offset: Int

	# Indicate the status of the optimization for this node
	#
	# 0: default value
	# 1: SST (direct access) can be used
	# 2: PH (multiple inheritance implementation) must be used
	var status: Int = 0

	# Identifier of the class which introduced the attribute
	var id: Int

	# Link to the attribute access in MO
	var moattrsite: nullable MOAttrSite

	# Optimize this attribute access
	# * `mproperty` The attribute which is accessed
	# * `recv` The receiver (The object) of the access
	protected fun optimize(mproperty: MAttribute, recv: MutableInstance)
	do
		var position = recv.mtype.as(MClassType).mclass.get_position_attributes(mproperty.intro_mclassdef.mclass)
		if position > 0 then
			# if this attribute class has an unique position for this receiver, then use direct access
			offset = position + mproperty.offset
			status = 1
		else
			# Otherwise, perfect hashing must be used
			id = mproperty.intro_mclassdef.mclass.vtable.id
			offset = mproperty.offset
			status = 2
		end
	end

	# Compile this attribute access from ast to mo
	redef fun compile_ast(vm: VirtualMachine, lp: MMethodDef)
	do
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
			moattrsite = make_mo(vm, recv, lp)
			lp.mosites.add(moattrsite.as(not null))	
		end
	end

	# Make the MO node / pattern
	private fun make_mo(vm: VirtualMachine, recv: MOExpr, lp:MMethodDef): MOAttrSite is abstract
end

redef class AAttrExpr
	redef fun expr(v)
	do
		# TODO : a workaround for now
		if not v isa VirtualMachine then return super

		var recv = v.expr(self.n_expr)
		if recv == null then return null
		if recv.mtype isa MNullType then fatal(v, "Receiver is null")
		var mproperty = self.mproperty.as(not null)

		assert recv isa MutableInstance
		if status == 0 then optimize(mproperty, recv)

		var i: Instance
		if status == 1 then
			# SST
			i = v.read_attribute_sst(recv.internal_attributes, offset)
		else
			# PH
			i = v.read_attribute_ph(recv.internal_attributes, recv.vtable.internal_vtable, recv.vtable.mask, id, offset)
		end

		# If we get a `MInit` value, throw an error
		if i == v.initialization_value then
			v.fatal("Uninitialized attribute {mproperty.name}")
			abort
		end

		#TODO : we need recompilations here
		status = 0

		return i
	end

	redef fun ast2mo do return moattrsite.as(nullable MOReadSite)

	redef fun make_mo(vm, recv, lp)
	do
		var moattr = new MOReadSite(recv, lp)
		var recv_class = n_expr.mtype.get_mclass(vm).as(not null)
		recv_class.set_site_pattern(moattr, recv_class.mclass_type, mproperty.as(not null))
		return moattr
	end

	redef fun generate_basicBlocks(vm, old_block)
	do
		var ret = super(vm, old_block)
		vm.current_propdef.as(AMethPropdef).to_compile.add(self)
		return ret
	end
end

redef class AAttrAssignExpr
	redef fun stmt(v)
	do
		# TODO : a workaround for now
		if not v isa VirtualMachine then
			super
			return
		end

		var recv = v.expr(self.n_expr)
		if recv == null then return
		if recv.mtype isa MNullType then fatal(v, "Receiver is null")
		var i = v.expr(self.n_value)
		if i == null then return
		var mproperty = self.mproperty.as(not null)

		assert recv isa MutableInstance
		if status == 0 then optimize(mproperty, recv)

		if status == 1 then
			v.write_attribute_sst(recv.internal_attributes, offset, i)
		else
			v.write_attribute_ph(recv.internal_attributes, recv.vtable.internal_vtable,
					recv.vtable.mask, id, offset, i)
		end

		#TODO : we need recompilations here
		status = 0
	end

	redef fun make_mo(vm, recv, lp)
	do
		var moattr = new MOWriteSite(recv, lp)
		var recv_class = n_expr.mtype.get_mclass(vm).as(not null)
		recv_class.set_site_pattern(moattr, recv_class.mclass_type, mproperty.as(not null))
		return moattr
	end

	redef fun generate_basicBlocks(vm, old_block)
	do
		var ret = super(vm, old_block)
		vm.current_propdef.as(AMethPropdef).to_compile.add(self)
		return ret
	end
end

# Add informations to optimize some method calls
redef class CallSite
	# Position of the method in virtual table
	#
	# The relative position of this MMethod if perfect hashing is used,
	# The absolute position of this MMethod if SST is used
	var offset: Int

	# Indicate the status of the optimization for this node
	#
	# 0: default value
	# 1: SST (direct access) can be used
	# 2: PH (multiple inheritance implementation) must be used
	var status: Int = 0

	# Identifier of the class which introduced the MMethod
	var id: Int

	# Optimize a method dispatch,
	# If this method is always at the same position in virtual table, we can use direct access,
	# Otherwise we must use perfect hashing
	fun optimize(recv: Instance)
	do
		var position = recv.mtype.as(MClassType).mclass.get_position_methods(mproperty.intro_mclassdef.mclass)
		#print "Call to {recv.mtype.as(MClassType).mclass}.{mproperty} => position unique = {position}"
		if position > 0 then
			offset = position + mproperty.offset
			status = 1
		else
			offset = mproperty.offset
			status = 2
		end
		id = mproperty.intro_mclassdef.mclass.vtable.id
	end
end

redef class AIsaExpr
	super AToCompile

	# Identifier of the target class type
	var id: Int

	# If the Cohen test is used, the position of the target id in vtable
	var position: Int

	# Indicate the status of the optimization for this node
	#
	# 0 : the default value
	# 1 : this test can be implemented with direct access
	# 2 : this test must be implemented with perfect hashing
	var status: Int = 0

	redef fun expr(v)
	do
		# TODO : a workaround for now
		if not v isa VirtualMachine then return super

		var recv = v.expr(self.n_expr)
		if recv == null then return null

		if status == 0 then optimize(v, recv.mtype, self.cast_type.as(not null))
		var mtype = v.unanchor_type(self.cast_type.as(not null))

		# If this test can be optimized, directly call appropriate subtyping methods
		if status == 1 and recv.mtype isa MClassType then
			# Direct access
			return v.bool_instance(v.inter_is_subtype_sst(id, position, recv.mtype.as(MClassType).mclass.vtable.internal_vtable))
		else if status == 2 and recv.mtype isa MClassType then
			# Perfect hashing
			return v.bool_instance(v.inter_is_subtype_ph(id, recv.vtable.mask, recv.mtype.as(MClassType).mclass.vtable.internal_vtable))
		else
			# Use the slow path (default)
			return v.bool_instance(v.is_subtype(recv.mtype, mtype))
		end
	end

	# Optimize a `AIsaExpr`
	# `source` the source type of the expression
	# `target` the target type of the subtyping test
	private fun optimize(v: VirtualMachine, source: MType, target: MType)
	do
		# If the source class and target class are not classic classes (non-generics) then return
		if not source isa MClassType or not target isa MClassType or target isa MGenericType then
			return
		end

		if not target.mclass.loaded then return

		#TODO
		# Try to get the position of the target type in source's structures
		var value = source.mclass.positions_methods.get_or_null(target.mclass)

		# if value != null then
		# 	if value != -1 then
		# 		# Store informations for Cohen test
		# 		position = target.mclass.color
		# 		status = 1
		# 	else
				# We use perfect hashing
				status = 2
		# 	end
		# end
		id = target.mclass.vtable.id
	end

	redef fun generate_basicBlocks(vm, old_block)
	do
		var ret = super(vm, old_block)
		vm.current_propdef.as(AMethPropdef).to_compile.add(self)
		return ret
	end
	
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
			var most = new MOSubtypeSite(recv, lp, cast_type.as(not null))
			var recv_class = n_expr.mtype.get_mclass(vm).as(not null)
			recv_class.set_subtype_pattern(most, recv_class.mclass_type)
			lp.mosites.add(most)
		end
	end
end

redef class AAsCastExpr
	super AToCompile

	# Identifier of the target class type
	var id: Int

	# If the Cohen test is used, the position of the target id in vtable
	var position: Int

	# Indicate the status of the optimization for this node
	#
	# 0 : the default value
	# 1 : this test can be implemented with direct access
	# 2 : this test must be implemented with perfect hashing
	var status: Int = 0

	redef fun expr(v)
	do
		# TODO : a workaround for now
		if not v isa VirtualMachine then return super

		var recv = v.expr(self.n_expr)
		if recv == null then return null

		if status == 0 then optimize(v, recv.mtype, self.mtype.as(not null))

		var mtype = self.mtype.as(not null)
		var amtype = v.unanchor_type(mtype)

		var res: Bool
		if status == 1 and recv.mtype isa MClassType then
			# Direct access
			res = v.inter_is_subtype_sst(id, position, recv.mtype.as(MClassType).mclass.vtable.internal_vtable)
		else if status == 2 and recv.mtype isa MClassType then
			# Perfect hashing
			res = v.inter_is_subtype_ph(id, recv.vtable.mask, recv.mtype.as(MClassType).mclass.vtable.internal_vtable)
		else
			# Use the slow path (default)
			res = v.is_subtype(recv.mtype, amtype)
		end

		if not res then
			fatal(v, "Cast failed. Expected `{amtype}`, got `{recv.mtype}`")
		end
		return recv
	end

	# Optimize a `AAsCastExpr`
	# * `source` the source type of the expression
	# * `target` the target type of the subtyping test
	private fun optimize(v: VirtualMachine, source: MType, target: MType)
	do
		# If the source class and target class are not classic classes (non-generics) then return
		if not source isa MClassType or not target isa MClassType or target isa MGenericType then
			return
		end

		if not target.mclass.loaded then return

		# Try to get the position of the target type in source's structures
		var value = source.mclass.positions_methods.get_or_null(target.mclass)

		#TODO
		# if value != null then
		# 	if value != -1 then
		# 		# Store informations for Cohen test
		# 		position = target.mclass.color
		# 		status = 1
		# 	else
				# We use perfect hashing
				status = 2
		# 	end
		# end
		id = target.mclass.vtable.id
	end
	
	redef fun generate_basicBlocks(vm, old_block)
	do
		var ret = super(vm, old_block)
		vm.current_propdef.as(AMethPropdef).to_compile.add(self)
		return ret
	end

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
			var moattr = new MOSubtypeSite(recv, lp, n_type.mtype.as(not null))
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
				movar = new MOParam(0)
			else if node isa AVarExpr then
				# A variable read
				if node.variable.parameter then
					movar = new MOParam(node.variable.position)
				else if node.variable.dep_exprs.length == 1 then
					var mo = node.variable.dep_exprs.first.ast2mo
					if mo != null then movar = new MOSSAVar(node.variable.position, mo)
				else if node.variable.dep_exprs.length > 1 then
					var phi = new List[MOExpr]
					for a_expr in node.variable.dep_exprs do 
						var mo = a_expr.ast2mo
						if mo != null then phi.add(mo)
					end

					if phi.length == 1 then
						movar = new MOSSAVar(node.variable.position, phi.first)
					else if phi.length > 1 then
						movar = new MOPhiVar(node.variable.position, phi)
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

	redef fun generate_basicBlocks(vm, old_block)
	do
		var sup = super(vm, old_block)

		# Int, String, and Number are abstract, so we can't instantiate them with "new" keyword.
		# Is there others primitives types we can do a "new" on it ? If not, remove this test.
		if not recvtype.is_primitive_type then
			monew = new MONew(vm.current_propdef.mpropdef.as(MMethodDef))
			vm.current_propdef.mpropdef.as(MMethodDef).monews.add(monew.as(not null))
			recvtype.mclass.set_new_pattern(monew.as(not null))
		end

		return sup
	end

	redef fun ast2mo do return monew
end

redef class ANode
	# True if self is a primitive node
	fun is_primitive_node: Bool
	do
		if self isa AIntExpr then return true
		if self isa ACharExpr then return true
		if self isa ANullExpr then return true
		if self isa AStringFormExpr then return true
		if self isa ATrueExpr then return true
		if self isa AFalseExpr then return true
		if self isa ASuperstringExpr then return true
		return false
	end

	# Convert AST node into MOExpression
	fun ast2mo: nullable MOExpr
	do
		if not is_primitive_node then trace("WARN: NYI {self}")
		return null
	end
end

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

# Common call to all AST node that must be compiled into MO node
class AToCompile
	# Compile the AST to into a MO node
	fun compile_ast(vm: VirtualMachine, lp: MMethodDef) is abstract
end

redef class AMethPropdef
	# list of return expression of the optimizing model
	# Null if this fuction is a procedure
	var mo_dep_exprs: nullable MOVar = null

	# List of ast node to compile
	var to_compile = new List[AToCompile]

	redef fun generate_basicBlocks(vm)
	do
		super(vm)

		# Generate MO for return of the propdef
		if returnvar.dep_exprs.length == 1 then
			var moexpr = returnvar.dep_exprs.first.ast2mo
			if moexpr != null then mo_dep_exprs = new MOSSAVar(returnvar.position, moexpr)
		else if returnvar.dep_exprs.length > 1 then
			var deps = new List[MOExpr]
			for a_expr in returnvar.dep_exprs do
				var moexpr = a_expr.ast2mo
				if moexpr != null then deps.add(moexpr)
			end

			if deps.length == 1 then
				mo_dep_exprs = new MOSSAVar(returnvar.position, deps.first)
			else if deps.length > 1 then
				mo_dep_exprs = new MOPhiVar(returnvar.position, deps)
			end
		end

		mpropdef.as(not null).return_expr = mo_dep_exprs

		# Generate MO for sites inside the propdef
		for expr in to_compile do expr.compile_ast(vm, mpropdef.as(not null))
	end
end

redef class ASendExpr
	super AToCompile

	# Site invocation associated with this node
	var mocallsite: nullable MOCallSite
	
	redef fun generate_basicBlocks(vm, old_block)
	do
		var sup = super(vm, old_block)
		vm.current_propdef.as(AMethPropdef).to_compile.add(self)
		return sup
	end

	redef fun ast2mo
	do
		return mocallsite
	end

	# Compile this ast node in MOCallSite after SSA
	redef fun compile_ast(vm: VirtualMachine, lp: MMethodDef)
	do
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
			moattr = new MOReadSite(recv, lp)
		else
			# The node is a MOWriteSite
			assert params_len == 1
			moattr = new MOWriteSite(recv, lp)
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
			mocallsite = new MOCallSite(recv, lp)
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

redef abstract class MOSitePattern
	# Implementation of the pattern (used if site as not concerte receivers list)
	var impl: nullable Implementation is noinit

	# Get implementation, compute it if not exists
	fun get_impl(vm: VirtualMachine): Implementation
	do
		if impl == null then compute_impl(vm)
		return impl.as(not null)
	end

	# Compute the implementation
	private fun compute_impl(vm: VirtualMachine) is abstract
end

redef class MOSubtypeSitePattern
	redef fun compute_impl(vm)
	do 
		if not rst.get_mclass(vm).loaded then
			impl = new PHImpl(false, target.get_mclass(vm).color)
			return
		end

		var pos_cls = rst.get_mclass(vm).get_position_methods(target.get_mclass(vm).as(not null))
		
		if pos_cls > 0 then
			impl = new SSTImpl(true, pos_cls)
		else
			impl = new PHImpl(false, target.get_mclass(vm).color)
		end
	end
end

redef abstract class MOPropSitePattern
	redef fun add_lp(lp: LP)
	do
		var reset = not lps.has(lp)

		super(lp)
		if reset then 
			if impl != null and impl.is_mutable then impl = null
			for site in sites do
				if site.impl != null and site.impl.is_mutable then site.impl = null
			end
		end
	end
end

redef class MOCallSitePattern
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

redef abstract class MOAttrPattern
	redef fun compute_impl(vm)
	do
		if not rst.get_mclass(vm).loaded then
			impl = new PHImpl(false, gp.offset)
			return
		end

		var pos_cls = rst.get_mclass(vm).get_position_attributes(gp.intro_mclassdef.mclass)

		if gp.intro_mclassdef.mclass.is_instance_of_object(vm) then
			impl = new SSTImpl(false, pos_cls + gp.offset)
		else if pos_cls > 0 then
			impl = new SSTImpl(true, pos_cls + gp.offset)
		else
			impl = new PHImpl(false, gp.offset) 
		end
	end
end

redef abstract class MOSite
	# Implementation of the site (null if can't determine concretes receivers)
	var impl: nullable Implementation is noinit

	# Get the implementation of the site
	fun get_impl(vm: VirtualMachine): Implementation is abstract
	
	# Compute the implementation with rst/pic
	private fun compute_impl(vm: VirtualMachine) is abstract
end

redef class MOSubtypeSite
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
		if get_concretes.length == 0 then
			var candidate_impl = pattern.get_impl(vm)

			if not expr_recv.is_pre then
				assert not candidate_impl isa StaticImplProp

				if candidate_impl isa SSTImpl or candidate_impl isa StaticImplSubtype then
					impl = new PHImpl(false, target.get_mclass(vm).color)
					candidate_impl = impl.as(not null)
				end
			end

			return candidate_impl
		else
			# We don't case of the preexistence here
			compute_impl(vm)
			return impl.as(not null)
		end
	end
end

redef abstract class MOAttrSite
	redef fun compute_impl(vm)
	do
		var gp = pattern.gp

		if not pattern.rst.get_mclass(vm).loaded then
			# The PHImpl here is mutable because it can be switch to a 
			# lightweight implementation when the class will be loaded
			impl = new PHImpl(false, gp.offset)
			return
		end

		var pos_cls = pattern.rst.get_mclass(vm).get_position_attributes(gp.intro_mclassdef.mclass)

		if gp.intro_mclassdef.mclass.is_instance_of_object(vm) then
			impl = new SSTImpl(false, pos_cls + gp.offset)
		else if unique_pos_concrete_recv then
			# SST immutable because it can't be more than these concretes receivers statically
			# We don't check if there is one or more concrete type, because we can't make a static dispatch
			# on attribute
			impl = new SSTImpl(false, pos_cls + gp.offset)
		else
			impl = new PHImpl(false, gp.offset) 
		end
	end

	# Each concrete receiver has unique attribute position
	private fun unique_pos_concrete_recv: Bool
	do
		var gp = pattern.gp

		for recv in get_concretes do
			if not recv.loaded then return false
			if recv.get_position_attributes(gp.intro_mclassdef.mclass) < 0 then return false
		end

		return true
	end

	redef fun get_impl(vm)
	do
		if get_concretes.length == 0 then
			var candidate_impl = pattern.get_impl(vm)

			if not expr_recv.is_pre then
				assert not candidate_impl isa StaticImplProp

				if candidate_impl isa SSTImpl then
					impl = new PHImpl(false, pattern.gp.offset)
					candidate_impl = impl.as(not null)
				end
			end

			return candidate_impl
		else
			# We don't care the preeeixstence of the site here
			if impl == null then compute_impl(vm)
			return impl.as(not null)
		end
	end


end

redef class MOCallSite
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
			impl = new StaticImplProp(false,
			vm.method_dispatch_ph(cls.vtable.internal_vtable,
			cls.vtable.mask,
			gp.intro_mclassdef.mclass.vtable.id, 
			gp.offset))
		else if unique_pos_concrete_recv then
			# SST immutable because it can't be more than these concretes receivers statically
			impl = new SSTImpl(false, pos_cls + gp.offset)
		else
			impl = new PHImpl(false, gp.offset) 
		end
	end
	
	# Each concrete receiver has unique method position
	private fun unique_pos_concrete_recv: Bool
	do
		var gp = pattern.gp

		for recv in get_concretes do
			if not recv.loaded then return false
			if recv.get_position_methods(gp.intro_mclassdef.mclass) < 0 then return false
		end

		return true
	end

	redef fun get_impl(vm)
	do
		if get_concretes.length == 0 then
			var candidate_impl = pattern.get_impl(vm)

			if not expr_recv.is_pre then
				var gp = pattern.gp
				var pos_cls = pattern.rst.get_mclass(vm).get_position_methods(gp.intro_mclassdef.mclass)
				
				if candidate_impl isa StaticImplProp then
					if pos_cls > 0 then
						impl = new SSTImpl(true, gp.offset + pos_cls)
					else
						impl = new PHImpl(false, gp.offset)
					end
					candidate_impl = impl.as(not null)
				else if candidate_impl isa SSTImpl and pos_cls <= 0 then
					impl = new PHImpl(false, gp.offset)
					candidate_impl = impl.as(not null)
				end
			end
			
			return candidate_impl
		else
			# We don't care the preeeixstence of the site here
			if impl == null then compute_impl(vm)
			return impl.as(not null)
		end
	end


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
