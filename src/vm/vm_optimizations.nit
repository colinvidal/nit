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

# Optimization of the nitvm
module vm_optimizations

import virtual_machine
import ssa
import model_optimizations

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

		mclass.handle_new_class
	end

	redef fun new_frame(node, mpropdef, args)
	do
		next_receivers.push(args.first.mtype)
#		trace("NEXT_RECEIVERS: {next_receivers}")
		var ret = super(node, mpropdef, args)
		if mpropdef isa MMethodDef then	mpropdef.preexist_all(self)
		next_receivers.pop
		return ret
	end

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
			pstats.inc("lits")
		else if n_expr.mtype.is_primitive_type then
			# Ignore primitives cases of the analysis
			ignore = true
			pstats.inc("primitive_sites")
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

		optimize(v, recv.mtype, self.cast_type.as(not null))
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

		if not target.mclass.abstract_loaded then return

		# If the value is positive, the target class has an invariant position in source's structures
		var value = source.mclass.get_position_methods(target.mclass)

		if value > 0 then
			# `value - 2` is the position of the target identifier in source vtable
			position = value - 2
			status = 1
		else
			# We use perfect hashing
			status = 2
		end
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
			pstats.inc("lits")
		else if n_expr.mtype.get_mclass(vm).mclass_type.is_primitive_type then
			# Ignore primitives cases of the analysis
			ignore = true
			pstats.inc("primitive_sites")
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

		optimize(v, recv.mtype, self.mtype.as(not null))

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

		# If the value is positive, the target class has an invariant position in source's structures
		var value = source.mclass.get_position_methods(target.mclass)

		if value > 0 then
			# `value - 2` is the position of the target identifier in source vtable
			position = value - 2
			status = 1
		else
			# We use perfect hashing
			status = 2
		end
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
			pstats.inc("lits")
		else if n_expr.mtype.is_primitive_type then
			# Ignore primitives cases of the analysis
			ignore = true
			pstats.inc("primitive_sites")
		else if n_type.mtype.get_mclass(vm).mclass_type.is_primitive_type then
			ignore = true
			pstats.inc("primitive_sites")
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
			pstats.inc("ast_new")
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
		if is_primitive_node then
			sys.pstats.inc("primitive_sites")
		else
			sys.pstats.inc("nyi")
			trace("WARN: NYI {self}")
		end

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
			pstats.inc("lits")
		else if n_expr.mtype.is_primitive_type then
			# Ignore primitives cases of the analysis
			ignore = true
			pstats.inc("primitive_sites")
		end

		var recv = n_expr.ast2mo

		if recv != null and not ignore then
			var cs = callsite.as(not null)

			# Static dispatch to know if the local property is an accessor
			var impl_node = vm.modelbuilder.mpropdef2node(cs.mpropdef)
			if impl_node isa AAttrPropdef then
				var params_len = cs.msignature.mparameters.length
				var moattr: MOAttrSite

				if params_len == 0 then
					# The node is a MOReadSite
					moattr = new MOReadSite(recv, lp)
				else
					# The node is a MOWriteSite
					assert params_len == 1
					moattr = new MOWriteSite(recv, lp)
				end

				var recv_class = n_expr.mtype.get_mclass(vm).as(not null)
				recv_class.set_site_pattern(moattr, recv_class.mclass_type, cs.mproperty)
				lp.mosites.add(moattr)	
			else
				# Here, we are sure that the property of the callsite is a real method call

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
	end
end

redef class AParExpr
	redef fun ast2mo do return n_expr.ast2mo
end

redef class ANotExpr
	redef fun ast2mo do return n_expr.ast2mo
end

redef class ABinopExpr
	# If a binary operation on primitives types return something (or test of equality), it's primitive
	# TODO: what about obj1 + obj2 ?
	redef fun ast2mo do
		pstats.inc("primitive_sites")
		return null
	end
end

redef class Int
	# Display 8 lower bits of preexitence value
	fun preexists_bits: Array[Int]
	do
		var bs = bits.reversed
		for i in [0..23] do bs.shift
		return bs
	end
end

redef class MPropDef
	# List of mutable preexists expressions
	var exprs_preexist_mut = new List[MOExpr]

	# List of mutable non preexists expressions
	var exprs_npreexist_mut = new List[MOExpr]

	# Drop exprs_preesit_mut and set unknown state to all expression inside
	# If the return_expr is in it, recurse on callers
	fun propage_preexist
	do
		var flag = false
		if self isa MMethodDef then
			if return_expr != null then flag = return_expr.is_pre_nper
		end

		for expr in exprs_preexist_mut do expr.init_preexist
		exprs_preexist_mut.clear

		if flag then for p in callers do p.as(MOExprSitePattern).propage_preexist
	end

	# Drop exprs_npreesit_mut and set unknown state to all expression inside
	# If the return_expr is in it, recurse on callers
	fun propage_npreexist
	do
		var flag = false
		if self isa MMethodDef then
			if return_expr != null then flag = return_expr.is_npre_nper
		end

		for expr in exprs_npreexist_mut do expr.init_preexist
		exprs_npreexist_mut.clear

		if flag then for p in callers do p.as(MOExprSitePattern).propage_npreexist
	end

	# Fill the correct list if the analysed preexistence if unperennial
	fun fill_nper(expr: MOExpr)
	do
		if expr.is_nper then
			if expr.is_pre then
				if not exprs_preexist_mut.has(expr) then exprs_preexist_mut.add(expr)
			else
				if not exprs_npreexist_mut.has(expr) then exprs_npreexist_mut.add(expr)
			end
		end
	end
end

redef class MMethodDef
	# Compute the preexistence of the return of the method expression
	fun preexist_return: Int
	do
		if not compiled then
			return_expr.set_npre_nper
			return return_expr.preexist_expr_value
		else if not return_expr.is_pre_unknown then
			return return_expr.preexist_expr_value
		else
			return_expr.set_recursive
			return return_expr.preexist_expr_value
		end
	end

	# Compute the preexistence of all invocation sites and return site of the method
	#
	# WARNING!
	# The VM can't interpret FFI code, so intern/extern methods are not analysed,
	# and a expression using a receiver from intern/extern method is preexistent.
	#
	fun preexist_all(vm: VirtualMachine)
	do
		if compiled or is_intern or is_extern then return
		compiled = true

		trace("\npreexist_all of {self}")
		var preexist: Int

		if not disable_preexistence_extensions then
			if return_expr != null then
				return_expr.preexist_expr
				if return_expr.is_rec then return_expr.set_pval_nper
				fill_nper(return_expr.as(not null))
				preexist = return_expr.preexist_expr_value
				trace("\tpreexist of return : {return_expr.as(not null)} {preexist} {preexist.preexists_bits}")
			end

			for newexpr in monews do
				assert not newexpr.pattern.cls.mclass_type.is_primitive_type

				preexist = newexpr.preexist_expr
				fill_nper(newexpr)
				trace("\tpreexist of new {newexpr} loaded:{newexpr.pattern.is_loaded} {preexist} {preexist.preexists_bits}")
			end
		end

		for site in mosites do
			assert not site.pattern.rst.is_primitive_type

			if site.expr_recv.is_from_monew then pstats.inc("sites_from_new")
			if site.expr_recv.is_from_mocallsite then pstats.inc("sites_from_meth_return")
			if site.expr_recv.is_from_monew or site.expr_recv.is_from_mocallsite then pstats.inc("sites_handle_by_extend_preexist")

			preexist = site.preexist_site
			var is_pre = site.expr_recv.is_pre
			var impl = site.get_impl(vm)

			var buff = "\tpreexist of "

			if site isa MOSubtypeSite then
			else
			end

			fill_nper(site.expr_recv)

			if site.expr_recv.is_pre then
				pstats.inc("preexist")
				if site.get_impl(vm) isa StaticImpl then pstats.inc("preexist_static")
			else
				pstats.inc("npreexist")
			end

			# attr_*
			if site isa MOAttrSite then
				buff += "attr {site.pattern.rst}.{site.pattern.gp}" 

				if site.expr_recv isa MOParam then 
					if site.expr_recv.as(MOParam).offset == 0 then pstats.inc("attr_self")
				end

				if impl isa SSTImpl then
					incr_specific_counters(is_pre, "attr_preexist_sst", "attr_npreexist_sst")
					pstats.inc("impl_sst")
				else if impl isa PHImpl then 
					pstats.inc("attr_ph")
					pstats.inc("impl_ph")
				else 
					# Specific case of the accessors statics
					pstats.inc("attr_accessors")
					incr_specific_counters(is_pre, "attr_preexist_accessors", "attr_npreexist_accessors")
				end

				if site isa MOReadSite then
					pstats.inc("attr_read")
				else
					pstats.inc("attr_write")
				end

				pstats.inc("attr")
				incr_specific_counters(is_pre, "attr_preexist", "attr_npreexist")
			end

			# cast_*
			if site isa MOSubtypeSite then
				buff += "cast {site.pattern.rst} isa {site.target}"
				
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
			end

			# meth_*
			if site isa MOCallSite then
				buff += "meth {site.pattern.rst}.{site.pattern.gp}" 
				
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
			end

			buff += " {site.expr_recv}.{site} {preexist} {preexist.preexists_bits}"
			trace(buff)

			# concretes_receivers_sites
			if site.get_concretes.length > 0 then pstats.inc("concretes_receivers_sites")
		
			trace("\t\tconcretes receivers? {(site.get_concretes.length > 0)}")
			trace("\t\t{impl} {impl.is_mutable}")
		end

		if exprs_preexist_mut.length > 0 then trace("\tmutables pre: {exprs_preexist_mut}")
		if exprs_npreexist_mut.length > 0 then trace("\tmutables nper: {exprs_npreexist_mut}")
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

# Preexistence masks
# PVAL_PER:	0...1111
# PTYPE_PER:	0...1101
# PVAL_NPER:	0...1011
# PTYPE_NPER:	0...1001
# NPRE_PER:	0...1100
# NPRE_NPER:	0...1000
# RECURSIV:	0...0000
# PRE_PER:	0...0101
# PRE_NPER:	0...0001
# UNKNOWN:	1...

# Preexistence mask of perennial value preexistence
fun pmask_PVAL_PER: Int do return 15

# Preexistence mask of perennial type preexistence
fun pmask_PTYPE_PER: Int do return 13

# Preexistence mask of no perennial value preexistence
fun pmask_PVAL_NPER: Int do return 11

# Preexistence mask of no perennial type preexistence
fun pmask_PTYPE_NPER: Int do return 9

# Preexistence mask of perennial no preexistence
fun pmask_NPRE_PER: Int do return 12

# Preexistence mask of no perennial no preexistence
fun pmask_NPRE_NPER: Int do return 8

# Preexistence mask of recursive calls
fun pmask_RECURSIV: Int do return 0

# Preexistence mask of unknown preexistence
fun pmask_UNKNOWN: Int do return -1

redef class MOExpr
	# The cached preexistence of the expression (the return of the expression)
	var preexist_expr_value: Int = pmask_UNKNOWN

	# Compute the preexistence of the expression
	fun preexist_expr: Int is abstract

	# Set a bit in a dependency range on the given offset to a preexistence state
	# Shift 4 bits (preexistence status) + the offset of dependency, and set bit to 1
	fun set_dependency_flag(offset: Int): Int
	do
		preexist_expr_value = preexist_expr_value.bin_or(1.lshift(4 + offset))
		return preexist_expr_value
	end

	# True if the expression depends of the preexistence of a dependencie at `index`
	fun is_dependency_flag(index: Int): Bool
	do
		# It must concern a dependency bit
		index += 5

		return 1.lshift(index).bin_and(preexist_expr_value) != 0
	end

	# Affect status mask
	private fun set_status_mask(mask: Int)
	do
		if is_pre_unknown or is_rec then preexist_expr_value = 0
		preexist_expr_value = preexist_expr_value.rshift(4).lshift(4).bin_or(mask)
	end

	# Set type preexist perennial
	fun set_ptype_per do set_status_mask(pmask_PTYPE_PER)

	# Set value preexist perennial
	fun set_pval_per do set_status_mask(pmask_PVAL_PER)

	# Set non preexist non perennial
	fun set_npre_nper do set_status_mask(pmask_NPRE_NPER)

	# Set non preexist perennial
	fun set_npre_per do preexist_expr_value = pmask_NPRE_PER

	# Set val preexist non perennial
	fun set_pval_nper do set_status_mask(pmask_PVAL_NPER)

	# Set recursive flag
	fun set_recursive do preexist_expr_value = pmask_RECURSIV

	# Return true if the preexistence of the expression isn't known
	fun is_pre_unknown: Bool do return preexist_expr_value == pmask_UNKNOWN

	# Return true if the expression is recursive
	fun is_rec: Bool do return preexist_expr_value == 0

	# Return true if the expression preexists (recursive case is interpreted as preexistent)
	fun is_pre: Bool do return preexist_expr_value.bin_and(1) == 1 or preexist_expr_value == 0

	# True true if the expression non preexists
	fun is_npre: Bool do return not is_pre

	# Return true if the preexistence state of the expression is perennial
	fun is_per: Bool do return preexist_expr_value.bin_and(4) == 4

	# Return true if the preexistence state if not perennial
	fun is_nper: Bool do return not is_per

	# Return true if the prexistence state is preexist and no perennial
	fun is_pre_nper: Bool do return is_pre and is_nper

	# Return true if the preexistence state is no preexist and no perennial
	fun is_npre_nper: Bool do return is_npre and is_nper

	# Return true if the preexistence state is no preexist and perennial
	fun is_npre_per: Bool do return is_npre and is_per

	# Initialize preexist_cache to UNKNOWN
	fun init_preexist do preexist_expr_value = pmask_UNKNOWN

	# Merge dependecies and preexistence state
	fun merge_preexistence(expr: MOExpr): Int
	do
		if expr.is_npre_per then
			set_npre_per
		else if expr.is_rec then
			set_recursive
		else
			var pre = preexist_expr_value.bin_and(15)
			var deps = preexist_expr_value.rshift(4).lshift(4)

			pre = pre.bin_and(expr.preexist_expr_value.bin_and(15))
			deps = deps.bin_or(expr.preexist_expr_value.rshift(4).lshift(4))

			preexist_expr_value = pre.bin_or(deps)
		end

		return preexist_expr_value
	end
end

redef class MOLit
	redef var preexist_expr_value = pmask_PVAL_PER

	redef fun init_preexist do end 

	redef fun preexist_expr do return preexist_expr_value
end

redef class MOParam
	redef var preexist_expr_value = pmask_PVAL_PER

	init do set_dependency_flag(offset)

	redef fun init_preexist do end 

	redef fun preexist_expr do return preexist_expr_value
end

redef class MONew
	redef fun init_preexist do
		if disable_preexistence_extensions then
			set_npre_per
		else if pattern.is_loaded then
			set_ptype_per
		else
			set_npre_nper
		end
	end

	redef fun preexist_expr do 
		if is_pre_unknown then init_preexist
		return preexist_expr_value
	end
end

redef class MOSSAVar
	redef fun preexist_expr
	do
		if is_pre_unknown then preexist_expr_value = dependency.preexist_expr
		return preexist_expr_value
	end
end

redef class MOPhiVar
	redef fun preexist_expr
	do
		if is_pre_unknown then
			preexist_expr_value = pmask_PVAL_PER
			for dep in dependencies do
				dep.preexist_expr
				merge_preexistence(dep)
				if is_npre_per then
					break
				end
			end
		end

		return preexist_expr_value
	end
end


redef class MOReadSite
	redef fun preexist_expr
	do
		if is_pre_unknown then
			expr_recv.preexist_expr
			if immutable and expr_recv.is_pre then
				set_pval_per
			else
				if expr_recv.is_pre then
					if expr_recv.is_per then
						set_pval_per
					else
						set_pval_nper
					end

					# The receiver is always at position 0 of the environment
					set_dependency_flag(0)
				else
					if expr_recv.is_per then
						set_npre_per
					else
						set_npre_nper
					end
				end
			end
		end

		return preexist_expr_value
	end
end

redef class MOCallSite
	# If the receiver expression of `self` depends of the preexistence of the arg at `index`,
	# check if `expr` depends of the preexistence of the same arg.
	fun dep_matches(expr: MOExpr, index: Int): Bool
	do
		if is_dependency_flag(index) and not expr.is_dependency_flag(index) then
			return false
		end

		return true
	end

	# Check if the preexistence of the arguments matches with the dependencies of the expression
	# Then, merge the preexsitence values of all arguments with the expression preexistence
	fun check_args: Int
	do
		var index = 0

		for arg in given_args do
			arg.preexist_expr
			if dep_matches(arg, index) then
				merge_preexistence(arg)
			else
				set_npre_nper
				return preexist_expr_value
			end
			index += 1
		end

		return preexist_expr_value
	end

	redef fun preexist_expr
	do
		if disable_preexistence_extensions then
			preexist_expr_value = pmask_NPRE_PER
		else if pattern.cuc > 0 then
			preexist_expr_value = pmask_NPRE_NPER
		else if pattern.perennial_status then
			preexist_expr_value = pmask_NPRE_PER
		else if pattern.lp_all_perennial then 
			preexist_expr_value = pmask_PVAL_PER
			check_args
		else if pattern.lps.length == 0 then
			set_npre_nper
		else
			preexist_expr_value = pmask_PVAL_PER
			for candidate in pattern.lps do
				if candidate.is_intern or candidate.is_extern then
					# WARNING
					# If the candidate method is intern/extern, then the return is preexist immutable
					# since the VM cannot make FFI.
					set_pval_per
					break
				else if not candidate.compiled then
					# The lp could be known by the model but not already compiled from ast to mo
					# So, we must NOT check it's return_expr (it could be still null)
					set_npre_nper
					break
				else if candidate.return_expr == null then
					# Lazy attribute not yet initialized
					# WARNING
					# Be sure that it can't be anything else that lazy attributes here
					trace("WARN NULL RETURN_EXPR {candidate} {candidate.mproperty}")
					set_npre_nper
					break
				end
				
				candidate.preexist_return
				merge_preexistence(candidate.return_expr.as(not null))
				if is_npre_per then
					break
				else
					check_args
				end
			end
		end

		return preexist_expr_value
	end
end


redef class MOSite
	# Compute the preexistence of the site call
	fun preexist_site: Int
	do
		expr_recv.preexist_expr
		if expr_recv.is_rec then expr_recv.set_pval_nper
		return expr_recv.preexist_expr_value
	end
end

redef class MOExprSitePattern
	# Number of uncompiled calles (local properties)
	var cuc = 0

	# If a LP no preexists and it's perexistence is perennial (unused while cuc > 0)
	var perennial_status = false

	# If all LPs preexists and are perennial, according to the current class hierarchy
	var lp_all_perennial = false

	# Call MMethodDef.propage_preexist on all lps 
	fun propage_preexist
	do
		for lp in lps do lp.propage_preexist
	end

	# Call MMethodDef.propage_npreexist on all lps
	fun propage_npreexist
	do
		for lp in lps do lp.propage_npreexist
	end

	# When add a new branch, if it is not compiled, unset preexistence to all expressions using it
	redef fun add_lp(lp)
	do
		super
		cuc += 1

		if cuc == 1 then
			for site in sites do
				site.expr_recv.init_preexist
				site.lp.propage_preexist
			end
		end

	end
end

redef class MONewPattern
	# Set npreexist new site preexistent
	# The non preexistence of newsite became preesitent if class is loaded
	fun set_preexist_newsite
	do
		for newexpr in newexprs do
			newexpr.set_ptype_per
			newexpr.lp.propage_npreexist
		end
	end
end

# Change preexistence state of new sites compiled before loading
redef class MClass
	redef fun handle_new_class
	do
		super
		new_pattern.set_preexist_newsite
	end
end

redef class ModelBuilder
	redef fun post_exec(mainmodule)
	do
		super(mainmodule)

		var compiled_methods = new List[MMethodDef]

		# Check if number of static callsites who preexists matches with the counter
		var preexist_static = 0
		for prop in mainmodule.model.mproperties do
			for propdef in prop.mpropdefs do
				if propdef isa MMethodDef and propdef.compiled then
					compiled_methods.add(propdef)

					for site in propdef.mosites do
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
		end

		if preexist_static != pstats.get("preexist_static") then
			print("WARNING: preexist_static {pstats.get("preexist_static")} is actually {preexist_static }")
		end

		# Recompile all active methods to get the upper bound of the preexistance
		# We don't need pstats counters with lower bound anymore
		pstats = new MOStats("UPPER")
		
		for mmethoddef in compiled_methods do mmethoddef.preexist_all(interpreter)

		print(pstats.pretty)
	end
end
