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

		pattern.lps.add(cs.mpropdef)
		cs.mpropdef.callers.add(pattern)
		pattern.exprsites.add(exprsite)
		exprsite.pattern = pattern
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
 
	# Handle class loading for update optimizing model
	fun handle_class_loading(cls: MClass)
	do
		for p in new_patterns do p.handle_class_loading(cls)
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
	fun handle_new_branch(lp: MPropDef)
	do
		if debug_if_not_internal(lp.mclassdef.mmodule.to_s) then print("new branch {lp.mclassdef} redefines {lp.name}")

		# For each patterns in lp.gp with classdef of the lp <: pattern.rst
		var compatibles_patterns = new List[MOExprSitePattern]
		for p in exprsites_patterns do
			if p.compatibl_with(self, lp) then compatibles_patterns.add(p)
		end

		for p in compatibles_patterns do p.handle_new_branch(lp)
	end

	redef fun new_frame(node, mpropdef, args)
	do
		var ret = super
		if mpropdef isa MMethodDef then
			mpropdef.preexist_all
#			mpropdef.compiled = true
		end
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

		return self.call(propdef, args)
	end

	redef fun create_class(mclass)
	do
		# mclassdef.mpropdef (intro & redef)
		super
		handle_class_loading(mclass)

		for classdef in mclass.mclassdefs do
			for i in [1..classdef.mpropdefs.length - 1] do
				var mdef = classdef.mpropdefs[i]
				if not mdef.is_intro then handle_new_branch(mdef)
			end
		end
	end
end

redef class AAttrFormExpr
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

	# Optimize this attribute access
	# * `mproperty` The attribute which is accessed
	# * `recv` The receiver (The object) of the access
	protected fun optimize(mproperty: MAttribute, recv: MutableInstance)
	do
		if mproperty.intro_mclassdef.mclass.positions_attributes[recv.mtype.as(MClassType).mclass] != -1 then
			# if this attribute class has an unique position for this receiver, then use direct access
			offset = mproperty.absolute_offset
			status = 1
		else
			# Otherwise, perfect hashing must be used
			id = mproperty.intro_mclassdef.mclass.vtable.id
			offset = mproperty.offset
			status = 2
		end
	end
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

		return i
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
		if mproperty.intro_mclassdef.mclass.positions_methods[recv.mtype.as(MClassType).mclass] != -1 then
			offset = mproperty.absolute_offset
			status = 1
		else
			offset = mproperty.offset
			status = 2
		end
		id = mproperty.intro_mclassdef.mclass.vtable.id
	end
end

redef class AIsaExpr
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

		# Try to get the position of the target type in source's structures
		var value = source.mclass.positions_methods.get_or_null(target.mclass)

		if value != null then
			if value != -1 then
				# Store informations for Cohen test
				position = target.mclass.color
				status = 1
			else
				# We use perfect hashing
				status = 2
			end
		end
		id = target.mclass.vtable.id
	end
end

redef class AAsCastExpr
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

		if value != null then
			if value != -1 then
				# Store informations for Cohen test
				position = target.mclass.color
				status = 1
			else
				# We use perfect hashing
				status = 2
			end
		end
		id = target.mclass.vtable.id
	end
end

redef class Variable
	# Represents the view of the variable in the optimizing representation
	var movar: nullable MOVar

	# Create (if doesn't exists) the movar corresponding to AST node, and return it
	fun get_movar(node: AExpr): MOVar
	do
		if movar == null then
			if node isa ASelfExpr then
				movar = new MOParam(0)
			else if node isa AVarExpr then
				# A variable read
				if node.variable.parameter then
					movar = new MOParam(node.variable.position + 1)
				else if node.variable.dep_exprs.length == 1 then
					print("ast ssavar {self}")
					movar = new MOSSAVar(-1, new MOParam(1))
				else
					print("ast phivar {self}")
				end
			end
			assert movar != null
		end
		return movar.as(not null)
	end
end

redef class ANewExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		var sup = super(vm, old_block)

		var newexpr = new MONew(vm.current_propdef.mpropdef.as(MMethodDef))
		vm.current_propdef.mpropdef.as(MMethodDef).moexprs.add(newexpr)
		vm.set_new_pattern(newexpr, recvtype.mclass)

		return sup
	end
end

redef class ANode
	# True if self is a literal node
	fun is_lit: Bool
	do
		if self isa AIntExpr then return true
		if self isa ACharExpr then return true
		if self isa ANullExpr then return true
		if self isa AStringFormExpr then return true
		if self isa ATrueExpr then return true
		if self isa AFalseExpr then return true
		return false
	end

	# Convert AST node into MOExpression
	fun ast2mo: MOExpr
	do
		var mo_expr: MOExpr
		
		if is_lit then
			mo_expr = new MOLit
		else
			mo_expr = new MOSSAVar(-1, new MOParam(3))
		end

		return mo_expr
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

redef class AMethPropdef
	# list of return expression of the optimizing model
	var mo_dep_exprs: MOVar

	redef fun generate_basicBlocks(vm)
	do
		super(vm)

		if returnvar.dep_exprs.length == 1 then
			mo_dep_exprs = new MOSSAVar(returnvar.position, returnvar.dep_exprs.first.ast2mo)
		else
			var deps = new List[MOExpr]
			for a_expr in returnvar.dep_exprs do deps.add(a_expr.ast2mo)
			mo_dep_exprs = new MOPhiVar(returnvar.position, deps)
		end
		
		print("ast apropdef {mpropdef.as(not null)} mo_dep_exprs:{mo_dep_exprs}")
	end
end

redef class ASendExpr
	# Site invocation associated with this node
	var mocallsite: MOCallSite

	redef fun generate_basicBlocks(vm, old_block)
	do
		var sup = super(vm, old_block)
		var recv = n_expr.ast2mo
		
		var lp = vm.current_propdef.mpropdef.as(MMethodDef)
		mocallsite = new MOCallSite(recv, lp)
		lp.moexprsites.add(mocallsite)
		vm.set_exprsite_pattern(mocallsite, callsite.as(not null))

		# Expressions arguments given to the method called
		# mocallsite.given_args.add_all(raw_arguments)

		return sup
	end

	redef fun ast2mo
	do
		# Simulate that a parameter is return by the receiver
		callsite.mpropdef.return_expr = new MOParam(2)
		
		return mocallsite
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

redef class MMethodDef
	# Tell if the method has been compiled at least one time
	var compiled = false

	# List of callers of this local property
	var callers = new HashSet[MOExprSitePattern]

	# Return expression of the method (null if procedure)
	var return_expr: nullable MOExpr

	# List of expressions in this local property (without MOExprSite)
	# eg. attr.baz()
	var moexprs = new List[MOExpr]

	# List of site expressions in this local property
	# eg. a.foo().bar(), variable, instantiation site 
	var moexprsites = new List[MOExprSite]

	# List of object site in this local property (without MOExprSite)
	# eg. subtype test, write attribute
	var mosites = new List[MOSite]

	# List of mutable preexists expressions
	var exprs_preexist_mut = new List[MOExpr]

	# List of mutable non preexists expressions
	var exprs_npreexist_mut = new List[MOExpr]

	# Drop exprs_preesit_mut and set unknown state to all expression inside
	# If the return_expr is in it, recurse on callers
	fun propage_preexist
	do
		var flag = return_expr.is_preexists
		
		var cpy = new List[MOExpr]
		cpy.add_all(exprs_preexist_mut)
		for expr in cpy do
			expr.init_preexist_cache
			exprs_preexist_mut.remove(expr)
		end

		if flag then for p in callers do p.propage_preexist
	end

	# Drop exprs_npreesit_mut and set unknown state to all expression inside
	# If the return_expr is in it, recurse on callers
	fun propage_npreexist
	do
		var flag = not return_expr.is_preexists

		var cpy = new List[MOExpr]
		cpy.add_all(exprs_npreexist_mut)
		for expr in cpy do
			expr.init_preexist_cache
			exprs_npreexist_mut.remove(expr)
		end

		if flag then for p in callers do p.propage_npreexist
	end

	# Compute the preexistence of the return of the method expression
	fun preexist_return: Int
	do
		if not compiled then
			return_expr.set_preexistence_flag(pmask_NPRE_NPER)
			return return_expr.preexist_expr_value
		else if not return_expr.is_preexistence_unknown then
			return return_expr.preexist_expr_value
		else
			return_expr.set_preexistence_flag(pmask_RECURSIV)
			return return_expr.preexist_expr_value
		end
	end

	# Compute the preexistence of all invocation sites and return site of the method
	fun preexist_all
	do
		if compiled then return
		compiled = true

		print("preexist_all of {self}")
		var preexist: Int

		if return_expr != null then
			if return_expr.get_preexistence_flag(pmask_RECURSIV) then
				return_expr.set_preexistence_flag(pmask_PVAL_NPER)
			end

			preexist = return_expr.preexist_expr_value
			print("\tpreexist of return : {return_expr.as(not null)} {preexist} {preexist.preexists_bits}")
		end
	
		for expr in moexprs do
			expr.preexist_expr
			preexist = expr.preexist_expr_value
			print("\tpreexist of expr {expr} {preexist} {preexist.preexists_bits}")
			if expr isa MONew then print("\t\t" + "class {expr.pattern.cls} is loaded? {expr.pattern.is_loaded}")

			# TODO: choose implementation here
		end

		for exprsite in moexprsites do
			exprsite.preexist_site
			preexist = exprsite.preexist_site_value
			print("\tpreexist of exprsite {exprsite.expr_recv}.{exprsite} {preexist} {preexist.preexists_bits}")

			# TODO:choose implementation here
		end

		for site in mosites do
			print("MOSite cases - NYI")
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
# UNKNOWN:	1...

# Preexistence mask of perennial value preexistence
fun pmask_PVAL_PER: Int
do
	return 15
end

# Preexistence mask of perennial type preexistence
fun pmask_PTYPE_PER: Int
do
	return 13
end

# Preexistence mask of no perennial value preexistence
fun pmask_PVAL_NPER: Int
do
	return 11
end

# Preexistence mask of no perennial type preexistence
fun pmask_PTYPE_NPER: Int
do
	return 9
end

# Preexistence mask of perennial no preexistence
fun pmask_NPRE_PER: Int
do
	return 12
end

# Preexistence mask of no perennial no preexistence
fun pmask_NPRE_NPER: Int
do
	return 8
end

# Preexistence mask of recursive calls
fun pmask_RECURSIV: Int
do
	return 0
end

# Preexistence mask of unknown preexistence
fun pmask_UNKNOWN: Int
do
	return -1
end

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
		assert index > 15

		return 1.lshift(index).bin_and(preexist_expr_value) != 0
	end

	# Set a preexistence flag
	fun set_preexistence_flag(flag: Int): Int
	do
		# It must not write on dependencies bits
		assert flag < 16

		preexist_expr_value = preexist_expr_value.bin_or(flag)
		return preexist_expr_value
	end

	# Get if the preexistence state of a expression matches with given flag
	fun get_preexistence_flag(flag: Int): Bool
	do
		return preexist_expr_value.bin_and(15) == flag
	end

	# Return true if the preexistence of the expression isn't known
	fun is_preexistence_unknown: Bool
	do
		return preexist_expr_value == pmask_UNKNOWN
	end

	# Return true if the expression preexists (recursive case is interpreted as preexistent)
	fun is_preexists: Bool
	do
		return preexist_expr_value.bin_and(1) == 1 or preexist_expr_value == 0
	end

	# Return true if the preexistence state of the expression is perennial
	fun is_perennial: Bool
	do
		return preexist_expr_value.bin_and(4) == 4
	end

	# Initialize preexist_cache to UNKNOWN
	fun init_preexist_cache
	do
		preexist_expr_value = pmask_UNKNOWN
	end

	# Merge dependecies and preexistence state
	fun merge_preexistence(expr: MOExpr): Int
	do
		if expr.get_preexistence_flag(pmask_NPRE_PER) then
			preexist_expr_value = pmask_NPRE_PER
		else if expr.get_preexistence_flag(pmask_RECURSIV) then
			preexist_expr_value = pmask_RECURSIV
		else
			var pre = preexist_expr_value.bin_and(15)
			var deps = preexist_expr_value.bin_and(240)

			pre = pre.bin_and(expr.preexist_expr_value.bin_and(15))
			deps = deps.bin_or(expr.preexist_expr_value.bin_and(240))

			preexist_expr_value = pre.bin_or(deps)
		end

		return preexist_expr_value
	end
end

redef class MOLit
	redef var preexist_expr_value = pmask_PVAL_PER

	redef fun preexist_expr
	do
		return preexist_expr_value
	end
end

redef class MOParam
	redef var preexist_expr_value = pmask_PVAL_PER

	init
	do
		set_dependency_flag(offset)
	end

	redef fun preexist_expr
	do
		return preexist_expr_value
	end
end

redef class MONew
	redef var preexist_expr_value = pmask_NPRE_NPER

	redef fun preexist_expr
	do
		if pattern.is_loaded then set_preexistence_flag(pmask_PTYPE_PER)
		return preexist_expr_value
	end
end

redef class MOSSAVar
	init
	do
		preexist_expr_value = dependency.preexist_expr
	end

	redef fun preexist_expr
	do
		return preexist_expr_value
	end
end

redef class MOPhiVar
	redef fun preexist_expr
	do
		if is_preexistence_unknown then
			preexist_expr_value = pmask_PVAL_PER
			for dep in dependencies do
				merge_preexistence(dep)
				if get_preexistence_flag(pmask_NPRE_PER) then
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
		if is_preexistence_unknown then
			expr_recv.preexist_expr
			if immutable and expr_recv.is_preexists then
				set_preexistence_flag(pmask_PVAL_PER)
			else
				if expr_recv.is_preexists then
					if expr_recv.is_perennial then
						set_preexistence_flag(pmask_PVAL_PER)
					else
						set_preexistence_flag(pmask_PVAL_NPER)
					end

					# The receiver is always at position 0 of the environment
					set_dependency_flag(0)
				else
					if expr_recv.is_perennial then
						set_preexistence_flag(pmask_NPRE_PER)
					else
						set_preexistence_flag(pmask_NPRE_NPER)
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
				set_preexistence_flag(pmask_NPRE_NPER)
				return preexist_expr_value
			end
			index += 1
		end
		return preexist_expr_value
	end

	redef fun preexist_expr
	do
		if pattern.cuc > 0 then
			preexist_expr_value = pmask_NPRE_NPER
		else if pattern.perennial_status then
			preexist_expr_value = pmask_NPRE_PER
		else if pattern.lp_all_perennial then 
			preexist_expr_value = pmask_PVAL_PER
			check_args
		else
			preexist_expr_value = pmask_PVAL_PER
			for candidate in pattern.lps do
				candidate.preexist_return
				merge_preexistence(candidate.return_expr.as(not null))
				if get_preexistence_flag(pmask_NPRE_PER) then
					break
				else
					check_args
				end
			end
		end

		return preexist_expr_value
	end
end


redef class MOPropSite
	# The preexistence value of the site call
	var preexist_site_value: Int = pmask_UNKNOWN

	# Compute the preexistence of the site call
	fun preexist_site: Int
	do
		expr_recv.preexist_expr

		if expr_recv.get_preexistence_flag(pmask_RECURSIV) then expr_recv.set_preexistence_flag(pmask_PVAL_NPER)
		preexist_site_value = expr_recv.preexist_expr
		return preexist_site_value
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
	# Set non preesitent all non perenial preexistent expressions known by this pattern 
	# If the expression if the return of a lp, propage the callers
	fun handle_new_branch(lp: MPropDef)
	do
		lps.add(lp.as(MMethodDef))
		cuc += 1

		if cuc == 1 then
			for expr in exprsites do
				if expr.is_preexists and not expr.is_perennial then
#					var old = expr.preexist_site_value
					print("\texpr NEEDS [TODO] switch to non preexist {expr}")
#					if expr.lp.return_expr == expr then
#						expr.lp.propage_preexist
#					end
				end
			end
		end
	end
end

redef class MONewPattern
	# Handle class loading for update the optimizing model
	# The non preexistence of newsite became preesitent if class is loaded
	fun handle_class_loading(loadcls: MClass)
	do
		if cls == loadcls then
			for newexpr in newexprs do
				var old = newexpr.preexist_expr_value.preexists_bits.to_s
				newexpr.set_preexistence_flag(pmask_PVAL_PER)
				var cur = newexpr.preexist_expr_value.preexists_bits.to_s
				print("update prexistence {newexpr} in {newexpr.lp} from {old} to {cur}")
			end
		end
	end
end
