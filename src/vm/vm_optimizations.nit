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
import variables_numbering
import model_optimizations

redef class VirtualMachine
	# List of known patterns (static type + global property)
	var patterns = new List[MOPattern]

	# Add pattern if it didn't already exists
	fun add_pattern(cs: CallSite): nullable MOPattern
	do
		var p = get_pattern(cs.mproperty, cs.recv)

		if p == null then
			p = new MOPattern(cs.recv, cs.mproperty)
			patterns.push(p)
		end
		return p.add_callsite(cs)
	end

	# Get a pattern who matches with given gp and rst
	fun get_pattern(gp: MProperty, rst: MType): nullable MOPattern
	do
		for p in patterns do
			if p.gp == gp and p.rst == rst then
				return p
			end
		end
		return null
	end

	# If the new frame is a method frame, marks this local property as compiled
	redef fun new_frame(node, mpropdef, args)
	do
		var ret = super
		if mpropdef isa MMethodDef then
			mpropdef.compiled = true
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

	# Pattern that uses this call site
	var pattern: MOPattern

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

	redef fun to_s: String
	do
		return "<{class_name}#ST:{recv}#GP:{mproperty}#pattern_valid:{pattern.rst == recv and pattern.gp == mproperty}>"
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

redef class ASendExpr
	redef fun numbering(v: VirtualMachine, pos: Int): Int
	do
		v.current_mpropdef.as(MMethodDef).add_callsite(v, callsite.as(not null))
		for arg in raw_arguments do
			arg.numbering(v, pos)
		end

		# test preexistence sur parametres
		var fake_recv = new MOParam(1)
		var expr = new MOCallSite(fake_recv, callsite.pattern)
		v.current_mpropdef.as(MMethodDef).call_exprs.add(expr)

		return n_expr.numbering(v, pos)
	end
end

redef class MMethodDef
	# Tell if the method has been compiled at least one time
	var compiled = false

	# List of known callsites inside a local property
	var callsites = new List[CallSite]

	# Add a callsite inside a local property
	fun add_callsite(v: VirtualMachine, cs: CallSite)
	do
		var p = v.add_pattern(cs)

		if p != null then
			cs.pattern = p
		else
			print "Error: pattern null for a callsite"
			abort
		end

		if not callsites.has(cs) then
			callsites.push(cs)
		end
	end

	# Return expression of the method (null if procedure)
	var return_expr: nullable MOExpr

	# List of expressions sites (contains callsites and read attribute)
	var call_exprs = new List[MOExprSite]

	# Compute the preexistence of the return of the method expression
	fun preexists_return(reset: List[MOExpr]): Int
	do
		if not compiled then
			return pmask_NPRE_NPER
		else if not return_expr.is_preexistence_unknown then
			return return_expr.preexist_cache
		else
			return_expr.set_preexistence_flag(pmask_RECURSIV)
			if not return_expr.is_perennial then
				reset.add(return_expr.as (not null))
			end
			return return_expr.preexists(reset)
		end
	end

	# Compute the preexistence of all invocation sites and return site of the method
	fun preexists_all
	do
		var reset = new List[MOExpr]

		if return_expr != null then
			preexists_return(reset)
			if return_expr.get_preexistence_flag(pmask_RECURSIV) then
				return_expr.set_preexistence_flag(pmask_PVAL_NPER)
			end

			# TODO: choose implementation of expr_return here
		end

		for expr in call_exprs do
			var recv = expr.expr_recv

			recv.preexists(reset)
			print("preexist " + recv.to_s + " > " + recv.preexist_cache.to_s)
			if recv.get_preexistence_flag(pmask_RECURSIV) then
				recv.set_preexistence_flag(pmask_PVAL_NPER)
			end
			expr.preexist_cache = recv.preexist_cache

			# TODO: choose implementation of expr here
		end

		for expr in reset do
			expr.init_preexist_cache
		end
	end
end

redef class ModelBuilder
	redef fun run_virtual_machine(mainmodule: MModule, arguments: Array[String])
	do
		super
		var buf = "\n"
		var known_patterns = new List[MOPattern]

		for c in model.mclassdef_hierarchy do
			for m in c.mpropdefs do
				if m isa MMethodDef then
					buf += m.to_s + "\n"
					for cs in m.callsites do
						buf += "\t {cs.to_s}\n"
						if not known_patterns.has(cs.pattern) then
							known_patterns.add(cs.pattern)
						end
					end
				end
			end
		end

		buf += "*** NITVM: List of known patterns ***\n"
		for p in known_patterns do
			buf += "{p.rst}.{p.gp.name}\n"
		end

		self.toolcontext.info("*** NITVM: list of callsites by mpropdef ***" + buf, 1)

		buf = ""
		for p in known_patterns do
			for lp in p.lps do
				for expr in lp.call_exprs do
					lp.preexists_all
					buf += "preexist_cache of " + expr.pattern.rst.to_s
					buf += "#" + expr.pattern.gp.to_s + ": " + expr.preexist_cache.to_s + "\n"
				end
			end
		end
		self.toolcontext.info("*** NITVM: test preexistence ***\n" + buf, 1)
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
	# The cached preexistence of the expression
	var preexist_cache: Int = pmask_UNKNOWN

	# Compute the preexistence of the expression
	# `reset` is the list of no perennial preexistences of the expression and it depdendencies
	fun preexists(reset: List[MOExpr]): Int is abstract

	# Set a bit in a dependency range on the given offset to a preexistence state
	# Shift 4 bits (preexistence status) + the offset of dependency, and set bit to 1
	fun set_dependency_flag(offset: Int): Int
	do
		preexist_cache = preexist_cache.bin_or(1.lshift(4 + offset))
		return preexist_cache
	end

	# True if the expression depends of the preexistence of a dependencie at `index`
	fun is_dependency_flag(index: Int): Bool
	do
		# It must concern a dependency bit
		assert index > 15

		return 1.lshift(index).bin_and(preexist_cache) != 0
	end

	# Set a preexistence flag
	fun set_preexistence_flag(flag: Int): Int
	do
		# It must not write on dependencies bits
		assert flag < 16

		preexist_cache = preexist_cache.bin_and(240).bin_or(flag)
		return preexist_cache
	end

	# Get if the preexistence state of a expression matches with given flag
	fun get_preexistence_flag(flag: Int): Bool
	do
		return preexist_cache.bin_and(15) == flag
	end

	# Return true if the preexistence of the expression isn't known
	fun is_preexistence_unknown: Bool
	do
		return preexist_cache == pmask_UNKNOWN
	end

	# Return true if the expression preexists (recursive case is interpreted as preexistent)
	fun is_preexists: Bool
	do
		return preexist_cache.bin_and(1) == 1 or preexist_cache == 0
	end

	# Return true if the preexistence state of the expression is perennial
	fun is_perennial: Bool
	do
		return preexist_cache.bin_and(4) == 4
	end

	# Initialize preexist_cache to UNKNOWN
	fun init_preexist_cache
	do
		preexist_cache = pmask_UNKNOWN
	end

	# Merge dependecies and preexistence state
	fun merge_preexistence(expr: MOExpr): Int
	do
		if expr.get_preexistence_flag(pmask_NPRE_PER) then
			preexist_cache = pmask_NPRE_PER
		else if expr.get_preexistence_flag(pmask_RECURSIV) then
			preexist_cache = pmask_RECURSIV
		else
			var pre = preexist_cache.bin_and(15)
			var deps = preexist_cache.bin_and(240)

			pre = pre.bin_and(expr.preexist_cache.bin_and(15))
			deps = deps.bin_or(expr.preexist_cache.bin_and(240))
			
			preexist_cache = pre.bin_or(deps)
		end

		return preexist_cache
	end
end

redef class MOLit
	redef var preexist_cache = pmask_PVAL_PER

	redef fun preexists(reset)
	do
		return preexist_cache
	end
end

redef class MOParam
	redef var preexist_cache = pmask_PVAL_PER

	redef fun preexists(reset)
	do
		return set_dependency_flag(offset)
	end
end

redef class MONew
	redef fun preexists(reset)
	do
		if loaded then
			set_preexistence_flag(pmask_PTYPE_PER)
		else
			set_preexistence_flag(pmask_NPRE_NPER)
			reset.add(self)
		end

		return preexist_cache
	end
end

redef class MOSSAVar
	redef fun preexists(reset)
	do
		if is_preexistence_unknown then
			preexist_cache = dependency.preexists(reset)
			if not is_perennial then
				reset.add(self)
			end
		end

		return preexist_cache
	end
end

redef class MOPhiVar
	redef fun preexists(reset)
	do
		if is_preexistence_unknown then
			preexist_cache = pmask_PVAL_PER
			for dep in dependencies do
				merge_preexistence(dep)
				if get_preexistence_flag(pmask_NPRE_PER) then
					break
				end
			end

			if not is_perennial then
				reset.add(self)
			end
		end

		return preexist_cache
	end
end


redef class MOReadSite
	redef fun preexists(reset)
	do
		if is_preexistence_unknown then
			if immutable then
				set_preexistence_flag(pmask_NPRE_PER)
			else
				expr_recv.preexists(reset)
				if expr_recv.is_preexists then
					if expr_recv.is_perennial then
						set_preexistence_flag(pmask_PVAL_PER)
					else
						set_preexistence_flag(pmask_PVAL_NPER)
						reset.add(self)
					end

					# The receiver is always at position 0 of the environment 
					set_dependency_flag(0)
				else
					if expr_recv.is_perennial then
						set_preexistence_flag(pmask_NPRE_PER)
					else
						set_preexistence_flag(pmask_NPRE_NPER)
						reset.add(self)
					end
				end
			end
		end

		return preexist_cache
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
	fun check_args(reset: List[MOExpr]): Int
	do
		var index = 0

		for arg in given_args do
			arg.preexists(reset)
			if dep_matches(arg, index) then
				merge_preexistence(arg)
			else
				set_preexistence_flag(pmask_NPRE_NPER)
				reset.add(self)
				return preexist_cache
			end
			index += 1
		end

		return preexist_cache
	end

	redef fun preexists(reset)
	do
		if pattern.cuc > 0 then
			set_preexistence_flag(pmask_NPRE_NPER)
			reset.add(self)
		else if pattern.perennial_status then
			set_preexistence_flag(pmask_NPRE_PER)
		else if pattern.lp_all_perennial then
			check_args(reset)
		else
			set_preexistence_flag(pmask_PVAL_PER)
			for lp in pattern.lps do
				lp.preexists_return(reset)
				merge_preexistence(lp.return_expr.as(not null))
				if get_preexistence_flag(pmask_NPRE_PER) then
					break
				else
					check_args(reset)
				end
			end
		end

		if not is_perennial then
			reset.add(self)
		end

		return preexist_cache	
	end
end

redef class MOPattern
	# Number of uncompiled calles (local properties)
	var cuc = 0

	# If a LP no preexists and it's perexistence is perennial (unused while cuc > 0)
	var perennial_status = false

	# If all LPs preexists and are perennial, according to the current class hierarchie
	var lp_all_perennial = false
end
