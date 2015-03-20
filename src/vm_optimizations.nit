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

import vm
import variables_numbering

redef class VirtualMachine
	# List of known patterns (static type + global property)
	var patterns = new List[MPattern]

	# Add pattern if it didn't already exists
	fun add_pattern(cs: CallSite): nullable MPattern
	do
		var found = false

		for p in patterns do
			if p.gp == cs.mproperty and p.st == cs.recv then
				found = true
				return p.add_callsite(cs)
			end
		end

		if not found then
			var p = new MPattern(cs.recv, cs.mproperty, cs.mpropdef)
			patterns.push(p)
			return p.add_callsite(cs)
		end
		
		return null
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
	var pattern: MPattern

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
		return "<{class_name}#ST:{recv}#GP:{mproperty}#pattern_valid:{pattern.st == recv and pattern.gp == mproperty}>"
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
		return n_expr.numbering(v, pos)
	end
end

redef class MMethodDef
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
end

redef class ModelBuilder
	redef fun run_virtual_machine(mainmodule: MModule, arguments: Array[String])
	do
		super
		var buf = "\n"
		var known_patterns = new List[MPattern]

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
			buf += "{p.st}.{p.gp.name}\n"
		end

		self.toolcontext.info("*** NITVM: list of callsites by mpropdef ***" + buf, 1)
	end
end

# Pattern of a callsite
class MPattern
	# Static type of the receiver
	var st: MType

	# Global property called
	var gp: MMethod

	# Local property called
	var lp: MMethodDef

	# CallSite using this pattern
	var callsites = new List[CallSite]

	# Add a callsite using this pattern
	fun add_callsite(cs: CallSite): nullable MPattern
	do
		if cs.recv == st and cs.mproperty == gp then
			if not callsites.has(cs) then
				callsites.add(cs)
			end

			return self
		end

		return null
	end
end
