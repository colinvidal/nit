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

# Compute Single-Static Assignement form from an AST
module ssa

import variables_numbering
import virtual_machine

redef class VirtualMachine
	redef fun new_frame(node, mpropdef, args)
	do
		var sup = super

		# Compute SSA for method and attribute body
		if node isa AMethPropdef then
			# Compute ssa for the block
			node.compute_ssa(self)
		end

		if node isa AAttrPropdef then
			node.compute_ssa(self)
		end

		return sup
	end
end

redef class Variable
	# The dependencies of this variable for SSA-Algorithm
	var dependencies: HashSet[Variable] = new HashSet[Variable]

	# The blocks in which this variable is assigned
	var assignment_blocks: Array[ANode] = new Array[ANode] is lazy

	# Part of the program where this variable is read
	var read_blocks: Array[ANode] = new Array[ANode] is lazy
end

redef class ANode
	# The iterated dominance frontier of this block
	# i.e. the set of blocks this block dominate directly or indirectly
	var dominance_frontier: Array[ANode] = new Array[ANode] is lazy

	public fun compute_ssa(vm: VirtualMachine) do end

	# Add the `block` to the dominance frontier of this block
	fun add_df(block: ANode)
	do
		# Add this block recursively in super-blocks to compute the iterated
		# dominance frontier
		dominance_frontier.add(block)

		var dominator = dominator_block
		if dominator isa ABlockExpr then dominator.add_df(block)
	end

	# Return the block that dominate self
	# It can be a `ANode` or the enclosing `APropdef`
	fun dominator_block: ANode
	do
		var block: ANode = parent.as(not null)

		# While parent is not a block, go up
		while not block isa ABlockExpr do
			if block isa APropdef then return block

			block = block.parent.as(not null)
		end

		return block
	end
end

redef class APropdef
	# The variables contained in the body on this propdef
	var variables: HashSet[Variable] = new HashSet[Variable] is lazy
end

redef class AMethPropdef
	redef fun compute_ssa(vm)
	do
		# TODO : handle self
		if n_block != null then n_block.compute_ssa(vm)

		# Places where a phi-function is added per variable
		var phi_blocks = new HashMap[Variable, Array[ANode]]

		# For each variables in the propdef
		for v in variables do
			var phi_variables = new Array[ANode]

			var read_blocks = new Array[ANode]
			read_blocks.add_all(v.read_blocks)

			print v.to_s + "   " + read_blocks.to_s

			# While we have not treated each part accessing `v`
			while not read_blocks.is_empty do
				# Remove a block from the set
				var block = read_blocks.first
				read_blocks.remove(block)

				# For each block in the dominance frontier of `block`
				for df in block.dominance_frontier do
					# If we have not yet put a phi-function at the beginning of this block
					if not phi_variables.has(df) then
						#TODO: Add a phi function at the beginning of df
						print("Add a phi-function at the beginning of {df} for variable {v}")
						df.dump_tree
						phi_variables.add(df)

						if not v.read_blocks.has(df) then read_blocks.add(df)
					end
				end
			end

			# Add phi-variables to the global map
			phi_blocks[v] = phi_variables
		end
	end
end

redef class AAttrPropdef
	redef fun compute_ssa(vm)
	do
		# TODO : handle self
		if n_block != null then n_block.compute_ssa(vm)
	end
end

redef class AVarExpr
	redef fun compute_ssa(vm)
	do
		self.variable.as(not null).read_blocks.add(dominator_block)
	end
end

redef class AVardeclExpr
	redef fun compute_ssa(vm)
	do
		# Add the corresponding variable to the enclosing mpropdef
		vm.current_propdef.variables.add(self.variable.as(not null))

		self.n_expr.compute_ssa(vm)
	end
end

redef class AVarAssignExpr
	redef fun compute_ssa(vm)
	do
		self.variable.as(not null).assignment_blocks.add(dominator_block)
	end
end

redef class AVarReassignExpr
	redef fun compute_ssa(vm)
	do
		self.variable.as(not null).read_blocks.add(dominator_block)
		self.variable.as(not null).assignment_blocks.add(dominator_block)
	end
end

# TODO : go to super block for phi fonctions ?
# redef class AEscapeExpr
# 	redef fun stmt(v)
# 	do
# 		var ne = self.n_expr
# 		if ne != null then
# 			var i = v.expr(ne)
# 			if i == null then return
# 			v.escapevalue = i
# 		end
# 		v.escapemark = self.escapemark
# 	end
# end

redef class AReturnExpr
	redef fun compute_ssa(vm)
	do
		# TODO: create a special variable for the return
		self.n_expr.compute_ssa(vm)
	end
end

# redef class AAssertExpr
# 	redef fun stmt(v)
# 	do
# 		var cond = v.expr(self.n_expr)
# 		if cond == null then return
# 		if not cond.is_true then
# 			v.stmt(self.n_else)
# 			if v.is_escaping then return
# 			var nid = self.n_id
# 			if nid != null then
# 				fatal(v, "Assert '{nid.text}' failed")
# 			else
# 				fatal(v, "Assert failed")
# 			end
# 			exit(1)
# 		end
# 	end
# end

redef class AOrExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)
		self.n_expr2.compute_ssa(vm)
	end
end

redef class AImpliesExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)
		self.n_expr2.compute_ssa(vm)
	end
end

redef class AAndExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)
		self.n_expr2.compute_ssa(vm)
	end
end

redef class ANotExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)
	end
end

redef class AOrElseExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)
		self.n_expr2.compute_ssa(vm)
	end
end

redef class AArrayExpr
	redef fun compute_ssa(vm)
	do
		for nexpr in self.n_exprs do nexpr.compute_ssa(vm)
	end
end

redef class ASuperstringExpr
	redef fun compute_ssa(vm)
	do
		for nexpr in self.n_exprs do nexpr.compute_ssa(vm)
	end
end

redef class ACrangeExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)
		self.n_expr2.compute_ssa(vm)
	end
end

redef class AOrangeExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)
		self.n_expr2.compute_ssa(vm)
	end
end

redef class AIsaExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)
	end
end

# redef class AAsCastExpr
# 	redef fun expr(v)
# 	do
# 		var i = v.expr(self.n_expr)
# 		if i == null then return null
# 		var mtype = self.mtype.as(not null)
# 		var amtype = v.unanchor_type(mtype)
# 		if not v.is_subtype(i.mtype, amtype) then
# 			fatal(v, "Cast failed. Expected `{amtype}`, got `{i.mtype}`")
# 		end
# 		return i
# 	end
# end

# redef class AAsNotnullExpr
# 	redef fun expr(v)
# 	do
# 		var i = v.expr(self.n_expr)
# 		if i == null then return null
# 		if i.mtype isa MNullType then
# 			fatal(v, "Cast failed")
# 		end
# 		return i
# 	end
# end

# redef class AParExpr
# 	redef fun expr(v)
# 	do
# 		return v.expr(self.n_expr)
# 	end
# end

# redef class AOnceExpr
# 	redef fun expr(v)
# 	do
# 		if v.onces.has_key(self) then
# 			return v.onces[self]
# 		else
# 			var res = v.expr(self.n_expr)
# 			if res == null then return null
# 			v.onces[self] = res
# 			return res
# 		end
# 	end
# end

redef class ASendExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)
		for e in self.raw_arguments do e.compute_ssa(vm)
	end
end

redef class ASendReassignFormExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)
		for e in self.raw_arguments do e.compute_ssa(vm)
	end
end

redef class ASuperExpr
	redef fun expr(v)
	do
		var recv = v.frame.arguments.first

		var callsite = self.callsite
		if callsite != null then
			var args = v.varargize(callsite.mpropdef, recv, self.n_args.n_exprs)
			if args == null then return null
			# Add additional arguments for the super init call
			if args.length == 1 then
				for i in [0..callsite.msignature.arity[ do
					args.add(v.frame.arguments[i+1])
				end
			end
			# Super init call
			var res = v.callsite(callsite, args)
			return res
		end

		# standard call-next-method
		var mpropdef = self.mpropdef
		mpropdef = mpropdef.lookup_next_definition(v.mainmodule, recv.mtype)

		var args = v.varargize(mpropdef, recv, self.n_args.n_exprs)
		if args == null then return null

		if args.length == 1 then
			args = v.frame.arguments
		end
		var res = v.call(mpropdef, args)
		return res
	end
end

redef class ANewExpr
	redef fun compute_ssa(vm)
	do
		for e in self.n_args.n_exprs do e.compute_ssa(vm)
	end
end

redef class AAttrExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)
	end
end

redef class AAttrAssignExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)
	end
end

redef class AAttrReassignExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)
	end
end

redef class AIssetAttrExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)
	end
end

redef class ABlockExpr
	redef fun compute_ssa(vm)
	do
		# Go in the enclosing block to set the dominance frontier
		var block = dominator_block
		if block isa ABlockExpr then block.add_df(self)

		for e in self.n_expr do e.compute_ssa(vm)
	end
end

redef class AIfExpr
	redef fun compute_ssa(vm)
	do
		self.n_then.compute_ssa(vm)
		if self.n_else != null then self.n_else.compute_ssa(vm)
	end
end

redef class AIfexprExpr
	redef fun compute_ssa(vm)
	do
		self.n_then.compute_ssa(vm)
		self.n_else.compute_ssa(vm)
	end
end

redef class ADoExpr
	redef fun compute_ssa(vm)
	do
		self.n_block.compute_ssa(vm)
	end
end

redef class AWhileExpr
	redef fun compute_ssa(vm)
	do
		self.n_block.compute_ssa(vm)
	end
end

redef class ALoopExpr
	redef fun compute_ssa(vm)
	do
		self.n_block.compute_ssa(vm)
	end
end

redef class AForExpr
	redef fun compute_ssa(vm)
	do
		#TODO
		# Give a position to each variable declared in the header of the for
		# if self.variables.length == 1 then
		# 	self.variables.first.position = position
		# 	self.variables[0].position = position
		# 	position += 1
		# else if self.variables.length == 2 then
		# 	self.variables[0].position = position
		# 	position += 1
		# 	self.variables[1].position = position
		# 	position += 1
		# end
		self.n_block.compute_ssa(vm)
	end
end

# TODO : récolter les new dans une propriété locale
