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

# Compute Single-Static Assignment form from an AST
module ssa

import variables_numbering
import virtual_machine

redef class VirtualMachine
	redef fun new_frame(node, mpropdef, args)
	do
		var sup = super

		# Compute SSA for method and attribute body
		if node isa AMethPropdef or node isa AAttrPropdef then
			# The first step is to generate the basic blocks
			if not node.as(APropdef).is_generated then node.as(APropdef).generate_basicBlocks(self)
		end

		return sup
	end
end

# Represent a sequence of the program
# A basic block is composed of several instruction without a jump
class BasicBlock
	# First instruction of the basic block
	var first: ANode is noinit

	# Last instruction of the basic block
	var last: ANode is noinit

	# Direct successors
	var successors = new Array[BasicBlock]

	# Direct precessors
	var predecessors = new Array[BasicBlock]

	# Self is the old block to link to the new
	# The two blocks are not linked if the current ends with
	# a `AReturnExpr` or `ABreakExpr`
	# i.e. self is the predecessor of `successor`
	# `successor` The successor block
	fun link(successor: BasicBlock)
	do
		# Do not link the two blocks if the current block end with a return
		if last isa AReturnExpr then return

		if last isa ABreakExpr then return

		successors.add(successor)
		successor.predecessors.add(self)
	end

	# Self is the old block to link to the new
	# i.e. self is the predecessor of `successor`
	# `successor` The successor block
	fun link_special(successor: BasicBlock)
	do
		# Link the two blocks even if the current block
		# ends with a return or a break
		successors.add(successor)
		successor.predecessors.add(self)
	end

	# Used to dump the BasicBlock to dot
	var treated: Bool = false

	# Indicate the BasicBlock is newly created and needs to be updated
	var need_update: Bool = false
end

redef class Variable
	# The dependencies of this variable for SSA-Algorithm
	var dependencies: Array[Variable] = new Array[Variable]

	# The blocks in which this variable is assigned
	var assignment_blocks: Array[ANode] = new Array[ANode] is lazy

	# Part of the program where this variable is read
	var read_blocks: Array[ANode] = new Array[ANode] is lazy
end

class PhiFunction
	# The dependencies of a variable for SSA-Algorithm
	var dependencies: Array[Variable] = new Array[Variable] is lazy

	# The position in the AST of the phi-function
	var location: ANode

	# Set the dependencies for the phi-function
	# *`block` block in which we go through the dominance-frontier
	# *`v` The variable to looking for
	fun add_dependencies(block: ANode, v: Variable)
	do
		# Look in which blocks of DF(block) `v` has been assigned
		for b in block.dominance_frontier do
			if v.assignment_blocks.has(b) then dependencies.add(v)
		end
	end
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

	# The first basic block of the code
	var basic_block: nullable BasicBlock

	# If true, the basic blocks where generated
	var is_generated: Bool = false

	# Generate all basic blocks for this code
	fun generate_basicBlocks(vm:VirtualMachine) do end
end

redef class AExpr
	# Generate recursively basic block for this expression
	# *`vm` Running instance of the virtual machine
	# *`block` A basic block not completely filled
	# Return the newest block
	fun generate_basicBlocks(vm: VirtualMachine, block: BasicBlock): BasicBlock
	do
		#print "NOT YET IMPLEMENTED = " + self.class_name
		return block
	end
end

redef class AMethPropdef

	# The return variable of the propdef
	# Create an empty variable for the return of the method
	# and treat returns like variable assignments
	var returnvar: Variable = new Variable("returnvar")

	# The PhiFunction this method contains
	var phi_functions = new Array[PhiFunction]

	redef fun generate_basicBlocks(vm)
	do
		basic_block = new BasicBlock
		basic_block.first = self
		basic_block.last = self

		# Recursively goes into the nodes
		if n_block != null then
			n_block.generate_basicBlocks(vm, basic_block.as(not null))
		end

		is_generated = true

		# FIXME: just debug the foo method
		if mpropdef != null then
			if mpropdef.name == "foo" then
				# Dump the hierarchy in a dot file
				var debug = new BlockDebug(new FileWriter.open("basic_blocks.dot"))
				debug.dump(basic_block.as(not null))
			end
		end
	end

	redef fun compute_ssa(vm)
	do
		# TODO : handle self
		if n_block != null then n_block.compute_ssa(vm)

		# If the method has a signature
		if n_signature != null then
			# TODO: parameters
			print "Parameters = " + n_signature.n_params.to_s
		end

		# Places where a phi-function is added per variable
		var phi_blocks = new HashMap[Variable, Array[ANode]]

		# For each variables in the propdef
		for v in variables do
			var phi_variables = new Array[ANode]

			var read_blocks = new Array[ANode]
			read_blocks.add_all(v.read_blocks)

			# While we have not treated each part accessing `v`
			while not read_blocks.is_empty do
				# Remove a block from the set
				var block = read_blocks.first
				read_blocks.remove(block)

				# For each block in the dominance frontier of `block`
				for df in block.dominance_frontier do
					# If we have not yet put a phi-function at the beginning of this block
					if not phi_variables.has(df) then
						print("Add a phi-function at the beginning of {df} for variable {v}")
						phi_variables.add(df)

						# Create a new phi-function and set its dependencies
						var phi = new PhiFunction(df)
						phi.add_dependencies(block, v)
						phi_functions.add(phi)

						if not v.read_blocks.has(df) then read_blocks.add(df)
					end
				end
			end

			# Add `phi-variables` to the global map
			phi_blocks[v] = phi_variables
		end

		for p in phi_functions do
			print "\t" + p.location.to_s + ", " + p.dependencies.to_s
		end
	end
end

# Utility class for dump basic block and SSA to dot files
class BlockDebug
	var file: FileWriter

	# Dump the hierarchy of BasicBlock from `block`
	fun dump(block: BasicBlock)
	do
		# Write the basic blocks hierarchy in debug file
		file.write("digraph basic_blocks\n\{\n")
		var i = 0
		file.write(print_block(block, i))
		file.write("\n\}")

		file.close
	end

	fun print_block(block: BasicBlock, i:Int): String
	do
		# Precise the type and location of the begin and end of current block
		var s = "block{block.hash.to_s} [shape=record, label="+"\"\{"
		s += "block" + block.hash.to_s
		s += "|\{" + block.first.location.file.filename.to_s + block.first.location.line_start.to_s
		s += " | " + block.first.to_s.escape_to_dot
		s += "}|\{" + block.last.location.file.filename.to_s + block.last.location.line_start.to_s
		s += " | " + block.last.to_s.escape_to_dot + "}}\"];"+ "\n"

		i += 1
		block.treated = true

		for b in block.successors do
			# Print edges to successors
			s += "block{block.hash.to_s} -> " + " block{b.hash.to_s};\n"

			# Print recursively child blocks
			if not b.treated then s += print_block(b, i)
		end

		return s
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
		self.n_value.compute_ssa(vm)
	end
end

redef class AVarReassignExpr
	redef fun compute_ssa(vm)
	do
		self.variable.as(not null).read_blocks.add(dominator_block)
		self.variable.as(not null).assignment_blocks.add(dominator_block)
		self.n_value.compute_ssa(vm)
	end
end

redef class ABreakExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		# Finish the old block
		old_block.last = self

		# Search the enclosing loop
		var found = false
		var loop_block = old_block
		while not found do
			var first = loop_block.first
			if first isa AWhileExpr or first isa ALoopExpr or first isa ADoExpr or first isa AForExpr then
				found = true
			end

			if loop_block.predecessors.length == 0 then break

			loop_block = loop_block.predecessors.first
		end

		# Link the old_block to the first instruction of the loop
		old_block.link_special(loop_block.successors.first)

		return old_block
	end
end

#TODO: implement it
redef class AContinueExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		return old_block
	end
end

redef class AReturnExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)

		var returnvar = vm.current_propdef.as(AMethPropdef).returnvar
		returnvar.assignment_blocks.add(dominator_block)
	end

	redef fun generate_basicBlocks(vm, old_block)
	do
		# The return just set the current block and stop the recursion
		old_block.last = self
		return old_block
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

redef class AParExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		return self.n_expr.generate_basicBlocks(vm, old_block)
	end
end

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

	redef fun generate_basicBlocks(vm, old_block)
	do
		# A call does not finish the current block
		# because we create intra-procedural basic blocks here

		# We do not need to recurse over the arguments since
		return self.n_expr.generate_basicBlocks(vm, old_block)
	end
end

redef class ASendReassignFormExpr
	redef fun compute_ssa(vm)
	do
		self.n_expr.compute_ssa(vm)
		self.n_value.compute_ssa(vm)
		for e in self.raw_arguments do e.compute_ssa(vm)
	end
end

# redef class ASuperExpr
# 	redef fun expr(v)
# 	do
# 		var recv = v.frame.arguments.first

# 		var callsite = self.callsite
# 		if callsite != null then
# 			var args = v.varargize(callsite.mpropdef, recv, self.n_args.n_exprs)
# 			if args == null then return null
# 			# Add additional arguments for the super init call
# 			if args.length == 1 then
# 				for i in [0..callsite.msignature.arity[ do
# 					args.add(v.frame.arguments[i+1])
# 				end
# 			end
# 			# Super init call
# 			var res = v.callsite(callsite, args)
# 			return res
# 		end

# 		# standard call-next-method
# 		var mpropdef = self.mpropdef
# 		mpropdef = mpropdef.lookup_next_definition(v.mainmodule, recv.mtype)

# 		var args = v.varargize(mpropdef, recv, self.n_args.n_exprs)
# 		if args == null then return null

# 		if args.length == 1 then
# 			args = v.frame.arguments
# 		end
# 		var res = v.call(mpropdef, args)
# 		return res
# 	end
# end

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

	# The block needs to know if a new block is created
	redef fun generate_basicBlocks(vm, old_block)
	do
		var last_block = old_block
		var current_block: BasicBlock

		# Recursively continue in the body of the block
		for i in [0..self.n_expr.length[ do
			current_block = self.n_expr[i].generate_basicBlocks(vm, last_block)

			if current_block.need_update then
				if i < (self.n_expr.length-1) then
					# Current_block must be filled
					current_block.first = self.n_expr[i+1]
					current_block.last = self.n_expr[i+1]
					current_block.need_update = false
				else
					# Put the current block at the end of the block
					current_block.first = last_block.last
					current_block.last = last_block.last
				end
			end

			if not current_block.last isa AEscapeExpr or current_block.last isa AReturnExpr then
				# Re-affected the last block
				current_block.last = self.n_expr[i]
			end

			last_block = current_block
		end

		return last_block
	end
end

redef class AIfExpr
	redef fun compute_ssa(vm)
	do
		self.n_then.compute_ssa(vm)
		if self.n_else != null then self.n_else.compute_ssa(vm)
	end

	redef fun generate_basicBlocks(vm, old_block)
	do
		# Terminate the previous block
		old_block.last = self

		# Create a new block for the test
		var block_test = new BasicBlock
		block_test.first = self.n_expr
		block_test.last = self.n_expr

		# Link the test to the previous block
		old_block.link(block_test)

		# We start two new blocks if the if has two branches
		var block_then = new BasicBlock

		# Launch the recursion in two successors if they exist
		if self.n_then != null then
			block_test.link(block_then)

			block_then.first = self.n_then.as(not null)
			block_then.last = self.n_then.as(not null)
			self.n_then.generate_basicBlocks(vm, block_then)
		end

		var block_else = new BasicBlock

		if self.n_else != null then
			block_test.link(block_else)

			block_else.first = self.n_else.as(not null)
			block_else.last = self.n_else.as(not null)
			self.n_else.generate_basicBlocks(vm, block_else)
		end

		# Create a new BasicBlock to represent the two successor
		# branches of the if
		var new_block = new BasicBlock
		new_block.first = self
		new_block.last = self

		if self.n_then != null then block_then.link(new_block)

		# The new block needs to be filled by the caller
		new_block.need_update = true

		if block_else.predecessors.length != 0 then block_else.link(new_block)

		return new_block
	end
end

redef class AIfexprExpr
	redef fun compute_ssa(vm)
	do
		self.n_then.compute_ssa(vm)
		self.n_else.compute_ssa(vm)
	end

	redef fun generate_basicBlocks(vm, old_block)
	do
		# We start two new blocks if the if has two branches
		old_block.last = self
		var block_then = new BasicBlock

		# Link the two to the predecessor
		old_block.link(block_then)

		# Launch the recursion in two successors if they exist
		block_then.first = self.n_then
		block_then.last = self.n_then
		self.n_then.generate_basicBlocks(vm, block_then)

		var block_else = new BasicBlock
		old_block.link(block_else)

		block_else.first = self.n_else
		block_else.last = self.n_else

		return self.n_else.generate_basicBlocks(vm, block_else)
	end
end

redef class ADoExpr
	redef fun compute_ssa(vm)
	do
		self.n_block.compute_ssa(vm)
	end

	redef fun generate_basicBlocks(vm, old_block)
	do
		old_block.last = self

		# The beginning of the block is the first instruction
		var block = new BasicBlock
		block.first = self.n_block.as(not null)
		block.last = self.n_block.as(not null)

		old_block.link(block)
		return self.n_block.generate_basicBlocks(vm, block)
	end
end

redef class AWhileExpr
	redef fun compute_ssa(vm)
	do
		self.n_block.compute_ssa(vm)
	end

	redef fun generate_basicBlocks(vm, old_block)
	do
		old_block.last = self

		# The beginning of the block is the test of the while
		var block = new BasicBlock
		block.first = self.n_expr
		block.last = self.n_block.as(not null)

		old_block.link(block)
		var b = self.n_block.generate_basicBlocks(vm, block)

		# var new_block = new BasicBlock
		# new_block.first = self
		# new_block.last = self
		# block.link(new_block)

		return b
	end
end

redef class ALoopExpr
	redef fun compute_ssa(vm)
	do
		self.n_block.compute_ssa(vm)
	end

	redef fun generate_basicBlocks(vm, old_block)
	do
		old_block.last = self

		# The beginning of the block is the first instruction
		var block = new BasicBlock
		block.first = self.n_block.as(not null)
		block.last = self.n_block.as(not null)

		old_block.link(block)
		self.n_block.generate_basicBlocks(vm, block)

		return block
	end
end

redef class AForExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		#self.n_block.compute_ssa(vm)
		old_block.last = self

		# The beginning of the block is the first instruction
		var block = new BasicBlock
		block.first = self.n_block.as(not null)
		block.last = self.n_block.as(not null)

		old_block.link(block)
		self.n_block.generate_basicBlocks(vm, block)

		return block
	end
end

# TODO : récolter les new dans une propriété locale
