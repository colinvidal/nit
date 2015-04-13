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

intrude import semantize::scope

redef class VirtualMachine

	var current_propdef: APropdef

	redef fun new_frame(node, mpropdef, args)
	do

		# Compute SSA for method and attribute body
		if node isa AMethPropdef then
			if node.n_block != null then
				current_propdef = node
				# The first step is to generate the basic blocks
				if not node.is_generated then node.generate_basicBlocks(self)
			end
		end

		var sup = super
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

	# Direct predecessors
	var predecessors = new Array[BasicBlock]

	# Parts of AST that contain a read to a variable
	var read_sites = new Array[AVarFormExpr]

	# Parts of AST that contain a write to a variable
	var write_sites = new Array[AVarFormExpr]

	# The iterated dominance frontier of this block
	# i.e. the set of blocks this block dominate directly or indirectly
	var dominance_frontier: Array[BasicBlock] = new Array[BasicBlock] is lazy

	# Self is the old block to link to the new
	# The two blocks are not linked if the current ends with a `AReturnExpr` or `ABreakExpr`
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

	# Add the `block` to the dominance frontier of this block
	fun add_df(block: BasicBlock)
	do
		# Add this block recursively in super-blocks to compute the iterated
		# dominance frontier
		dominance_frontier.add(block)

		for successor in block.successors do
			# If this successor has not already been add to the dominance frontier
			if not dominance_frontier.has(successor) then
				add_df(successor)
			end
		end
	end

	fun compute_df
	do
		# Treat each block only one time
		df_computed = true

		for s in successors do
			add_df(s)

			if not s.df_computed then s.compute_df
		end
	end

	# Used to dump the BasicBlock to dot
	var treated: Bool = false

	# If true, the iterated dominance frontier of this block has been computed
	var df_computed: Bool = false

	# Indicate the BasicBlock is newly created and needs to be updated
	var need_update: Bool = false

	# Indicate if the variables renaming step has been made for this block
	var is_renaming: Bool = false

	# The variables that are accessed in this block
	var variables = new Array[Variable] is lazy

	# The PhiFunction this block contains at the beginning
	var phi_functions = new Array[PhiFunction] is lazy
end

redef class Variable
	# The dependences of this variable for SSA-Algorithm
	var dependences = new Array[Couple[Variable, BasicBlock]]

	# The blocks in which this variable is assigned
	var assignment_blocks: Array[BasicBlock] = new Array[BasicBlock] is lazy

	# Part of the program where this variable is read
	var read_blocks: Array[BasicBlock] = new Array[BasicBlock] is lazy

	# The place in AST where this variable has been assigned
	var reaching_def: nullable ANode = null

	# The stack of this variable, used for SSA
	var stack = new Array[Variable] is lazy

	# The original Variable in case of renaming
	var original_variable: nullable Variable = self
end

class PhiFunction
	super Variable

	# The position in the AST of the phi-function
	var block: BasicBlock

	# Set the dependences for the phi-function
	# *`block` BasicBlock in which we go through the dominance-frontier
	# *`v` The variable to looking for
	fun add_dependences(block: BasicBlock, v: Variable)
	do
		# Look in which blocks of DF(block) `v` has been assigned
		for b in block.predecessors do
			if v.assignment_blocks.has(b) then
				var dep = new Couple[Variable, BasicBlock](v, b)
				dependences.add(dep)
			end
		end
	end

	redef fun to_s: String
	do
		var s = ""
		s += " dependences = [ "
		for d in dependences do
			s += d.first.to_s + " "
		end
		s += "]"

		return s
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
	fun generate_basicBlocks(vm: VirtualMachine) is abstract
end

redef class AExpr
	# Generate recursively basic block for this expression
	# *`vm` Running instance of the virtual machine
	# *`block` A basic block not completely filled
	# Return the newest block
	fun generate_basicBlocks(vm: VirtualMachine, block: BasicBlock): BasicBlock
	do
		print "NOT YET IMPLEMENTED = " + self.class_name
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
		if n_block != null and mpropdef.name == "foo" then
			n_block.generate_basicBlocks(vm, basic_block.as(not null))
		end

		is_generated = true

		# Once basic blocks were generated, compute SSA algorithm
		if is_generated and mpropdef.name == "foo" then
			compute_phi
			rename_variables
		end

		# TODO: debug the foo method
		if mpropdef != null then
			if mpropdef.name == "foo" then
				# Dump the hierarchy in a dot file
				var debug = new BlockDebug(new FileWriter.open("basic_blocks.dot"))
				debug.dump(basic_block.as(not null))

				print phi_functions.length.to_s
				for phi in phi_functions do
					print "{phi}" + phi.to_s
				end

				dump_tree
			end
		end
	end

	# Compute the first phase of SSA algorithm: placing phi-functions
	# NOTE: `generate_basicBlocks` must has been called before
	fun compute_phi
	do
		var root_block = basic_block.as(not null)

		# Compute the iterated dominance frontier of the graph of basic blocks
		root_block.compute_df

		# If the method has a signature
		if n_signature != null then
			# TODO: A Variable must know if it is a parameter
			print "Parameters = " + n_signature.n_params.to_s
		end

		# Places where a phi-function is added per variable
		var phi_blocks = new HashMap[Variable, Array[BasicBlock]]

		# For each variables in the propdef
		for v in variables do
			var phi_variables = new Array[BasicBlock]

			var read_blocks = new Array[BasicBlock]
			read_blocks.add_all(v.read_blocks)

			# While we have not treated each part accessing `v`
			while not read_blocks.is_empty do
				# Remove a block from the set
				var block = read_blocks.shift

				# For each block in the dominance frontier of `block`
				for df in block.dominance_frontier do
					# If we have not yet put a phi-function at the beginning of this block
					if not phi_variables.has(df) then
						phi_variables.add(df)

						# Create a new phi-function and set its dependences
						var phi = new PhiFunction("phi", df)
						phi.add_dependences(df, v)
						phi.block = df
						phi.original_variable = phi

						# Indicate this phi-function is assigned in this block
						phi.assignment_blocks.add(block)
						phi_functions.add(phi)

						# Add a phi-function at the beginning of df for variable v
						df.phi_functions.add(phi)

						if not v.read_blocks.has(df) then read_blocks.add(df)
					end
				end
			end

			# Add `phi-variables` to the global map
			phi_blocks[v] = phi_variables
		end
	end

	# Compute the second phase of SSA algorithm: renaming variables
	# NOTE: `compute_phi` must has been called before
	fun rename_variables
	do
		# A counter for each variable
		# The key is the variable, the value the number of assignment into the variable
		var counter = new HashMap[Variable, Int]

		for v in variables do
			counter[v] = 0
			v.stack.push(v)
		end

		for phi in phi_functions do counter[phi] = 0

		# Launch the recursive renaming from the root block
		rename(basic_block.as(not null), counter)
	end

	#TODO: documentation
	# Rename each variable in this block to comply to SSA-algorithm
	fun rename(block: BasicBlock, counter: HashMap[Variable, Int])
	do
		if block.is_renaming then return

		block.is_renaming = true

		# For each phi-function of this block
		for phi in block.phi_functions do
			generate_name(phi, counter)

			#Replace the phi into the block
			phi = phi.original_variable.stack.last.as(PhiFunction)
		end

		# For each variable write
		for vwrite in block.write_sites do
			generate_name(vwrite.variable.as(not null), counter)

			# Replace the old variable by the last created
			vwrite.variable = vwrite.variable.original_variable.stack.last
		end


		# For each variable read in `block`
		for vread in block.read_sites do
			# Replace the old variable in AST
			vread.variable = vread.variable.original_variable.stack.last
		end

		# Rename occurrence of old names in phi-function
		for successor in block.dominance_frontier do
			for sphi in successor.phi_functions do
				# Go over the couples in the phi dependences to rename variables
				for couple in sphi.dependences do
					if couple.second == block then
						# Rename this variable
						couple.first = couple.first.original_variable.stack.last
					end
				end
			end
		end

		# Recurse in successor blocks
		for successor in block.successors do
			rename(successor, counter)
		end

		# Pop old names off the stack for each phi-function
		for phi in block.phi_functions do
			if not phi.stack.is_empty then phi.stack.pop
		end
	end

	# Generate a new version of the variable `v`
	# *`v` The variable for which we generate a name
	fun generate_name(v: Variable, counter: HashMap[Variable, Int])
	do
		var original_variable = v.original_variable.as(not null)

		print "{original_variable}"
		for key, value in counter do
			print "\t {key} -> {value}"
		end
		var i = counter[original_variable]

		var new_version: Variable

		# Create a new version of Variable
		if original_variable isa PhiFunction then
			var block = original_variable.block
			new_version = new PhiFunction(original_variable.name + i.to_s, block)
			new_version.dependences.add_all(original_variable.dependences)

			block.phi_functions[block.phi_functions.index_of(v.as(PhiFunction))] = new_version
		else
			# Create a new version of variable and replace it in `block`
			new_version = new Variable(original_variable.name + i.to_s)
		end

		# Recopy the fields into the new version
		new_version.location = original_variable.location
		new_version.original_variable = original_variable

		# Push a new version on the stack
		original_variable.stack.add(new_version)
		counter[v] = i + 1
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
		s += "block" + block.to_s.escape_to_dot
		s += "|\{" + block.first.location.file.filename.to_s + block.first.location.line_start.to_s
		s += " | " + block.first.to_s.escape_to_dot

		# Print phi-functions if any
		for phi in block.phi_functions do
			s += " | " + phi.to_s.escape_to_dot + " "
		end

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

# Used to factorize work on loop
# Superclass of loops expressions
class ALoopHelper
end

redef class AVarFormExpr
	# The original variable
	var original_variable: nullable Variable = variable
end

# TODO: treat attribute blocks
redef class AAttrPropdef
	redef fun generate_basicBlocks(vm)
	do
	end
end

redef class AVarExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		self.variable.as(not null).read_blocks.add(old_block)
		old_block.variables.add(self.variable.as(not null))

		self.variable.as(not null).original_variable = self.variable.as(not null)
		# Save this read site in the block
		old_block.read_sites.add(self)

		return old_block
	end
end

redef class AVardeclExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		var decl = self.variable.as(not null)

		# Add the corresponding variable to the enclosing mpropdef
		vm.current_propdef.variables.add(decl)

		decl.original_variable = decl
		decl.assignment_blocks.add(old_block)
		old_block.variables.add(decl)

		return self.n_expr.generate_basicBlocks(vm, old_block)
	end
end

redef class AVarAssignExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		self.variable.as(not null).assignment_blocks.add(old_block)
		old_block.variables.add(self.variable.as(not null))

		self.variable.as(not null).original_variable = self.variable.as(not null)
		# Save this write site in the block
		old_block.write_sites.add(self)

		return self.n_value.generate_basicBlocks(vm, old_block)
	end
end

redef class AVarReassignExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		#self.variable.as(not null).read_blocks.add(old_block)
		self.variable.as(not null).assignment_blocks.add(old_block)

		old_block.variables.add(self.variable.as(not null))
		self.variable.as(not null).original_variable = self.variable.as(not null)
		# Save this write site in the block
		old_block.write_sites.add(self)

		return self.n_value.generate_basicBlocks(vm, old_block)
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
			if first isa ALoopHelper then
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

# TODO : memoize returns
redef class AReturnExpr
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
	# redef fun compute_ssa(vm)
	# do
	# 	self.n_expr.compute_ssa(vm)
	# 	self.n_expr2.compute_ssa(vm)
	# end
end

redef class AImpliesExpr
	# redef fun compute_ssa(vm)
	# do
	# 	self.n_expr.compute_ssa(vm)
	# 	self.n_expr2.compute_ssa(vm)
	# end
end

redef class AAndExpr
	# redef fun compute_ssa(vm)
	# do
	# 	self.n_expr.compute_ssa(vm)
	# 	self.n_expr2.compute_ssa(vm)
	# end
end

redef class ANotExpr
	# redef fun compute_ssa(vm)
	# do
	# 	self.n_expr.compute_ssa(vm)
	# end
end

redef class AOrElseExpr
	# redef fun compute_ssa(vm)
	# do
	# 	self.n_expr.compute_ssa(vm)
	# 	self.n_expr2.compute_ssa(vm)
	# end
end

redef class AArrayExpr
	# redef fun compute_ssa(vm)
	# do
	# 	for nexpr in self.n_exprs do nexpr.compute_ssa(vm)
	# end
end

redef class ASuperstringExpr
	# redef fun compute_ssa(vm)
	# do
	# 	for nexpr in self.n_exprs do nexpr.compute_ssa(vm)
	# end
end

redef class ACrangeExpr
	# redef fun compute_ssa(vm)
	# do
	# 	self.n_expr.compute_ssa(vm)
	# 	self.n_expr2.compute_ssa(vm)
	# end
end

redef class AOrangeExpr
	# redef fun compute_ssa(vm)
	# do
	# 	self.n_expr.compute_ssa(vm)
	# 	self.n_expr2.compute_ssa(vm)
	# end
end

redef class AIsaExpr
	# redef fun compute_ssa(vm)
	# do
	# 	self.n_expr.compute_ssa(vm)
	# end
end

redef class AAsCastExpr
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
end

redef class AAsNotnullExpr
# 	redef fun expr(v)
# 	do
# 		var i = v.expr(self.n_expr)
# 		if i == null then return null
# 		if i.mtype isa MNullType then
# 			fatal(v, "Cast failed")
# 		end
# 		return i
# 	end
end

redef class AParExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		return self.n_expr.generate_basicBlocks(vm, old_block)
	end
end

redef class AOnceExpr
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
end

#TODO: for send expression, store them into the model
redef class ASendExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		# A call does not finish the current block
		# because we create intra-procedural basic blocks here

		# Recursively goes into arguments to find variables if any
		for e in self.raw_arguments do e.generate_basicBlocks(vm, old_block)

		# We do not need to recurse over the arguments since
		return self.n_expr.generate_basicBlocks(vm, old_block)
	end
end

redef class ASendReassignFormExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		self.n_expr.generate_basicBlocks(vm, old_block)

		# Recursively goes into arguments to find variables if any
		for e in self.raw_arguments do e.generate_basicBlocks(vm, old_block)

		return self.n_value.generate_basicBlocks(vm, old_block)
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

# TODO: Store the new into the model
redef class ANewExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		for e in self.n_args.n_exprs do e.generate_basicBlocks(vm, old_block)

		return old_block
	end
end

# TODO: Store attribute access sites in model
redef class AAttrExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		return self.n_expr.generate_basicBlocks(vm, old_block)
	end
end

redef class AAttrAssignExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		return self.n_expr.generate_basicBlocks(vm, old_block)
	end
end

redef class AAttrReassignExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		return self.n_expr.generate_basicBlocks(vm, old_block)
	end
end

redef class AIssetAttrExpr
	redef fun generate_basicBlocks(vm, old_block)
	do
		return self.n_expr.generate_basicBlocks(vm, old_block)
	end
end

redef class ABlockExpr
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

			# Apply a special treatment for loops
			# TODO: finish the comment
			if last_block.last isa ALoopHelper then last_block.successors.add(current_block)

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
	redef fun generate_basicBlocks(vm, old_block)
	do
		# Terminate the previous block
		old_block.last = self

		# We start two new blocks if the if has two branches
		var block_then = new BasicBlock

		# Launch the recursion in two successors if they exist
		if self.n_then != null then
			old_block.link(block_then)

			block_then.first = self.n_then.as(not null)
			block_then.last = self.n_then.as(not null)
			self.n_then.generate_basicBlocks(vm, block_then)
		end

		var block_else = new BasicBlock

		if self.n_else != null then
			old_block.link(block_else)

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

# TODO : same as AIfExpr
redef class AIfexprExpr
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
	super ALoopHelper

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
	super ALoopHelper

	redef fun generate_basicBlocks(vm, old_block)
	do
		old_block.last = self

		# The beginning of the block is the test of the while
		var block = new BasicBlock
		block.first = self.n_expr
		block.last = self.n_block.as(not null)

		old_block.link(block)

		return self.n_block.generate_basicBlocks(vm, block)
	end
end

redef class ALoopExpr
	super ALoopHelper

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
	super ALoopHelper

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
