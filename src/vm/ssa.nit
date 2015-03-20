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
	var assignement_blocks: HashSet[ANode] = new HashSet[ANode] is lazy
end

redef class AExpr
	public fun compute_ssa(vm: VirtualMachine) do end

	# Return the closer block that contains this expression
	fun declaring_block: ABlockExpr
	do
		var declaring_block: ANode = parent.as(not null)

		while not declaring_block isa ABlockExpr do declaring_block = declaring_block.parent.as(not null)

		return declaring_block
	end
end

redef class APropdef

	# The variables contained in the body on this propdef
	var variables: HashSet[Variable] = new HashSet[Variable] is lazy

	# Assign a position in the environment to each local variable of `mpropdef`
	# *`v` The current VirtualMachine
	# *`mpropdef` The method for which we want to compute SSA
	public fun compute_ssa(vm: VirtualMachine) do end
end

redef class AMethPropdef
	redef fun compute_ssa(vm)
	do
		# TODO : handle self
		if n_block != null then n_block.compute_ssa(vm)

		# SSA-Algorithm
		# Once we have collected all data to compute SSA
		for v in variables do
			print "\t {v}"
			for bb in v.assignement_blocks do
				print "assignement in = \t\t{bb}"
			end
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
		self.variable.as(not null).assignement_blocks.add(declaring_block)
	end
end

redef class AVarReassignExpr
	redef fun compute_ssa(vm)
	do
		self.variable.as(not null).assignement_blocks.add(declaring_block)
	end
end

redef class ABlockExpr

	# The dominance frontier of this block
	# i.e. the set of blocks this block dominate
	var dominates: HashSet[ABlockExpr] = new HashSet[ABlockExpr] is lazy

	redef fun compute_ssa(vm)
	do
		for e in self.n_expr do e.compute_ssa(vm)
	end
end

redef class AIfExpr
	redef fun compute_ssa(vm)
	do
		self.n_then.compute_ssa(vm)
		self.n_else.compute_ssa(vm)
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

redef class AArrayExpr
	redef fun compute_ssa(vm)
	do
		for nexpr in self.n_exprs do nexpr.compute_ssa(vm)
	end
end
