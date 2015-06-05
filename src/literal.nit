# This file is part of NIT ( http://www.nitlanguage.org ).
#
# Copyright 2012 Jean Privat <jean@pryen.org>
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

# Parsing of literal values in the abstract syntax tree.
module literal

import phase

redef class ToolContext
	# Parses literal values in the whole AST and produces errors if needed
	var literal_phase: Phase = new LiteralPhase(self, null)
end

private class LiteralPhase
	super Phase

	redef fun process_nmodule(nmodule) do nmodule.do_literal(toolcontext)
end

redef class AModule
	# Visit the module to compute the real value of the literal-related node of the AST.
	# Warnings and errors are displayed on the toolcontext.
	fun do_literal(toolcontext: ToolContext)
	do
		var v = new LiteralVisitor(toolcontext)
		v.enter_visit(self)
	end
end

private class LiteralVisitor
	super Visitor

	var toolcontext: ToolContext

	redef fun visit(n)
	do
		n.accept_literal(self)
		n.visit_all(self)
	end
end

redef class ANode
	private fun accept_literal(v: LiteralVisitor) do end
end

redef class AExpr
	# Get `self` as a `String`.
	# Return null if not a string.
	fun as_string: nullable String
	do
		if not self isa AStringFormExpr then return null
		return self.value.as(not null)
	end

	# Get `self` as an `Int`.
	# Return null if not an integer.
	fun as_int: nullable Int
	do
		if not self isa AIntExpr then return null
		return self.value.as(not null)
	end

	# Get `self` as a single identifier.
	# Return null if not a single identifier.
	fun as_id: nullable String
	do
		if self isa AMethidExpr then
			return self.collect_text
		end
		if not self isa ACallExpr then return null
		if not self.n_expr isa AImplicitSelfExpr then return null
		if not self.n_args.n_exprs.is_empty then return null
		return self.n_id.text
	end
end

redef class Text
	private fun remove_underscores: Text do
		var b = new FlatBuffer
		for i in chars do
			if i == '_' then continue
			b.add i
		end
		return b
	end
end

redef class AIntExpr
	# The value of the literal int once computed.
	var value: nullable Int
end

redef class ADecIntExpr
	redef fun accept_literal(v)
	do
		value = self.n_number.text.to_i
	end
end

redef class AHexIntExpr
	redef fun accept_literal(v)
	do
		var s = self.n_hex_number.text.substring_from(2).remove_underscores
		if s.is_empty then
			v.toolcontext.error(location, "Error: invalid hexadecimal literal")
			return
		end
		value = s.to_hex
	end
end

redef class ABinIntExpr
	redef fun accept_literal(v)
	do
		var s = self.n_bin_number.text.substring_from(2).remove_underscores
		if s.is_empty then
			v.toolcontext.error(location, "Error: invalid binary literal")
			return
		end
		value = s.to_bin
	end
end

redef class AOctIntExpr
	redef fun accept_literal(v)
	do
		var s = self.n_oct_number.text.substring_from(2).remove_underscores
		if s.is_empty then
			v.toolcontext.error(location, "Error: invalid octal literal")
			return
		end
		value = s.to_oct
	end
end

redef class AByteExpr
	# The value of the literal int once computed.
	var value: nullable Byte
end

redef class ADecByteExpr
	redef fun accept_literal(v)
	do
		var t = self.n_bytenum.text
		value = t.substring(0, t.length - 2).to_i.to_b
	end
end

redef class AHexByteExpr
	redef fun accept_literal(v)
	do
		var t = self.n_hex_bytenum.text
		var s = t.substring(2, t.length - 4).remove_underscores
		if s.is_empty then
			v.toolcontext.error(location, "Error: invalid hexadecimal literal")
			return
		end
		value = s.to_hex.to_b
	end
end

redef class ABinByteExpr
	redef fun accept_literal(v)
	do
		var t = self.n_bin_bytenum.text
		var s = t.substring(2, t.length - 4).remove_underscores
		if s.is_empty then
			v.toolcontext.error(location, "Error: invalid binary literal")
			return
		end
		value = s.to_bin.to_b
	end
end

redef class AOctByteExpr
	redef fun accept_literal(v)
	do
		var t = self.n_oct_bytenum.text
		var s = t.substring(2, t.length - 4).remove_underscores
		if s.is_empty then
			v.toolcontext.error(location, "Error: invalid octal literal")
			return
		end
		value = s.to_oct.to_b
	end
end

redef class AFloatExpr
	# The value of the literal float once computed.
	var value: nullable Float
	redef fun accept_literal(v)
	do
		self.value = self.n_float.text.to_f
	end
end

redef class ACharExpr
	# The value of the literal char once computed.
	var value: nullable Char
	redef fun accept_literal(v)
	do
		var txt = self.n_char.text.unescape_nit
		if txt.length != 3 then
			v.toolcontext.error(self.hot_location, "Syntax Error: invalid character literal `{txt}`.")
			return
		end
		self.value = txt.chars[1]
	end
end

redef class AStringFormExpr
	# The value of the literal string once computed.
	var value: nullable String
	redef fun accept_literal(v)
	do
		var txt = self.n_string.text
		var behead = 1
		var betail = 1
		if txt.chars[0] == txt.chars[1] and txt.length >= 6 then
			behead = 3
			betail = 3
			if txt.chars[0] == '"' and txt.chars[3] == '\n' then behead = 4 # ignore first \n in """
		end
		self.value = txt.substring(behead, txt.length - behead - betail).unescape_nit
	end
end
