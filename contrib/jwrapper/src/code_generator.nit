# This file is part of NIT (http://www.nitlanguage.org).
#
# Copyright 2014 Frédéric Vachon <fredvac@gmail.com>
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

# Services to generate extern class `in "Java"`
module code_generator

intrude import model

class CodeGenerator

	var with_attributes: Bool
	var comment_unknown_types: Bool
	var file_out: FileWriter
	var java_class: JavaClass
	var nb_params: Int
	var module_name: nullable String = null

	init (file_name: String, jclass: JavaClass, with_attributes, comment: Bool)
	do
		file_out = new FileWriter.open(file_name)

		var nit_ext = ".nit"
		if file_name.has_suffix(nit_ext) then
			# Output file ends with .nit, we expect it to be a valid name
			module_name = file_name.strip_extension(nit_ext)

			# Otherwise, it may be anything so do not declare a module
		end

		self.java_class = jclass
		self.with_attributes = with_attributes
		self.comment_unknown_types = comment
	end

	fun generate
	do
		var jclass = self.java_class

		var class_content = new Array[String]
		class_content.add(gen_class_header(jclass.class_type))

		if with_attributes then
			for id, jtype in jclass.attributes do class_content.add(gen_attribute(id, jtype))
		end

		for id, methods_info in jclass.methods do
			for method_info in methods_info do
				var nid = id
				if methods_info.length > 1 then nid += "{methods_info.index_of(method_info)}"
				class_content.add gen_method(id, nid, method_info.return_type, method_info.params)
			end
		end
		class_content.add("\nend\n")

		var wrappers = new Array[String]
		for jtype in jclass.unknown_types do
			if jtype == jclass.class_type then continue
			wrappers.add("\n")
			wrappers.add(gen_unknown_class_header(jtype))
		end

		var imports = new Array[String]
		imports.add("import mnit_android\n")
		for import_ in jclass.imports do
			imports.add("import android::{import_}\n")
		end

		file_out.write(gen_licence)

		var module_name = module_name
		if module_name != null then file_out.write "module {module_name}\n"

		file_out.write("\n")
		file_out.write(imports.join(""))
		file_out.write("\n")
		file_out.write(class_content.join(""))
		file_out.write(wrappers.join(""))
	end

	fun gen_licence: String
	do
		return """
# This file is part of NIT (http://www.nitlanguage.org).
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

# This code has been generated using `jwrapper`
"""
	end

	fun gen_class_header(jtype: JavaType): String
	do
		var temp = new Array[String]
		temp.add("extern class Native{jtype.id} in \"Java\" `\{ {jtype} `\}\n")
		temp.add("\tsuper JavaObject\n\n")

		return temp.join("")
	end

	fun gen_unknown_class_header(jtype: JavaType): String
	do
		var nit_type: NitType
		if jtype.extern_name.has_generic_params then
			nit_type = jtype.extern_name.generic_params.first
		else
			nit_type = jtype.extern_name
		end

		var temp = new Array[String]
		temp.add("extern class {nit_type} in \"Java\" `\{ {jtype.to_package_name} `\}\n")
		temp.add("\tsuper JavaObject\n\nend\n")

		return temp.join("")
	end

	fun gen_attribute(jid: String, jtype: JavaType): String
	do
		return "\tvar {jid.to_nit_method_name}: {jtype.to_nit_type}\n"
	end

	fun gen_method(jmethod_id: String, nmethod_id: String, jreturn_type: JavaType, jparam_list: Array[JavaType]): String
	do
		var java_params = ""
		var nit_params  = ""
		var nit_id = "arg"
		var nit_id_no = 0
		var nit_types = new Array[NitType]
		var comment = ""

		# Parameters
		for i in [0..jparam_list.length[ do
			var jparam = jparam_list[i]
			var nit_type = jparam.to_nit_type

			if not nit_type.is_complete then
				if jparam.is_wrapped then
					java_class.imports.add nit_type.mod.as(not null)
				else
					if comment_unknown_types then
						comment = "#"
					else
						nit_type = jparam.extern_name
						java_class.unknown_types.add(jparam)
					end
				end
			end

			var cast = ""

			if not jparam.is_collection then cast = jparam.param_cast

			nit_types.add(nit_type)
			nit_type.arg_id = "{nit_id}{nit_id_no}"

			if i == jparam_list.length - 1 then
				java_params += "{cast}{nit_id}{nit_id_no}"
				nit_params  += "{nit_id}{nit_id_no}: {nit_type}"
			else
				java_params += "{cast}{nit_id}{nit_id_no}" + ", "
				nit_params  += "{nit_id}{nit_id_no}: {nit_type}, "
			end

			nit_id_no += 1
		end

		# Method identifier
		var method_id = nmethod_id.to_nit_method_name
		var nit_signature = new Array[String]

		nit_signature.add "\tfun {method_id}"

		if not jparam_list.is_empty then
			nit_signature.add "({nit_params})"
		end

		var return_type = null

		if not jreturn_type.is_void then
			return_type = jreturn_type.to_nit_type

			if not return_type.is_complete then
				if jreturn_type.is_wrapped then
					java_class.imports.add return_type.mod.as(not null)
				else
					if comment_unknown_types then
						comment = "#"
					else
						return_type = jreturn_type.extern_name
						java_class.unknown_types.add(jreturn_type)
					end
				end
			end

			nit_signature.add ": {return_type} "
		end

		var temp = new Array[String]

		temp.add(comment + nit_signature.join(""))

		# FIXME : This huge `if` block is only necessary to copy primitive arrays as long as there's no better way to do it
		if comment == "#" then
			temp.add(" in \"Java\" `\{\n{comment}\t\tself.{jmethod_id}({java_params});\n{comment}\t`\}\n")
		# Methods with return type
		else if return_type != null then
			temp.add(" in \"Java\" `\{\n{comment}\t\treturn {jreturn_type.return_cast}self.{jmethod_id}({java_params});\n{comment}\t`\}\n")
		# Methods without return type
		else if jreturn_type.is_void then
			temp.add(" in \"Java\" `\{\n{comment}\t\tself.{jmethod_id}({java_params});\n{comment}\t`\}\n")
		# No copy
		else
			temp.add(" in \"Java\" `\{\n{comment}\t\tself.{jmethod_id}({java_params});\n{comment}\t`\}\n")
		end

		return temp.join("")
	end
end

redef class String
	# Convert the Java method name `self` to the Nit style
	#
	# * Converts to snake case
	# * Strips `Get` and `Set`
	# * Add suffix `=` to setters
	fun to_nit_method_name: String
	do
		var name = self.to_snake_case
		if name.has_prefix("get_") then
			name = name.substring_from(4)
		else if name.has_prefix("set_") then
			name = name.substring_from(4) + "="
		end

		return name
	end
end
