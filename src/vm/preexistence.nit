# Compute preexistence of each objets sites in alives methods
module preexistence

import model_optimizations

redef class ToolContext
	# Disable inter-procedural analysis and 'new' cases
	var disable_preexistence_extensions = new OptionBool("Disable preexistence extensions", "--no-preexist-ext")

	redef init
	do
		super
		option_context.add_option(disable_preexistence_extensions)
	end
end

redef class Sys
	# Tell if preexistence extensions are disabled
	var disable_preexistence_extensions: Bool
end

redef class ModelBuilder	
	redef fun run_virtual_machine(mainmodule: MModule, arguments: Array[String])
	do
		sys.disable_preexistence_extensions = toolcontext.disable_preexistence_extensions.value
		super(mainmodule, arguments)
	end
end

redef class VirtualMachine
	redef fun load_class(mclass)
	do
		if mclass.loaded then return
		super(mclass)
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

	# Compute the preexistence of all invocation sites of the method
	# Return true if the method is analysed, false otherwise (already compiled, extern or extern method)
	#
	# WARNING!
	# The VM can't interpret FFI code, so intern/extern methods are not analysed,
	# and a expression using a receiver from intern/extern method is preexistent.
	#
	fun preexist_all(vm: VirtualMachine): Bool
	do
		if compiled or is_intern or is_extern then return false
		compiled = true

		trace("\npreexist_all of {self}")
		var preexist: Int

		if not disable_preexistence_extensions then
			for newexpr in monews do
				assert not newexpr.pattern.cls.mclass_type.is_primitive_type

				preexist = newexpr.preexist_expr
				fill_nper(newexpr)
				trace("\tpreexist of new {newexpr} loaded:{newexpr.pattern.is_loaded} {preexist} {preexist.preexists_bits}")
			end
		end

		for site in mosites do
			assert not site.pattern.rst.is_primitive_type

			preexist = site.preexist_site
			var buff = "\tpreexist of "

			fill_nper(site.expr_recv)

			if site isa MOAttrSite then
				buff += "attr {site.pattern.rst}.{site.pattern.gp}" 
			else if site isa MOSubtypeSite then 
				buff += "cast {site.pattern.rst} isa {site.target}"
			else if site isa MOCallSite then 
				buff += "meth {site.pattern.rst}.{site.pattern.gp}" 
			else
				abort
			end

			buff += " {site.expr_recv}.{site} {preexist} {preexist.preexists_bits}"
			trace(buff)
			trace("\t\tconcretes receivers? {(site.get_concretes.length > 0)}")
		end

		if exprs_preexist_mut.length > 0 then trace("\tmutables pre: {exprs_preexist_mut}")
		if exprs_npreexist_mut.length > 0 then trace("\tmutables nper: {exprs_npreexist_mut}")

		return true
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
		if not disable_preexistence_extensions then new_pattern.set_preexist_newsite
	end
end
