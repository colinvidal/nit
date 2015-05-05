module test_vm_optimizations_lit

redef class Int
	fun foo: Int do return 1 end
end
#
#redef class String
#	fun foo do end
#end
#
1.foo.foo

var i = 4

i.foo

#"abc".foo
