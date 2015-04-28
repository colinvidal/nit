#redef class Object
#	fun foo do end
#end
#
#
class A
	#
#	redef fun foo do end
	fun foo do end
end

#
fun bar(p: A)
do
	p.foo
end

var a1 = new A

a1.foo
bar(a1)

a1.output_class_name
