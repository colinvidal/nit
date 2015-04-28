#
class A
	#
	fun foo do end
#	redef fun output_class_name do end
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
