class A
	fun m do end
	var x = 5
end

class B
	super A
	redef fun m do end
	redef fun x:Int do return super + 6 end
end

redef class Int
	fun foo:Int do return 4 end
end

fun foo: A do 
	return new A
end

fun bar(a: A): A
do
	return a
end

foo.m

var a = new A
bar(a).m

1.foo.foo.foo

var b = new B
b.x.output
