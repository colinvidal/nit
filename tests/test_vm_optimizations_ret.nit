class A
	fun m do end
end

class B
	super A
	redef fun m do end
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
