class A
	var foo: X = new X is lazy
end

class X
	fun bar do end
end

fun baz do 
	var a = new A
	a.foo.bar
end

(new A).foo.bar
baz

