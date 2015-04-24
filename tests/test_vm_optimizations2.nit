class A
	fun foo do end
	fun bar
	do
		var a = new A
		a.foo

		var c = new C
		c.foo
	end
end

class B
	super A
end

class C
	super B 
	redef fun foo do end
end

var a = new A
a.foo

var b = new B
b.foo

var c = new C
c.foo

var ac: A

if 1 == 2 then
	ac = new A
else
	ac = new C
end

ac.foo

a.bar
