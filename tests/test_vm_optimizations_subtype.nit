class A
	fun foo do print("foo")
end

class B
	super A
end

class C
	super B
end

var a: A

if 1 == 2 then
	a = new A
else
	a = new C
end

if a isa C then a.foo

if a isa C then
	a.foo
end


a.as(C).foo
