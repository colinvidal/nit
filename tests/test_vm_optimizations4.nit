class A
	fun foo do end
end

class B
	super A

	redef fun foo do end
end

class C
	super A

	redef fun foo do end
end

class H
	super C

	redef fun foo do end
end

class D
	super B
end

class E
	super B
end

class F
	super D
	super E
end

class G
	super F

	redef fun foo do end
end

fun after_load
do
	var ac: A
	if 1 == 2 then
		ac = new A
	else
		ac = new C
	end
	ac.foo

	var af = new F
	af.foo

	var b = new B
	b.foo

	var f = new G
	f.foo

	var ch: C
	if 1 == 2 then
		ch = new C
	else
		ch = new H
	end
	ch.foo
end

fun testparam(a: A)
do
	a = new C
	a.foo
end

var ac: A
if 1 == 2 then
	ac = new A
else
	ac = new C
end
ac = new A
ac.foo

var af = new F
af.foo

var b = new B
b.foo

var f = new F
f = new G
f.foo

var h = new H
h.foo

after_load

testparam(ac)
