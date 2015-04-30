class A
	fun foo do end
end

class X
	super A
	redef fun foo do end
end

class Y
	super X
	redef fun foo do end
end
#
#class B
#	super A
#	redef fun foo do end
#end
#
#class C
#	super B
#end
#
#class D
#	super B
#	redef fun foo do end
#end
#
#class E
#	super C
#	super D
#end
#
#class F
#	super E
#	redef fun foo do end
#end

fun test_pos
do
	var x: X

	if 1 == 2 then
		x = new X
	else
		x = new Y
	end

	x.foo
end

var baz = new Y
baz.foo

test_pos
