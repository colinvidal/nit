class A
	fun foo do end
end

class B
	super A
end

var baz: A

if 1 == 2 then
	if 1 == 2 then
		if 1 == 2 then
			baz = new A
		else
			baz = new B
		end
	else if 1 == 2 then
		if 1 == 2 then
			baz = new A
		else
			baz = new B
		end
	else
		baz = new B
	end
else
	baz = new A
end

baz.foo
