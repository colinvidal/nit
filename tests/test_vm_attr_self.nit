class X
	fun bar do end
end

class Y
	var attr = new X
end

class Z
end

class A
	var attrx: X is noinit
	var attry = new Y
	var attr = 0
#
#	fun attr: Int
#	do
#		attr += 1
#		return attr
#	end

	fun foo
	do
		attrx = new X
		_attrx = new X
		print("{_attrx}")
		print("{attrx}")
#		attr = 0
#		_attr = 1
#		print(_attr)
#		print(attr)
		attry._attr.bar
		print("{attrx}")
	end
end

class B
	super A

	redef var attrx do
		return new X
	end
end

(new A).foo
