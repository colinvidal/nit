class A
	var foo: Object is lazy do
		1.output
		do
			2.output
			if true then break
			3.output
		end
		return 4
	end

	var bar: Object = baz is lazy

	fun baz: Object do
		10.output
		do
			20.output
			if true then break
			30.output
		end
		return 40
	end
end

var a = new A
a.foo.output
a.bar.output

'\n'.output

var na: nullable A = a
na.foo.output
na.bar.output
