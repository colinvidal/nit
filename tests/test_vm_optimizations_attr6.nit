class A
	var foo: Int = 1
	var bar: Int = 2
	var baz: Int = 3
	var vaz: Int = 4
end

class B
	super A
	redef fun foo: Int do return super + 10
	redef fun bar=(i: Int)
	do
		'#'.output
		i.output
		super(i+20)
	end
	redef fun baz: Int do return super + 30
	redef fun baz=(i: Int)
	do
		'#'.output
		i.output
		super(i+30)
	end
	redef var vaz: Int = 40 is redef writable
end

var b = new B
b.foo.output

var c = b.foo
c.output

b.foo = 100
b.foo.output
'\n'.output
b.bar.output
b.bar = 200
#b.bar.output
#'\n'.output
#b.baz.output
#b.baz = 300
#b.baz.output
#'\n'.output
#b.vaz.output
#b.vaz = 400
#b.vaz.output
