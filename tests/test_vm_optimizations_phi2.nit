class A end
class B super A end

fun foo
do
	var baz: A
	var x = 0

	if 1 == 2 then
		if x == 10 then
			baz = new B
			x = 15
		else
			baz = new A
			x = 20
		end

#		print x.to_s + baz.to_s
		x.output
		baz.output
		x = 5
	else
		baz = new A
	end

#	print baz
	baz.output
	baz = new B
	x+= 10

	baz = new A
#	print baz
	baz.output
end

foo
foo
