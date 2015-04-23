class A
	fun foo do end
end

class B
	super A
end

class C
	super B 
	redef fun foo do end
end

redef class Int
	fun faz do end
end

fun useA(load: Bool)
do 
	var a: A = new A
	var c: nullable C

	if load then 
		a = new B
	else
		c = new C
	end
end

fun foo do 2.faz
fun bar(i: Int) do i.faz
fun barR(i: Int): Int do return i
fun imbric do barR(barR(5)).faz
fun twoparam(i: Int, j: Int) do j.faz
fun threeparam(i: Int, j: Int, k: Int) do k.faz
fun threeparambis(i: Int, j: Int, k: Int)
do
	k.faz
	i.faz
end

1.faz

bar(3)

self.bar(3)

var aa = new A
aa.foo

useA(false)

var test = self
test.bar(5)
test.bar(6)

barR(4).faz

imbric

twoparam(1,2)

threeparam(1,2,3)

threeparambis(1,2,3)

var a = new A

#useA(true)
var b = new B
b.foo
