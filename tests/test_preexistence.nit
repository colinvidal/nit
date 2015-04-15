import end

enum Int
	fun output is intern
end

fun foo do 2.output
fun bar(i: Int) do i.output
fun barR(i: Int): Int do return i

1.output

bar(3)

self.bar(3)

var test = self
test.bar(5)
test.bar(6)

barR(4).output
