redef class Int
	fun next: nullable Int do if self < 20 then return self + 1 else return null
end

var t2: nullable Int = 10
t2.output
while t2 != null do
	t2 = t2.next #alt1# t2 = null
	t2 = null
	while t2 != null do
		t2.output
		t2 = t2.next #alt2# t2 = null
	end
	#alt3#t2 = t2.next
end
