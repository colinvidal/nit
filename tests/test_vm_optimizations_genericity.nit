class A[T: Object]
	var container = new List[T]

	fun info(el: T) do el.hash.output

	fun add(el: T) do
		info(el)
		container.add(el)
	end

	fun del(el: T) do
		info(el)
		container.remove(el)
	end
end

var i = new A[Int]
i.add(4)
i.add(5)
i.del(4)
