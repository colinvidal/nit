class A
	fun rec: A
	do
		if 2 == 2 then
			return new A
		else
			return rec
		end
	end
end

(new A).rec
