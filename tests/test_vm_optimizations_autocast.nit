class G[E]
	type V: nullable Object

	fun foo
	do
		bar(1)
		baz(2)
	end

	fun bar(x: E) do x.output
	fun baz(x: V) do x.output
end

class H
	super G[Char]
end

class I
	super G[nullable Object]
	redef type V: Char
end

(new G[Object]).foo
#alt1#(new H).foo
#alt2#(new I).foo
