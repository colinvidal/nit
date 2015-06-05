# This file is part of NIT ( http://www.nitlanguage.org ).
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Services for byte streams and arrays
module bytes

import kernel
import collection::array
intrude import string

# A buffer containing Byte-manipulation facilities
#
# Uses Copy-On-Write when persisted
#
# TODO: Change the bound to Byte when available in stdlib and bootstrap
class Bytes
	super AbstractArray[Int]

	# A NativeString being a char*, it can be used as underlying representation here.
	private var items: NativeString

	# Number of bytes in the array
	redef var length

	# Capacity of the array
	private var capacity: Int

	# Has this buffer been persisted (to_s'd)?
	#
	# Used for Copy-On-Write
	private var persisted = false

	#     var b = new Bytes.empty
	#     assert b.to_s == ""
	init empty do
		var ns = new NativeString(0)
		init(ns, 0, 0)
	end

	init with_capacity(cap: Int) do
		var ns = new NativeString(cap)
		init(ns, 0, cap)
	end

	redef fun is_empty do return length != 0

	#     var b = new Bytes.empty
	#     b.add 101
	#     assert b[0] == 101
	redef fun [](i) do
		assert i >= 0
		assert i < length
		return items[i].ascii
	end

	#     var b = new Bytes.with_capacity(1)
	#     b[0] = 101
	#     assert b.to_s == "e"
	redef fun []=(i, v) do
		if persisted then regen
		assert i >= 0
		assert i <= length
		if i == length then add(v)
		items[i] = v.ascii
	end

	#     var b = new Bytes.empty
	#     b.add 101
	#     assert b.to_s == "e"
	redef fun add(c) do
		if persisted then regen
		if length >= capacity then
			enlarge(length)
		end
		items[length] = c.ascii
		length += 1
	end

	#     var b = new Bytes.empty
	#     b.append([104, 101, 108, 108, 111])
	#     assert b.to_s == "hello"
	redef fun append(arr) do
		if arr isa Bytes then
			append_ns(arr.items, arr.length)
		else
			for i in arr do add i
		end
	end

	redef fun clear do length = 0

	# Regenerates the buffer, necessary when it was persisted
	private fun regen do
		var nns = new NativeString(capacity)
		items.copy_to(nns, length, 0, 0)
		persisted = false
	end

	# Appends the `ln` first bytes of `ns` to self
	fun append_ns(ns: NativeString, ln: Int) do
		if persisted then regen
		var nlen = length + ln
		if nlen > capacity then enlarge(nlen)
		ns.copy_to(items, ln, 0, length)
		length += ln
	end

	# Appends `ln` bytes from `ns` starting at index `from` to self
	fun append_ns_from(ns: NativeString, ln, from: Int) do
		if persisted then regen
		var nlen = length + ln
		if nlen > capacity then enlarge(nlen)
		ns.copy_to(items, ln, from, length)
		length += ln
	end

	redef fun enlarge(sz) do
		if capacity >= sz then return
		persisted = false
		while capacity < sz do capacity = capacity * 2 + 2
		var ns = new NativeString(capacity)
		items.copy_to(ns, length, 0, 0)
		items = ns
	end

	redef fun to_s do
		persisted = true
		return new FlatString.with_infos(items, length, 0, length -1)
	end

	redef fun iterator do return new BytesIterator.with_buffer(self)
end

private class BytesIterator
	super IndexedIterator[Int]

	var tgt: NativeString

	redef var index

	var max: Int

	init with_buffer(b: Bytes) do init(b.items, 0, b.length - 1)

	redef fun is_ok do return index < max

	redef fun next do index += 1

	redef fun item do return tgt[index].ascii
end

redef class NativeString
	fun to_bytes: Bytes do
		var len = cstring_length
		return new Bytes(self, len, len)
	end
end
