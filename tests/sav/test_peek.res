# Thi
# Thi
s file is pa
s file is pa
rt of NIT ( http://www.nitlanguage.org ).
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

var f = new FileReader.open("test_peek.nit")

print f.peek(5)
print f.read(5)

print f.peek(12)
print f.read(12)

print f.read_all

print f.peek(2)

f.close


