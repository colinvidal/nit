# Copyright 2013 Alexandre Terrasa <alexandre@moz-code.org>.
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

all: run

run: hello_world.jar
	java -jar hello_world.jar

hello_world.jar: nitj
	NIT_DIR= ./nitj ../examples/hello_world.nit

nitj:
	NIT_DIR= ./nitg ../src/nitj.nit

clean:
	rm -rf -- hello_world.jar .nit_jcompile 2> /dev/null || true
