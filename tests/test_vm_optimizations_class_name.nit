class Test end
class MyArray[E] end

class Toto
	redef fun class_name do return "TotoToto"
end

var test1 = new Test
var test2: Object = new Test
var test3 = new MyArray[Int]
var test4 = new Toto

"".class_name.output
'\n'.output
1.class_name.output
'\n'.output

test1.class_name.output
'\n'.output
test2.class_name.output
'\n'.output
test3.class_name.output
'\n'.output

test4.class_name.output

sys.buffer_mode_line
'\n'.output
