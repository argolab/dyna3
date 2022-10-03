from dyna import Dyna, DynaTerm

t = DynaTerm('test', 1,2,3)
print(t)
# print(t.name)
# print(t[2])
assert t.name == 'test'
assert t[2] == 3
assert str(t) == 'test(1, 2, 3)'

inst = Dyna()

inst.run('''
print "hello from dyna".
''')

inst.run('''
print str("hello ", $0).
''', 'world')

inst.run('''
assert $0 == "world".
''', 'world')

res = inst.query('''
foo = 123.
1 + 2?
4?
''')
assert res[0] == 3
assert res[1] == 4

res2 = inst.query('''
1 + $0?
''', 2)

assert res2[0] == 3


@inst.define_function()
def my_function(a, b):
    print('my python function called')
    return a*3 + b


res3 = inst.query('''
my_function($0, $1)?
''', 3, 4)

assert res3[0] == my_function(3, 4)


res4 = inst.query('''
&foo(1,2,3) ?
''')
print(res4[0])


res5 = inst.query('''
[1,2,3,4] ?
''')
print(res5[0])
assert type(res5[0]) is list

res6 = inst.query('''
sum([]) = 0.
sum([X|Y]) = X+sum(Y).
sum($0)?
''', [1,2,3])

assert res6[0] == 6

# test passing an opaque value through dyna
class SomeTestClass: pass
val = SomeTestClass()
res7 = inst.query('''
$0 ?
''', val)
assert res7[0] is val
