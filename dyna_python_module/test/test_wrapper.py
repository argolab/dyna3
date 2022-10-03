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
1 + 2?
''')
assert res[0] == 3

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
