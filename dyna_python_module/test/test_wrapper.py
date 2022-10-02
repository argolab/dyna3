import os
import sys

# sys.path.insert(0, os.path.dirname(__file__))

# from java_wrapper import *

# print('imported java wrapper')


# run('''
# print "hello world".
# ''')

from dyna import Dyna, DynaTerm

print('imported')


t = DynaTerm('test', 1,2,3)
print(t)
print(t.name)
print(t[2])

inst = Dyna()

inst.run('''
print "hello from dyna".
''')

inst.run('''
print str("hello ", $0).
''', 'world')

res = inst.query('''
1 + 2?
''')
assert res[0] == 3

res2 = inst.query('''
1 + $0?
''', 2)

assert res2[0] == 3
