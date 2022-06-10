import os
import sys

sys.path.insert(0, os.path.dirname(__file__))

from java_wrapper import *

print('imported java wrapper')


run('''
print "hello world".
''')
