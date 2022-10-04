from setuptools import setup
import os

setup(name='dyna',
      version='0.1.0',
      description='Dyna programming language',
      author='Matthew Francis-Landau',
      author_email='matthew@matthewfl.com',
      url='http://dyna.org/',
      packages=['dyna'],
      install_requires=[
          'JPype1>=1.3.0',  # java wrapper for calling the JVM
      ],
      package_data = {'dyna': ['*.jar']}
     )
