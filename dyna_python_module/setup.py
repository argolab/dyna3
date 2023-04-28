from setuptools import setup
import os

setup(name='dyna',
      version='0.0.1',
      description='Dyna programming language',
      long_description="""# Dyna
Dyna is a high level declaritive programming language.  Dyna
      """,
      long_description_content_type='text/markdown',
      license='LGPLv3: GNU Lesser General Public License v3 https://www.gnu.org/licenses/lgpl-3.0.en.html',
      author='Matthew Francis-Landau',
      author_email='matthew@matthewfl.com',
      url='http://dyna.org/',
      packages=['dyna'],
      install_requires=[
          'JPype1>=1.3.0',  # java wrapper for calling the JVM
      ],
      package_data = {'dyna': ['*.jar']},
      entry_points = {'console_scripts': [
          'dyna = dyna.start_dyna_repl:start_dyna_repl',
      ]}
     )
