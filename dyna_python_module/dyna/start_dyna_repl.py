import os, sys, importlib.resources


def start_dyna_repl():
    jar = importlib.resources.path('dyna', 'dyna.jar')
    if not os.path.exists(jar):
        print('Unable to find dyna runtime')
    os.execv(jar, sys.argv)

if __name__ == '__main__':
    start_dyna_repl()
