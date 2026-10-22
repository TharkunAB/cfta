import runpy
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
arguments = sys.argv[1:]
assert arguments and len(arguments) % 2 == 0
for index in range(0, len(arguments), 2):
    sys.argv = [str(HERE / 'archive-extra.py'), *arguments[index:index + 2]]
    runpy.run_path(str(HERE / 'archive-extra.py'), run_name='__main__')
