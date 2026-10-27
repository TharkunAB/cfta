from pathlib import Path
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-flat-pruning-callback-20261027')
modules = json.loads((area / 'modules.json').read_text())
paths = ['lean/MicroCFTA/' + module + '.lean' for module in modules + ['Audit']]
def git(*args):
    return subprocess.check_output(['git', *args], cwd=root)
assert git('branch', '--show-current').strip() == b'formalize'
assert not git('diff', '--cached', '--name-only', '-z')
subprocess.run(['git', 'diff', '--check'], cwd=root, check=True)
subprocess.run(['git', 'add', '--', *paths], cwd=root, check=True)
staged = git('diff', '--cached', '--name-only', '-z').split(b'\0')
assert {item.decode() for item in staged if item} == set(paths)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
result = subprocess.run(['git', 'commit', '-m', 'Replay concrete pruning callbacks with direct-parent forests'],
    cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True)
(area / 'source-commit.log').write_bytes(result.stdout)
head = git('rev-parse', 'HEAD').decode().strip()
(area / 'source-head.txt').write_text(head + '\n')
print(result.stdout.decode(), end='')
print(json.dumps({'source_head': head, 'files': len(paths)}))
