import hashlib
import json
import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
modules = [('request', 'SourceCurrentNativeRequestPositivePositions'),
           ('current', 'SourceCurrentNativeCurrentStores')]
files = []
for tag, module in modules:
    source = ROOT / 'lean/MicroCFTA' / (module + '.lean')
    receipt = json.loads((HERE / (tag + '-strict-1.json')).read_text())
    assert receipt['exit_code'] == 0 and not (HERE / (tag + '-strict-1.log')).read_bytes()
    assert hashlib.sha256(source.read_bytes()).hexdigest() == receipt['sha256']
    files.append(str(source.relative_to(ROOT)))
old = (HERE / 'native-request-before.lean.txt').read_bytes()
append = (HERE / 'stores/native-request-call-stores-append.lean.txt').read_bytes()
combined = (ROOT / files[0]).read_bytes()
assert combined.count(b'\n' + append) == 1
assert combined.replace(b'\n' + append, b'', 1) == old
audit = ROOT / 'lean/MicroCFTA/Audit.lean'
existing = 'import MicroCFTA.SourceCurrentNativeRequestPositivePositions\n'
line = 'import MicroCFTA.SourceCurrentNativeCurrentStores\n'
text = audit.read_text()
assert text.count(existing) == 1 and line not in text
marker = '/-!\n# Proof dependency audit\n'
assert text.count(marker) == 1
audit.write_text(text.replace(marker, line + marker, 1))
files.append(str(audit.relative_to(ROOT)))
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)
subprocess.run(['git', 'diff', '--check', '--', *files], cwd=ROOT, check=True)
subprocess.run(['git', 'add', '--', *files], cwd=ROOT, check=True)
assert set(git('diff', '--cached', '--name-only').splitlines()) == set(files)
subprocess.run(['git', 'commit', '--quiet', '-m', 'Preserve conditional native stores through completed queries'], cwd=ROOT, check=True)
head = git('rev-parse', 'HEAD').strip()
(HERE / 'proof-commit-stores.txt').write_text(head + '\n')
env = {**os.environ, 'GIT_SSH_COMMAND': 'ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2'}
with (HERE / 'proof-push-stores.log').open('xb') as log:
    subprocess.run(['timeout', '45s', 'git', 'push', 'origin', 'HEAD:formalize'], cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
remote = subprocess.check_output(['timeout', '45s', 'git', 'ls-remote', 'origin', 'refs/heads/formalize', 'refs/heads/main'], cwd=ROOT, env=env, text=True)
(HERE / 'proof-remote-stores.txt').write_text(remote)
assert head + '\trefs/heads/formalize' in remote
assert '794903b3fbad3becb8b28736fc33463760731fc7\trefs/heads/main' in remote
print(json.dumps({'status': 'PASS', 'proof': head, 'remote_equal': True,
                  'old_declarations_byte_exact': True}))
