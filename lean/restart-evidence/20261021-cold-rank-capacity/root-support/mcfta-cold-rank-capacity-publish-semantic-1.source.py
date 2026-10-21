import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
tag, module, strict, message = sys.argv[1:]
source = ROOT / 'lean/MicroCFTA' / (module + '.lean')
receipt = json.loads((HERE / (strict + '.json')).read_text())
assert receipt['exit_code'] == 0 and not (HERE / (strict + '.log')).read_bytes()
assert hashlib.sha256(source.read_bytes()).hexdigest() == receipt['sha256']
audit = ROOT / 'lean/MicroCFTA/Audit.lean'
line = 'import MicroCFTA.' + module + '\n'
assert audit.read_text().count(line) == 1
marker = '/-!\n# Proof dependency audit\n'
assert audit.read_text().count(marker) == 1
assert audit.read_text().index(line) < audit.read_text().index(marker)
audit_receipt = json.loads((HERE / 'audit-2.json').read_text())
assert audit_receipt['exit_code'] == 0
assert audit_receipt['command'][-1] == 'MicroCFTA.Audit'
audit_log = (HERE / 'audit-2.log').read_text()
assert 'Build completed successfully' in audit_log
assert not re.search(r'^error', audit_log, re.M)
assert all('InternedFreshOrdinaryClosedCompletion.lean' in warning
           for warning in re.findall(r'^warning:.*$', audit_log, re.M))
files = [str(source.relative_to(ROOT)), str(audit.relative_to(ROOT))]
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)
subprocess.run(['git', 'diff', '--check', '--', *files], cwd=ROOT, check=True)
subprocess.run(['git', 'add', '--', *files], cwd=ROOT, check=True)
assert set(git('diff', '--cached', '--name-only').splitlines()) == set(files)
subprocess.run(['git', 'commit', '--quiet', '-m', message], cwd=ROOT, check=True)
head = git('rev-parse', 'HEAD').strip()
(HERE / ('proof-commit-' + tag + '.txt')).write_text(head + '\n')
env = {**os.environ, 'GIT_SSH_COMMAND': 'ssh -p 443 -o Hostname=ssh.github.com -o HostKeyAlias=github.com -o StrictHostKeyChecking=yes -o ConnectTimeout=15 -o ConnectionAttempts=1 -o BatchMode=yes -o ServerAliveInterval=10 -o ServerAliveCountMax=2'}
with (HERE / ('proof-push-' + tag + '.log')).open('xb') as log:
    subprocess.run(['timeout', '45s', 'git', 'push', 'origin', 'HEAD:formalize'],
                   cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
remote = subprocess.check_output(['timeout', '45s', 'git', 'ls-remote', 'origin',
                                 'refs/heads/formalize', 'refs/heads/main'], cwd=ROOT, env=env, text=True)
(HERE / ('proof-remote-' + tag + '.txt')).write_text(remote)
assert head + '\trefs/heads/formalize' in remote
assert '794903b3fbad3becb8b28736fc33463760731fc7\trefs/heads/main' in remote
print(json.dumps({'status': 'PASS', 'proof': head, 'remote_equal': True}))
