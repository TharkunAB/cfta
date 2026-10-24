"""Check observer evidence, public statements, and preservation of earlier work."""
import argparse
import gzip
import hashlib
import json
import re
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root', type=Path, required=True)
root = parser.parse_args().root.resolve()
here = root / 'lean/restart-evidence/20261024-partial-congruence'
baseline = '51505458d39a58890f837393a338855a5523de57'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def load(name):
    return json.loads((here / name).read_text())

def git(*args):
    return subprocess.check_output(['git', *args], cwd=root)

manifest = {}
for line in (here / 'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ', 1)
    assert name not in manifest and not Path(name).is_absolute() and '..' not in Path(name).parts
    manifest[name] = digest
actual = {p.relative_to(here).as_posix() for p in here.rglob('*') if p.is_file()}
assert actual == set(manifest) | {'SHA256SUMS'}
for name, digest in manifest.items():
    assert sha((here / name).read_bytes()) == digest, name

tree = gzip.decompress((here / 'work/baseline-tree.txt.gz').read_bytes())
assert tree == git('ls-tree', '-r', '-z', baseline)
assert sha(tree) == load('work/baseline.json')['tree_sha256']
changes = load('work/document-changes.json')
audit_change = load('work/audit-addition.json')
changed = []
count = 0
for raw in tree.split(b'\0'):
    if not raw:
        continue
    metadata, raw_name = raw.split(b'\t', 1)
    mode, kind, blob = metadata.decode().split()
    name = raw_name.decode()
    path = root / name
    assert kind == 'blob'
    assert ('100755' if path.stat().st_mode & 0o111 else '100644') == mode, name
    data = path.read_bytes()
    if name in changes:
        changed.append(name)
        change = changes[name]
        assert sha(data) == change['after_sha256'], name
        text = data.decode()
        index, addition = change['insertion_character'], change['inserted']
        assert text[index:index + len(addition)] == addition, name
        data = (text[:index] + text[index + len(addition):]).encode()
        assert sha(data) == change['before_sha256'], name
    elif name == 'lean/MicroCFTA/Audit.lean':
        changed.append(name)
        addition = audit_change['prefix'].encode()
        assert data.startswith(addition) and sha(data) == audit_change['after_sha256']
        data = data[len(addition):]
        assert sha(data) == audit_change['before_sha256']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob, name
    count += 1
assert count == 126923 and len(changed) == 10 and len(changes) == 9
assert git('stash', 'list', '--format=%gd %H %s') == (here / 'work/baseline-stashes.txt').read_bytes()
worktrees = (here / 'work/baseline-worktrees.txt').read_bytes()
assert git('worktree', 'list', '--porcelain') == worktrees.replace(
    b'HEAD ' + baseline.encode(), b'HEAD ' + git('rev-parse', 'HEAD').strip(), 1)
for line in (here / 'work/baseline-refs.txt').read_text().splitlines():
    value, ref = line.split()
    if ref not in ['refs/heads/formalize', 'refs/remotes/origin/formalize']:
        assert git('rev-parse', ref).decode().strip() == value, ref

sources = {
    'EnumerationRootObservation': 'root-read-check-1',
    'EnumerationPartialCongruence': 'paired-check-2',
    'EnumerationPartialTransport': 'transport-check-3',
    'EnumerationPartialRoot': 'root-render-check-1',
}
for name, attempt in sources.items():
    data = (root / 'lean/MicroCFTA' / (name + '.lean')).read_bytes()
    assert data == (here / 'production-sources' / (name + '.lean')).read_bytes()
    assert data == (here / 'work' / attempt / 'checked.lean').read_bytes()
    assert not re.search(rb'\b(?:sorry|admit|axiom|unsafe)\b', data), name
assert (here / 'current-note.md').read_bytes() == (root / 'lean/notes-current-partial-congruence.md').read_bytes()
findings = (root / 'FINDINGS.md').read_text()
assert findings.index('## Haskell fix handoff for external work') < findings.index('## Partial rendering:')
main = load('work/main-verification.json')
assert main['main'] == 'a5fbb66eec52b8c28a4beacd982f00626c9e279a'
assert main['main_is_ancestor'] and main['new_upstream_commits'] == []
subprocess.run(['git', 'merge-base', '--is-ancestor', main['main'], 'HEAD'], cwd=root, check=True)

reports = list((here / 'work').glob('*/report.json'))
assert len(reports) == 11
for path in reports:
    report = json.loads(path.read_text())
    raw = (path.parent / 'raw.log').read_bytes()
    assert sha(raw) == report['raw_sha256'] and len(raw) == report['raw_bytes']
    if 'source_sha256' in report:
        assert sha((path.parent / 'checked.lean').read_bytes()) == report['source_sha256']
        assert '-DwarningAsError=true' in report['command'] and '-Dlinter.all=true' in report['command']
for path in reports:
    name = path.parent.name
    assert json.loads(path.read_text())['exit_code'] == (1 if name in ['paired-check-1', 'transport-check-1', 'transport-check-2'] else 0)
for name in sources.values():
    assert (here / 'work' / name / 'raw.log').read_bytes() == b''
audit = (here / 'work/audit-1/raw.log').read_text()
assert 'Checked axiom dependencies of 75775 MicroCFTA theorems.' in audit
assert 'Build completed successfully (3671 jobs).' in audit
assert len(re.findall(r'^warning:', audit, re.M)) == 1
assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in audit
public = (here / 'work/public-1/raw.log').read_text()
decls = load('work/public-declarations.json')
assert re.findall(r'^@?(MicroCFTA\.[\w.]+) :', public, re.M) == decls['declarations']
assert len(decls['declarations']) == 11 and len(public.encode()) == 9229
axioms = re.findall(r"'(MicroCFTA\.[^']+)' (?:depends on axioms: \[(.*?)\]|(does not depend on any axioms))", public, re.S)
assert [name for name, _, _ in axioms] == decls['theorems'] and len(axioms) == 11
for _, names, empty in axioms:
    assert empty or {name.strip().split('.{', 1)[0] for name in names.split(',')} <= {'propext', 'Quot.sound'}
limits = list((here / 'inputs').glob('*.limits.json'))
assert len(limits) == 11
for path in limits:
    assert json.loads(path.read_text()) == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
for path in (here / 'inputs').glob('*.usage.json'):
    usage = json.loads(path.read_text())
    assert 0 <= usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
print(json.dumps(dict(status='PASS', baseline=baseline, baseline_files=count,
                      unchanged_files=count-len(changed), exact_changed_files=changed,
                      new_modules=len(sources), retained_lean_attempts=len(reports),
                      public_signatures=11, axiom_reports=11, sealed_files=len(manifest),
                      new_compiler_jobs=0, goal='ACTIVE_INCOMPLETE'), indent=2))
