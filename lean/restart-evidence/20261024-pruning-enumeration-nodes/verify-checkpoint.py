"""Verify the stored enumeration-node checkpoint and the complete preserved baseline."""
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
here = root / 'lean/restart-evidence/20261024-pruning-enumeration-nodes'
baseline = '4c856a02c12a6fa2ff67e7780d5afa709a1a86a5'
main = '74250bd889685da436cdbfe32ac4b5a0878ffd09'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=root)

def load(name):
    return json.loads((here / name).read_text())

manifest = {}
for line in (here / 'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ', 1)
    assert re.fullmatch('[0-9a-f]{64}', digest) and name not in manifest
    assert not Path(name).is_absolute() and '..' not in Path(name).parts
    manifest[name] = digest
assert {p.relative_to(here).as_posix() for p in here.rglob('*') if p.is_file()} == set(manifest) | {'SHA256SUMS'}
for name, digest in manifest.items():
    assert sha((here / name).read_bytes()) == digest, name
proof = load('work/proof-commit.json')['commit']
for commit in [main, proof]:
    subprocess.run(['git', 'merge-base', '--is-ancestor', commit, 'HEAD'], cwd=root, check=True)
assert git('rev-parse', 'origin/main').decode().strip() == main
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
assert git('rev-list', '--parents', '-n', '1', proof).decode().split() == [proof, baseline]
assert set(git('diff-tree', '--no-commit-id', '--name-only', '-r', proof).decode().splitlines()) == {
    'lean/MicroCFTA/SourcePruningEnumerationNodes.lean', 'lean/MicroCFTA/Audit.lean'}
tree = gzip.decompress((here / 'work/baseline-tree.txt.gz').read_bytes())
assert tree == git('ls-tree', '-r', '-z', baseline)
assert sha(tree) == load('work/baseline.json')['tree_sha256']
assert load('work/baseline.json')['head'] == baseline
changes = load('work/document-changes.json')
audit_change = load('work/audit-addition.json')
assert len(changes) == 9
changed = []
count = 0
for raw in tree.split(b'\0'):
    if not raw:
        continue
    metadata, raw_name = raw.split(b'\t', 1)
    mode, kind, blob = metadata.decode().split()
    name = raw_name.decode()
    path = root / name
    data = path.read_bytes()
    assert kind == 'blob' and ('100755' if path.stat().st_mode & 0o111 else '100644') == mode, name
    if name in changes:
        change = changes[name]
        assert sha(data) == change['after_sha256'], name
        text = data.decode()
        position, addition = change['insertion_character'], change['inserted']
        assert text[position:position + len(addition)] == addition, name
        data = (text[:position] + text[position + len(addition):]).encode()
        assert sha(data) == change['before_sha256'], name
        changed.append(name)
    elif name == 'lean/MicroCFTA/Audit.lean':
        addition = audit_change['prefix'].encode()
        assert addition == b'import MicroCFTA.SourcePruningEnumerationNodes\n'
        assert sha(data) == audit_change['after_sha256'] and data.startswith(addition)
        data = data[len(addition):]
        assert sha(data) == audit_change['before_sha256']
        changed.append(name)
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob, name
    count += 1
assert count == 128198 and len(changed) == 10
assert git('stash', 'list', '--format=%gd %H %s') == (here / 'work/baseline-stashes.txt').read_bytes()
worktrees = (here / 'work/baseline-worktrees.txt').read_bytes()
assert git('worktree', 'list', '--porcelain') == worktrees.replace(
    b'HEAD ' + baseline.encode(), b'HEAD ' + git('rev-parse', 'HEAD').strip(), 1)
for line in (here / 'work/baseline-refs.txt').read_text().splitlines():
    value, ref = line.split()
    if ref not in ['refs/heads/formalize', 'refs/remotes/origin/formalize']:
        assert git('rev-parse', ref).decode().strip() == value, ref
assert git('rev-parse', 'codex/backup-pruning-enumeration-nodes-20261024-0456').decode().strip() == baseline

source = (root / 'lean/MicroCFTA/SourcePruningEnumerationNodes.lean').read_bytes()
assert source == (here / 'production-sources/SourcePruningEnumerationNodes.lean').read_bytes()
assert source == (here / 'work/source-check-2/MicroCFTA/SourcePruningEnumerationNodes.lean').read_bytes()
assert sha(source) == '1fb4077739402c31ec48d4bfa8254ef9c1b7453601290dfcd1c0c0031eeee8a4'
assert sha(source) == load('work/installation.json')['source_sha256']
assert len(source.splitlines()) == 76
assert not re.search(rb'\b(?:sorry|admit|axiom|unsafe|set_option)\b', source)
assert re.findall(rb'^(def|theorem) ', source, re.M) == [b'def'] * 2 + [b'theorem'] * 2
text = source.decode()
original = (here / 'work/source-check-1/MicroCFTA/SourcePruningEnumerationNodes.lean').read_text()
assert text.split('/-- Actual cache growth', 1)[0] == original.split('/-- Actual cache growth', 1)[0]

frozen = load('owner-proposal/FROZEN.json')
pins = load('owner-proposal/pins.json')
assert len(pins) == frozen['pinned_files'] == 41 and frozen['compiler_evidence'] is False
assert sha((here / 'owner-proposal/pins.json').read_bytes()) == frozen['pins_sha256']
assert {p.relative_to(here / 'owner-proposal').as_posix() for p in (here / 'owner-proposal').rglob('*') if p.is_file()} == set(pins) | {'pins.json', 'FROZEN.json'}
for name, pin in pins.items():
    assert not Path(name).is_absolute() and '..' not in Path(name).parts
    data = (here / 'owner-proposal' / name).read_bytes()
    assert len(data) == pin['bytes'] and sha(data) == pin['sha256']
contracts = load('owner-proposal/contracts.json')
assert contracts == load('work/body-gate.json')['contracts']
for name, digest in contracts.items():
    data = (here / 'owner-proposal' / name).read_bytes()
    assert sha(data) == digest
    if name != 'context.lean.txt':
        assert text.count(data.decode().rstrip()) == 1
    else:
        stripped = re.sub(r'/\-!.*?\-/', '', text, count=1, flags=re.S)
        lines = [line for line in stripped.splitlines() if line.strip()]
        context = [line for line in data.decode().splitlines() if line.strip()]
        assert lines[:len(context)] == context
sources = load('owner-proposal/source-index.json')['sources']
assert len(sources) == 10
for pin in sources:
    data = (root / pin['repository_path']).read_bytes()
    assert data == (here / 'owner-proposal' / pin['snapshot']).read_bytes()
    assert len(data) == pin['bytes'] and sha(data) == pin['sha256']
    for cut in pin['cuts']:
        part = b''.join(data.splitlines(keepends=True)[cut['start'] - 1:cut['end']])
        assert part == (here / 'owner-proposal' / cut['snapshot']).read_bytes()
        assert len(part) == cut['bytes'] and sha(part) == cut['sha256']

reports = list((here / 'work').glob('*/report.json'))
expected = {f'source-check-{i}' for i in range(1, 3)} | {'installed-build-1', 'audit-1', 'public-1'}
assert {p.parent.name for p in reports} == expected
failed = {'source-check-1'}
for path in reports:
    report = json.loads(path.read_text())
    raw = (path.parent / 'raw.log').read_bytes()
    assert sha(raw) == report['raw_sha256'] and len(raw) == report['raw_bytes']
    assert report['exit_code'] == (1 if path.parent.name in failed else 0)
    if 'source_sha256' in report:
        inputs = list(path.parent.rglob('*.lean'))
        assert len(inputs) == 1 and sha(inputs[0].read_bytes()) == report['source_sha256']
        assert '-DwarningAsError=true' in report['command'] and '-Dlinter.all=true' in report['command']
for name in ['source-check-2']:
    assert (here / 'work' / name / 'raw.log').read_bytes() == b''
audit = (here / 'work/audit-1/raw.log').read_text()
assert 'Checked axiom dependencies of 76095 MicroCFTA theorems.' in audit
assert 'Build completed successfully (3680 jobs).' in audit
assert len(re.findall(r'^warning:', audit, re.M)) == 1 and 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in audit
public = (here / 'work/public-1/raw.log').read_text()
decls = load('work/public-declarations.json')
assert re.findall(r'^@?(MicroCFTA\.[\w.]+)(?=\s)', public, re.M) == decls['declarations']
assert len(decls['declarations']) == 4
axioms = re.findall(r"'(MicroCFTA\.[^']+)' depends on axioms: \[(.*?)\]", public, re.S)
assert [name for name, _ in axioms] == decls['theorems'] and len(axioms) == 2
for _, names in axioms:
    assert {name.strip().split('.{', 1)[0] for name in names.split(',')} == {'propext', 'Quot.sound'}
for suffix in ['limits.json', 'usage.json']:
    paths = list((here / 'inputs').glob('*.' + suffix))
    assert len(paths) == 6
    for path in paths:
        value = json.loads(path.read_text())
        if suffix == 'limits.json':
            assert value == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        else:
            assert 0 <= value['age_seconds'] <= 600 and value['remaining_percent'] > 1
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert (here / 'inputs' / ('mcfta-pruning-enumeration-nodes-20261024-' + name + '-review.md')).is_file()
assert (root / 'lean/notes-current-pruning-enumeration-nodes.md').read_bytes() == (here / 'current-note.md').read_bytes()
findings = (root / 'FINDINGS.md').read_text().split('## Stored enumeration-node handles', 1)[0]
assert '## Haskell fix handoff for external work' in findings and findings.count('| Fixed by ') == 6
assert 'All six repairs are in the imported main history.' in findings
prior = load('previous-publication/remote-publication.json')
assert prior['status'] == 'PUSHED_AND_REMOTE_VERIFIED' and prior['remote_head'] == baseline
assert load('previous-publication/publication-spec.json')['head'] == baseline
print(json.dumps(dict(status='PASS', baseline=baseline, main=main, proof=proof,
    baseline_files=count, unchanged_files=count - len(changed), exact_changed_files=changed,
    new_modules=1, lean_attempts=5, public_signatures=4, axiom_reports=2,
    resource_receipts=6, sealed_files=len(manifest), goal='ACTIVE_INCOMPLETE'), indent=2))
