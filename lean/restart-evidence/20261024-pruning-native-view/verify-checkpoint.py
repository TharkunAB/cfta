"""Verify the native pruning view checkpoint and the complete preserved baseline."""
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
here = root / 'lean/restart-evidence/20261024-pruning-native-view'
baseline = '4c52896ccff16f4fbf479ac33746b6dbdf438e35'
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
    'lean/MicroCFTA/SourcePruningNativeView.lean', 'lean/MicroCFTA/Audit.lean'}
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
        assert addition == b'import MicroCFTA.SourcePruningNativeView\n'
        assert sha(data) == audit_change['after_sha256'] and data.startswith(addition)
        data = data[len(addition):]
        assert sha(data) == audit_change['before_sha256']
        changed.append(name)
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob, name
    count += 1
assert count == 127982 and len(changed) == 10
assert git('stash', 'list', '--format=%gd %H %s') == (here / 'work/baseline-stashes.txt').read_bytes()
worktrees = (here / 'work/baseline-worktrees.txt').read_bytes()
assert git('worktree', 'list', '--porcelain') == worktrees.replace(
    b'HEAD ' + baseline.encode(), b'HEAD ' + git('rev-parse', 'HEAD').strip(), 1)
for line in (here / 'work/baseline-refs.txt').read_text().splitlines():
    value, ref = line.split()
    if ref not in ['refs/heads/formalize', 'refs/remotes/origin/formalize']:
        assert git('rev-parse', ref).decode().strip() == value, ref
assert git('rev-parse', 'codex/backup-pruning-native-view-20261024-0432').decode().strip() == baseline

source = (root / 'lean/MicroCFTA/SourcePruningNativeView.lean').read_bytes()
assert source == (here / 'production-sources/SourcePruningNativeView.lean').read_bytes()
assert source == (here / 'work/source-check-4/MicroCFTA/SourcePruningNativeView.lean').read_bytes()
assert sha(source) == '0cf2d0d30d1a231dd6a1c53dc8a78bc0b8c37972ff5fe3d55b2767e9f6f98571'
assert sha(source) == load('work/installation.json')['source_sha256']
assert len(source.splitlines()) == 177
assert not re.search(rb'\b(?:sorry|admit|axiom|unsafe|set_option)\b', source)
assert re.findall(rb'^(def|theorem) ', source, re.M) == [b'def'] * 3 + [b'theorem'] * 3
text = source.decode()
original = (here / 'work/source-check-1/MicroCFTA/SourcePruningNativeView.lean').read_text()
assert text.split('/-- Closed source values', 1)[0] == original.split('/-- Closed source values', 1)[0]
start = text.index('/-- A closed non-Mu value')
end = text.index('/-- The Mu-only exemption', start)
assert len(text[start:end].splitlines()) == 23
assert (text[:start] + text[end:]).encode() == (here / 'work/source-check-3/MicroCFTA/SourcePruningNativeView.lean').read_bytes()
header = (here / 'work/emptyAt-completion-header.lean.txt').read_text()
assert text.count(header.rstrip()) == 1
assert sha(header.encode()) == load('work/emptyAt-completion-gate.json')['header_sha256']

frozen = load('owner-proposal/FROZEN.json')
pins = load('owner-proposal/pins.json')
assert len(pins) == frozen['pinned_files'] == 75 and frozen['compiler_evidence'] is False
assert sha((here / 'owner-proposal/pins.json').read_bytes()) == frozen['pins_sha256']
assert {p.relative_to(here / 'owner-proposal').as_posix() for p in (here / 'owner-proposal').rglob('*') if p.is_file()} == set(pins) | {'pins.json', 'FROZEN.json'}
for name, pin in pins.items():
    assert not Path(name).is_absolute() and '..' not in Path(name).parts
    data = (here / 'owner-proposal' / name).read_bytes()
    assert len(data) == pin['bytes'] and sha(data) == pin['sha256']
contracts = load('owner-proposal/contracts.json')
assert contracts == load('work/body-gate.json')['header_contracts']
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
assert len(sources) == 22
for pin in sources:
    data = (root / pin['repository_path']).read_bytes()
    assert data == (here / 'owner-proposal' / pin['snapshot']).read_bytes()
    assert len(data) == pin['bytes'] and sha(data) == pin['sha256']
    for cut in pin['cuts']:
        part = b''.join(data.splitlines(keepends=True)[cut['start'] - 1:cut['end']])
        assert part == (here / 'owner-proposal' / cut['snapshot']).read_bytes()
        assert len(part) == cut['bytes'] and sha(part) == cut['sha256']

reports = list((here / 'work').glob('*/report.json'))
expected = {f'source-check-{i}' for i in range(1, 5)} | {'installed-build-1', 'audit-1', 'public-1', 'public-2'}
assert {p.parent.name for p in reports} == expected
failed = {'source-check-1', 'source-check-2', 'public-1'}
for path in reports:
    report = json.loads(path.read_text())
    raw = (path.parent / 'raw.log').read_bytes()
    assert sha(raw) == report['raw_sha256'] and len(raw) == report['raw_bytes']
    assert report['exit_code'] == (1 if path.parent.name in failed else 0)
    if 'source_sha256' in report:
        inputs = list(path.parent.rglob('*.lean'))
        assert len(inputs) == 1 and sha(inputs[0].read_bytes()) == report['source_sha256']
        assert '-DwarningAsError=true' in report['command'] and '-Dlinter.all=true' in report['command']
for name in ['source-check-3', 'source-check-4']:
    assert (here / 'work' / name / 'raw.log').read_bytes() == b''
assert (here / 'work/public-1/checked.lean').read_text().replace('set_option pp.width 140\n', '') == (here / 'work/public-2/checked.lean').read_text()
audit = (here / 'work/audit-1/raw.log').read_text()
assert 'Checked axiom dependencies of 76089 MicroCFTA theorems.' in audit
assert 'Build completed successfully (3679 jobs).' in audit
assert len(re.findall(r'^warning:', audit, re.M)) == 1 and 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in audit
public = (here / 'work/public-2/raw.log').read_text()
decls = load('work/public-declarations.json')
assert re.findall(r'^@?(MicroCFTA\.[\w.]+)(?=\s)', public, re.M) == decls['declarations']
assert len(decls['declarations']) == 6
axioms = re.findall(r"'(MicroCFTA\.[^']+)' depends on axioms: \[(.*?)\]", public, re.S)
assert [name for name, _ in axioms] == decls['theorems'] and len(axioms) == 3
for _, names in axioms:
    assert {name.strip().split('.{', 1)[0] for name in names.split(',')} == {'propext', 'Classical.choice', 'Quot.sound'}
for suffix in ['limits.json', 'usage.json']:
    paths = list((here / 'inputs').glob('*.' + suffix))
    assert len(paths) == 9
    for path in paths:
        value = json.loads(path.read_text())
        if suffix == 'limits.json':
            assert value == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        else:
            assert 0 <= value['age_seconds'] <= 600 and value['remaining_percent'] > 1
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert (here / 'inputs' / ('mcfta-pruning-native-view-20261024-' + name + '-review.md')).is_file()
assert (root / 'lean/notes-current-pruning-native-view.md').read_bytes() == (here / 'current-note.md').read_bytes()
findings = (root / 'FINDINGS.md').read_text().split('## Actual interned-node narrowing', 1)[0]
assert '## Haskell fix handoff for external work' in findings and findings.count('| Fixed by ') == 6
assert 'All six repairs are in the imported main history.' in findings
prior = load('previous-publication/remote-publication.json')
assert prior['status'] == 'PUSHED_AND_REMOTE_VERIFIED' and prior['remote_head'] == baseline
assert load('previous-publication/publication-spec.json')['head'] == baseline
print(json.dumps(dict(status='PASS', baseline=baseline, main=main, proof=proof,
    baseline_files=count, unchanged_files=count - len(changed), exact_changed_files=changed,
    new_modules=1, lean_attempts=8, public_signatures=6, axiom_reports=3,
    resource_receipts=9, sealed_files=len(manifest), goal='ACTIVE_INCOMPLETE'), indent=2))
