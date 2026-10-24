"""Verify outer pruning wrapper and finite completion and the complete preserved baseline."""
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
here = root / 'lean/restart-evidence/20261024-pruning-outer-narrow'
baseline = '66c597b3c2f4387c116e384731cd9c89b793a59f'
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
    'lean/MicroCFTA/SourcePruningOuterNarrow.lean', 'lean/MicroCFTA/Audit.lean'}
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
        assert addition == b'import MicroCFTA.SourcePruningOuterNarrow\n'
        assert sha(data) == audit_change['after_sha256'] and data.startswith(addition)
        data = data[len(addition):]
        assert sha(data) == audit_change['before_sha256']
        changed.append(name)
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob, name
    count += 1
assert count == 129494 and len(changed) == 10
assert git('stash', 'list', '--format=%gd %H %s') == (here / 'work/baseline-stashes.txt').read_bytes()
worktrees = (here / 'work/baseline-worktrees.txt').read_bytes()
assert git('worktree', 'list', '--porcelain') == worktrees.replace(
    b'HEAD ' + baseline.encode(), b'HEAD ' + git('rev-parse', 'HEAD').strip(), 1)
for line in (here / 'work/baseline-refs.txt').read_text().splitlines():
    value, ref = line.split()
    if ref not in ['refs/heads/formalize', 'refs/remotes/origin/formalize']:
        assert git('rev-parse', ref).decode().strip() == value, ref
assert git('rev-parse', 'codex/backup-pruning-outer-narrow-20261024-0710').decode().strip() == baseline

checks = load('work/build-summary.json')
source = (root / 'lean/MicroCFTA/SourcePruningOuterNarrow.lean').read_bytes()
assert source == (here / 'production-sources/SourcePruningOuterNarrow.lean').read_bytes()
assert source == (here / 'work' / checks['successful_source_attempt'] / 'MicroCFTA/SourcePruningOuterNarrow.lean').read_bytes()
assert sha(source) == load('work/installation.json')['source_sha256']
assert len(source.splitlines()) == checks['source_lines']
assert not re.search(rb'\b(?:sorry|admit|axiom|unsafe|set_option)\b', source)
assert re.findall(rb'^(def|theorem) ', source, re.M) == [b'def'] + [b'theorem'] * 4
assert not re.search(rb'^local instance ', source, re.M)
assert not re.search(rb'^(?:instance|structure|inductive|private) ', source, re.M)
text = source.decode()

frozen = load('owner-proposal/FROZEN.json')
pins = load('owner-proposal/pins.json')
assert len(pins) == frozen['pins_count'] and frozen['compiler_evidence'] is False
assert sha((here / 'owner-proposal/pins.json').read_bytes()) == frozen['pins_sha256']
assert frozen['local_instance_count'] == 0 and frozen['global_instance_count'] == 0
assert sha((here / 'owner-proposal/FROZEN.json').read_bytes()) == load('work/body-gate.json')['frozen_sha256']
assert {p.relative_to(here / 'owner-proposal').as_posix() for p in (here / 'owner-proposal').rglob('*') if p.is_file()} == set(pins) | {'pins.json', 'FROZEN.json'}
for name, pin in pins.items():
    assert not Path(name).is_absolute() and '..' not in Path(name).parts
    data = (here / 'owner-proposal' / name).read_bytes()
    assert len(data) == pin['bytes'] and sha(data) == pin['sha256']
contracts = load('owner-proposal/contracts.json')
assert contracts == load('work/body-gate.json')['contracts']
for name, literal in contracts.items():
    assert isinstance(literal, str)
    data = (here / 'owner-proposal' / name).read_bytes()
    assert data.decode() == literal
    assert text.count(literal.rstrip('\n')) == 1
sources = load('owner-proposal/source-index.json')['sources']
assert len(sources) == 12
for pin in sources:
    pinned_path = Path(pin['path'])
    if pinned_path.is_relative_to('/home/tritlo/Code/mcfta'):
        pinned_path = root / pinned_path.relative_to('/home/tritlo/Code/mcfta')
    data = pinned_path.read_bytes()
    assert data == (here / 'owner-proposal' / pin['snapshot']).read_bytes()
    assert len(data) == pin['bytes'] and sha(data) == pin['sha256']
    for cut in pin['cuts']:
        part = b''.join(data.splitlines(keepends=True)[cut['start'] - 1:cut['end']])
        assert part == (here / 'owner-proposal' / cut['snapshot']).read_bytes()
        assert len(part) == cut['bytes'] and sha(part) == cut['sha256']
for pin in load('owner-proposal/import-routes.json')['route_defining_sources'].values():
    data = (root / Path(pin['path']).relative_to('/home/tritlo/Code/mcfta')).read_bytes()
    assert len(data) == pin['bytes'] and sha(data) == pin['sha256']

reports = list((here / 'work').glob('*/report.json'))
expected = set(checks['attempts'])
assert {p.parent.name for p in reports} == expected
failed = set(checks['failed_attempts'])
for path in reports:
    report = json.loads(path.read_text())
    raw = (path.parent / 'raw.log').read_bytes()
    assert sha(raw) == report['raw_sha256'] and len(raw) == report['raw_bytes']
    assert report['exit_code'] == (1 if path.parent.name in failed else 0)
    if 'source_sha256' in report:
        inputs = list(path.parent.rglob('*.lean'))
        assert len(inputs) == 1 and sha(inputs[0].read_bytes()) == report['source_sha256']
        assert '-DwarningAsError=true' in report['command'] and '-Dlinter.all=true' in report['command']
for name in [checks['successful_source_attempt']]:
    assert (here / 'work' / name / 'raw.log').read_bytes() == b''
audit = (here / 'work/audit-1/raw.log').read_text()
checks = load('work/build-summary.json')
assert 'Build completed successfully (' + str(checks['installed_jobs']) + ' jobs).' in (here / 'work/installed-build-1/raw.log').read_text()
assert 'Checked axiom dependencies of ' + str(checks['axiom_dependency_checks']) + ' MicroCFTA theorems.' in audit
assert 'Build completed successfully (' + str(checks['audit_jobs']) + ' jobs).' in audit
assert len(re.findall(r'^warning:', audit, re.M)) == 1 and 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in audit
public = (here / 'work' / checks['public_attempt'] / 'raw.log').read_text()
assert '⋯' not in public
decls = load('work/public-declarations.json')
assert re.findall(r'^@?(MicroCFTA\.[\w.]+)(?=\s)', public, re.M) == decls['declarations']
assert len(decls['declarations']) == 5
axioms = {}
for name, names in re.findall(r"'(MicroCFTA\.[^']+)' depends on axioms: \[(.*?)\]", public, re.S):
    axioms[name] = sorted(name.strip().split('.{', 1)[0] for name in names.split(',') if name.strip())
for name in re.findall(r"'(MicroCFTA\.[^']+)' does not depend on any axioms", public):
    axioms[name] = []
assert set(axioms) == set(decls['declarations']) and len(axioms) == 5
assert axioms == decls['axioms']
assert len(decls['theorems']) == 4 and len(decls['definitions']) == 1
for names in axioms.values():
    assert set(names) <= {'Classical.choice', 'Quot.sound', 'propext'}
setup = load('work/setup-failures.json')
assert setup['compiler_invoked'] is False
setup_failed = set(setup['capped_attempts'])
assert setup_failed == {'source-check-1'} and not (setup_failed & expected)
for stem in setup_failed:
    assert not (here / 'work' / stem / 'report.json').exists()
    assert not (here / 'work' / stem / 'raw.log').exists()
    assert not list((here / 'work' / stem).rglob('*.lean'))
    assert sha((here / 'inputs' / ('mcfta-pruning-outer-narrow-20261024-' + stem + '.log')).read_bytes()) == setup['capped_attempts'][stem]['log_sha256']
receipt_stems = ['baseline-1'] + sorted(setup_failed) + checks['attempts']
prefix = 'mcfta-pruning-outer-narrow-20261024-'
expected_stems = {prefix + stem for stem in receipt_stems}
for suffix in ['limits.json', 'usage.json']:
    paths = list((here / 'inputs').glob('*.' + suffix))
    assert {path.name.removesuffix('.' + suffix) for path in paths} == expected_stems
for stem in receipt_stems:
    for suffix in ['json', 'log', 'limits.json', 'usage.json', 'source.py', 'peaks.txt']:
        assert (here / 'inputs' / (prefix + stem + '.' + suffix)).is_file()
    receipt = load('inputs/' + prefix + stem + '.json')
    assert receipt['exit_code'] == (1 if stem in failed | setup_failed else 0)
    limits = load('inputs/' + prefix + stem + '.limits.json')
    assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    usage = load('inputs/' + prefix + stem + '.usage.json')
    assert 0 <= usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert (here / 'inputs' / ('mcfta-pruning-outer-narrow-20261024-' + name + '-review.md')).is_file()
assert (root / 'lean/notes-current-pruning-outer-narrow.md').read_bytes() == (here / 'current-note.md').read_bytes()
findings = (root / 'FINDINGS.md').read_text().split('## Outer pruning wrapper and finite completion', 1)[0]
assert '## Haskell fix handoff for external work' in findings and findings.count('| Fixed by ') == 6
assert 'All six repairs are in the imported main history.' in findings
prior = load('previous-publication/remote-publication.json')
assert prior['status'] == 'PUSHED_AND_REMOTE_VERIFIED' and prior['remote_head'] == baseline
assert load('previous-publication/publication-spec.json')['head'] == baseline
plan = load('work/source-plan/retention.json')
assert sha((here / 'work/source-plan/plan.md').read_bytes()) == plan['plan_sha256'] == '434c9435bb7248ecd5142d26b7df4de25d2b0bcbf5c02ac7389f80fcb7759bf9'
assert len(plan['sources']) == 15
for pin in plan['sources']:
    data = (root / pin['path']).read_bytes()
    assert data == (here / 'work/source-plan' / pin['snapshot']).read_bytes()
    assert len(data) == pin['bytes'] and sha(data) == pin['sha256']
    for cut in pin['cuts']:
        part = b''.join(data.splitlines(keepends=True)[cut['start'] - 1:cut['end']])
        assert part == (here / 'work/source-plan' / cut['snapshot']).read_bytes()
        assert len(part) == cut['bytes'] and sha(part) == cut['sha256']
print(json.dumps(dict(status='PASS', baseline=baseline, main=main, proof=proof,
    baseline_files=count, unchanged_files=count - len(changed), exact_changed_files=changed,
    new_modules=1, lean_attempts=len(expected), public_signatures=5, axiom_reports=5,
    resource_receipts=len(receipt_stems), sealed_files=len(manifest), goal='ACTIVE_INCOMPLETE'), indent=2))
