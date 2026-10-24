"""Verify raw pending-slot assimilation dispatch and the complete preserved baseline."""
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
here = root / 'lean/restart-evidence/20261024-pruning-enumeration-dispatch'
baseline = 'dd4648d37fff9d5e0e80ac88f4979156c233ea6d'
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
    'lean/MicroCFTA/SourcePruningEnumerationDispatch.lean', 'lean/MicroCFTA/Audit.lean'}
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
        assert addition == b'import MicroCFTA.SourcePruningEnumerationDispatch\n'
        assert sha(data) == audit_change['after_sha256'] and data.startswith(addition)
        data = data[len(addition):]
        assert sha(data) == audit_change['before_sha256']
        changed.append(name)
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob, name
    count += 1
assert count == 134415 and len(changed) == 10
assert git('stash', 'list', '--format=%gd %H %s') == (here / 'work/baseline-stashes.txt').read_bytes()
worktrees = (here / 'work/baseline-worktrees.txt').read_bytes()
assert git('worktree', 'list', '--porcelain') == worktrees.replace(
    b'HEAD ' + baseline.encode(), b'HEAD ' + git('rev-parse', 'HEAD').strip(), 1)
for line in (here / 'work/baseline-refs.txt').read_text().splitlines():
    value, ref = line.split()
    if ref not in ['refs/heads/formalize', 'refs/remotes/origin/formalize'] and not ref.startswith('refs/codex/turn-diffs/'):
        assert git('rev-parse', ref).decode().strip() == value, ref
assert git('rev-parse', 'codex/backup-pruning-enumeration-dispatch-20261024-2008').decode().strip() == baseline

checks = load('work/build-summary.json')
source = (root / 'lean/MicroCFTA/SourcePruningEnumerationDispatch.lean').read_bytes()
assert source == (here / 'production-sources/SourcePruningEnumerationDispatch.lean').read_bytes()
assert source == (here / 'work' / checks['successful_source_attempt'] / 'MicroCFTA/SourcePruningEnumerationDispatch.lean').read_bytes()
assert sha(source) == load('work/installation.json')['source_sha256']
assert len(source.splitlines()) == checks['source_lines']
assert not re.search(rb'\b(?:sorry|admit|axiom|unsafe|set_option)\b', source)
assert not re.search(rb'^(?:instance|structure|inductive|private) ', source, re.M)
text = source.decode()

frozen = load('owner-proposal/FROZEN.json')
pins = load('owner-proposal/pins.json')
assert len(pins) == frozen['pins_count'] and frozen['compiler_evidence'] is False
assert len((here / 'owner-proposal/pins.json').read_bytes()) == frozen['pins_bytes']
assert sha((here / 'owner-proposal/pins.json').read_bytes()) == frozen['pins_sha256']
headers = load('owner-proposal/insertion-map.json')['public_heads']
assert re.findall(rb'^(?:noncomputable )?(def|theorem) ', source, re.M) == [item['kind'].encode() for item in headers]
assert len(re.findall(rb'^local instance ', source, re.M)) == frozen['local_instance_count']
assert frozen['global_instance_count'] == 0
assert len(source.splitlines()) <= frozen['proposed_hard_cap']
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
source_index = load('owner-proposal/source-index.json')
sources = source_index['sources']
assert len(sources) == frozen['source_count']
source_ids = {}
for pin in sources:
    assert pin['id'] not in source_ids
    pinned_path = Path(pin['path'])
    if pinned_path.is_relative_to('/home/tritlo/Code/mcfta'):
        pinned_path = root / pinned_path.relative_to('/home/tritlo/Code/mcfta')
    data = pinned_path.read_bytes()
    assert data == (here / 'owner-proposal' / pin['snapshot']).read_bytes()
    assert len(data) == pin['bytes'] and sha(data) == pin['sha256']
    source_ids[pin['id']] = (pin['path'], data)
assert len(source_index['cuts']) == frozen['cut_count']
for cut in source_index['cuts']:
    source_path, data = source_ids[cut['source']]
    assert cut['path'] == source_path
    assert 1 <= cut['start'] <= cut['end'] <= len(data.splitlines())
    part = b''.join(data.splitlines(keepends=True)[cut['start'] - 1:cut['end']])
    assert part == (here / 'owner-proposal' / cut['snapshot']).read_bytes()
    assert len(part) == cut['bytes'] and sha(part) == cut['sha256']
for pin in load('owner-proposal/import-routes.json')['defining_import_sources']:
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
assert 'Build completed successfully (' + str(checks['installed_jobs']) + ' jobs).' in (here / 'work/installed-1/raw.log').read_text()
assert 'Checked axiom dependencies of ' + str(checks['axiom_dependency_checks']) + ' MicroCFTA theorems.' in audit
assert 'Build completed successfully (' + str(checks['audit_jobs']) + ' jobs).' in audit
assert len(re.findall(r'^warning:', audit, re.M)) == 1 and 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in audit
public = (here / 'work' / checks['public_attempt'] / 'raw.log').read_text()
assert '⋯' not in public
decls = load('work/public-declarations.json')
assert re.findall(r'^@?(MicroCFTA\.[\w.]+)(?=\s)', public, re.M) == decls['declarations']
assert len(decls['declarations']) == len(headers)
axioms = {}
for name, names in re.findall(r"'(MicroCFTA\.[^']+)' depends on axioms: \[(.*?)\]", public, re.S):
    axioms[name] = sorted(name.strip().split('.{', 1)[0] for name in names.split(',') if name.strip())
for name in re.findall(r"'(MicroCFTA\.[^']+)' does not depend on any axioms", public):
    axioms[name] = []
assert set(axioms) == set(decls['declarations']) and len(axioms) == len(headers)
assert axioms == decls['axioms']
assert len(decls['theorems']) == sum(item['kind'] == 'theorem' for item in headers)
assert len(decls['definitions']) == sum(item['kind'] == 'def' for item in headers)
namespace = 'MicroCFTA.SourcePruningEnumerationDispatch.'
assert decls['definitions'] == [namespace + item['name'] for item in headers if item['kind'] == 'def']
assert decls['theorems'] == [namespace + item['name'] for item in headers if item['kind'] == 'theorem']
assert set(decls['definitions'] + decls['theorems']) == set(decls['declarations'])
for names in axioms.values():
    assert set(names) <= {'Classical.choice', 'Quot.sound', 'propext'}
failed_seals = checks['failed_seal_attempts']
receipt_stems = ['refresh-1', 'baseline-1'] + checks['attempts'] + failed_seals
prefix = 'mcfta-pruning-enumeration-dispatch-20261024-'
expected_stems = {prefix + stem for stem in receipt_stems}
for suffix in ['limits.json', 'usage.json']:
    paths = list((here / 'inputs').glob('*.' + suffix))
    assert {path.name.removesuffix('.' + suffix) for path in paths} == expected_stems
for stem in receipt_stems:
    for suffix in ['json', 'log', 'limits.json', 'usage.json', 'source.py', 'peaks.txt']:
        assert (here / 'inputs' / (prefix + stem + '.' + suffix)).is_file()
    receipt = load('inputs/' + prefix + stem + '.json')
    assert receipt['exit_code'] == (1 if stem in failed or stem in failed_seals else 0)
    limits = load('inputs/' + prefix + stem + '.limits.json')
    assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    usage = load('inputs/' + prefix + stem + '.usage.json')
    assert 0 <= usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert (here / 'inputs' / ('mcfta-pruning-enumeration-dispatch-20261024-' + name + '-review.md')).is_file()
assert (root / 'lean/notes-current-pruning-enumeration-dispatch.md').read_bytes() == (here / 'current-note.md').read_bytes()
findings = (root / 'FINDINGS.md').read_text().split('## Raw pending-slot assimilation dispatch', 1)[0]
assert '## Haskell fix handoff for external work' in findings and findings.count('| Fixed by ') == 6
assert 'All six repairs are in the imported main history.' in findings
prior = load('previous-publication/remote-publication.json')
assert prior['status'] == 'PUSHED_AND_REMOTE_VERIFIED' and prior['remote_head'] == baseline
assert load('previous-publication/publication-spec.json')['head'] == baseline
custody = load('work/prior-custody-index.json')
assert sha((here / 'work/prior-custody-index.json').read_bytes()) == 'be5742afba59dcd12847e6bf0bc52776fcf40e345ac6ffd296887ff34e5347a6'
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert len({pin['source'] for pin in custody}) == 26
assert {p.name for p in (here / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (here / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and sha(data) == pin['sha256']
assessment = (here / 'previous-publication/mcfta-pruning-enumeration-finish-20261024-next-assessment.md').read_bytes()
assert sha(assessment) == '3c770cc4cbab551061f850f884a736cb7b57fc3729d2cd3db4fa641111643e3c'
summary = load('previous-publication/post-publication-summary.json')
assert summary['head'] == baseline and summary['goal'] == 'ACTIVE_INCOMPLETE'
assert summary['component_status'] == 'PROVED_SEALED_PUSHED_REMOTE_VERIFIED'
assert summary['next_assessment_sha256'] == sha(assessment)
assert summary['next_assessment_is_currently_sealed'] is True
assert (root / summary['sealed_next_assessment_path']).read_bytes() == assessment
clarification = (here / 'work/script-proposal/context/prior-assessment-clarification.md').read_bytes()
assert sha(clarification) == summary['next_assessment_clarification_sha256'] == 'c232e2098ca8c7b488a349b1d418bd2cbf81e937923db40f8edf6ecd4d175b8d'
assert summary['next_assessment_clarification_is_currently_sealed'] is True
assert (root / summary['sealed_next_assessment_clarification_path']).read_bytes() == clarification
assert summary['seal_attempt'] == 'archive-1'
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
assert summary['final_local_publication_attempt'] == 'local-publication-1'
assert summary['all_manifest_files_committed'] is True
assert sha((here / 'inputs/mcfta-pruning-enumeration-dispatch-20261024-source-review.md').read_bytes()) == 'SOURCE_REVIEW_SHA_PENDING_ACTUAL_FROZEN_REPORT'

print(json.dumps(dict(status='PASS', baseline=baseline, main=main, proof=proof,
    baseline_files=count, unchanged_files=count - len(changed), exact_changed_files=changed,
    new_modules=1, lean_attempts=len(expected), public_signatures=len(headers), axiom_reports=len(headers),
    resource_receipts=len(receipt_stems), sealed_files=len(manifest), goal='ACTIVE_INCOMPLETE'), indent=2))
