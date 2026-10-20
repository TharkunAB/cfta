import hashlib
import json
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2) + '\n')


components = [
    ('actual-selection', '/tmp/mcfta-actual-owner-selection', 'owner-selection-verify.py'),
    ('delayed-descent', '/tmp/mcfta-delayed-owner-progress', 'delayed-owner-verify.py'),
    ('physical-boundary', '/tmp/mcfta-physical-merge-support-boundary', 'physical-merge-verify.py'),
    ('warm-fixture', '/tmp/mcfta-warm-owner-selection-fixture', 'warm-owner-kernels-verify.py'),
]
for name, source, verifier in components:
    destination = HERE / name
    assert not destination.exists()
    shutil.copytree(source, destination)
    for arguments in [[], ['--live']]:
        subprocess.run(['/usr/bin/python3', str(destination / verifier), *arguments],
                       cwd='/', check=True, stdout=subprocess.DEVNULL)
write('components.json', [{'path': name, 'verifier': verifier, 'live': True}
                          for name, _, verifier in components])

reviews = [
    'mcfta-outer-parent-history-review',
    'mcfta-outer-parent-owner-selection-review',
    'mcfta-outer-parent-owner-final-revision-review',
    'mcfta-warm-owner-selection-fixture-review',
    'mcfta-selected-copy-support-plan',
]
for stem in reviews:
    for suffix in ['.md', '-source-pins.json']:
        source = Path('/tmp') / (stem + suffix)
        assert source.is_file(), source
        shutil.copyfile(source, HERE / source.name)
shutil.copyfile('/tmp/mcfta-outer-top-owner-assessment.md',
                HERE / 'mcfta-outer-top-owner-assessment.md')
historical = {
    'b7ca5c78b622eba90898e05fc26260c476e23b3361f2a3fad10a618436f2f88b': 'history-strict-1.source.lean',
    '9c238d8c19b5e6cfa4f1f358d0d38c4b29ce7c9e5355ebcd87ff1cbe9a7640b0': 'history-strict-2.source.lean',
}
write('historical-review-snapshots.json', historical)

support = HERE / 'root-support'
support.mkdir()
for stem in ['mcfta-selected-owner-baseline-1', 'mcfta-selected-owner-proof-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'peaks.txt', 'source.py', 'usage.json']:
        source = Path('/tmp') / (stem + '.' + suffix)
        assert source.is_file(), source
        shutil.copyfile(source, support / source.name)
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-outer-owner-publication.json', 'mcfta-outer-owner-final-publication*',
                'mcfta-outer-owner-final-push.log', 'mcfta-outer-owner-final-remote.txt',
                'mcfta-outer-owner-board-readback.json', 'mcfta-outer-owner-seal-1.*',
                'mcfta-outer-owner-support-1.*']:
    found = [p for p in Path('/tmp').glob(pattern) if p.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)

modules = ['SourceCurrentActualOwnerSelection', 'SourceCurrentDelayedOwnerProgress',
           'SourceCurrentOuterParentHistory', 'SourceCurrentOuterOwnerSelection',
           'SourceCurrentPhysicalMergeSupportBoundary']
sources = {'lean/MicroCFTA/' + name + '.lean': {'sha256': sha(ROOT / 'lean/MicroCFTA' / (name + '.lean'))}
           for name in modules}
write('selected-sources.json', sources)
write('frozen-modules.json', {Path(name).stem: entry['sha256'] for name, entry in sources.items()})
write('selected-checks.json', {
    'history_strict': 'history-strict-5', 'history_public': 'history-public-2',
    'selection_strict': 'outer-selection-strict-1', 'selection_public': 'outer-selection-public-2',
    'canonical': 'owner-selection-canonical-3', 'audit': 'audit-2',
    'fixture_strict': 'fixture-strict-1',
    'unselected_successes': ['history-strict-1', 'history-strict-2', 'history-strict-3',
        'history-strict-4', 'owner-selection-canonical-1', 'owner-selection-canonical-2',
        'history-public-1', 'outer-selection-public-1', 'audit-1'],
    'reason': 'The final direct instance scopes remove the new linter warnings. Earlier exact source snapshots remain.',
})
print(json.dumps({'status': 'PASS', 'components': len(components), 'new_modules': len(sources)}))
