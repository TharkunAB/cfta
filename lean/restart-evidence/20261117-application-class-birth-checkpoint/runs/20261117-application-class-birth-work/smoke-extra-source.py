from pathlib import Path
from datetime import datetime
import json
import shutil
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
archive = work.parent / '20261117-application-class-birth-checkpoint'
fixture = root / 'lean/MicroCFTA/SourceCheckpointUnexpectedExtra.lean'
assert not fixture.exists()
assert not (archive / 'manifest.json').exists()
expected = {str(p.relative_to(root)) for p in (root / 'lean/MicroCFTA').glob('*.lean')}
assert len(expected) == 6242
with fixture.open('x') as output:
    output.write('-- Temporary unpinned Source path for the checkpoint verifier smoke check.\n')
try:
    rejected = subprocess.run(['python3', str(archive / 'verify.py'), '--current-tree'],
                              cwd=root, text=True, capture_output=True)
    assert rejected.returncode != 0
    assert 'Current Source path set differs from the pinned snapshot' in rejected.stderr
finally:
    fixture.unlink()
assert not fixture.exists()
assert {str(p.relative_to(root)) for p in (root / 'lean/MicroCFTA').glob('*.lean')} == expected
receipt = {'at': datetime.now().astimezone().isoformat(),
    'verifier': str((archive / 'verify.py').relative_to(root)),
    'fixture': str(fixture.relative_to(root)), 'expected_failure_exit': rejected.returncode,
    'extra_unpinned_source_rejected_at_path_set_check': True,
    'expected_failure_stderr': rejected.stderr,
    'fixture_removed_in_finally': True, 'original_source_path_set_restored': True,
    'source_files_after_fixture_removal': len(expected),
    'prior_immutable_archive_changed': False, 'haskell_changed': False}
target = work / 'VERIFIER-EXTRA-SOURCE-SMOKE.json'
target.write_text(json.dumps(receipt, indent=2) + '\n')
shutil.copyfile(target, archive / target.name)
subprocess.run(['python3', str(archive / 'verify.py'), '--write-manifest', '--current-tree'],
               cwd=root, check=True)
print(json.dumps({'extra_source_rejected': True, 'fixture_removed': True,
                  'normal_current_tree_and_manifest_verified': True}))
