import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-finalize-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-finalize'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'ccb37361daabfe631877723c315bbac2cc64de601941fbd53c44a2e49aef40e9'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-finalize-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-finalize-20261025-' + name + '-review.md').is_file()
evidence.mkdir()
for path in sorted(area.rglob('*')):
    if not path.is_file():
        continue
    target = evidence / 'work' / path.relative_to(area)
    target.parent.mkdir(parents=True, exist_ok=True)
    if path.name == 'baseline-tree.txt':
        target.with_suffix('.txt.gz').write_bytes(gzip.compress(path.read_bytes(), mtime=0))
    else:
        target.write_bytes(path.read_bytes())
inputs = evidence / 'inputs'
inputs.mkdir()
for pattern in ['mcfta-pruning-enumeration-finalize-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-finalize-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-finalize-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationFinalize.lean', production / 'SourcePruningEnumerationFinalize.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-finalize.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-finalize-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Captured-slot fragment finalization\n\nThe selected interface is finish, run and complete: two definitions, one finite producer and one named local List Monad instance. One typed reset-cache let is selected, with no proof let, Graph parameter, helper theorem or new carrier. Root selected 140–220 ordinary lines, hard limit 320. Actual owner controls record the exact contracts and local inventory.\n\nfinish clears expansion ancestry, reads the CURRENT raw slot at the captured original target, writes the enumerated fragment at that same slot and returns it. The cached run resets FIRST, then reads the current slot and calls existing NativeIndex.write with gained=[] and lost=references old. It does not substitute the later terminal winner or pre-expansion references. Every present old value is allowed, including eliminated. Missing storage is outside the producer. Its rawValue failure or cached Option.none describes model partiality, not a native Haskell error contract.\n\ncomplete starts from the actual current stored equation, Roots/counts/native flags, StorageValid, FragmentBound and PendingRealized. It derives one stable finite cached run and the actual enum singleton, literal reset/write core, target readback, false target flag, canonical old-reference removal and retained Roots/counts/flags/storage/realization. It assumes no successful prefix/callback execution. Earlier expansion and fragment production remain separate; no full compression Frame across the value write or final Safe/LiveRoots is claimed. Existing count/classifier/replacement APIs are reused without a duplicate count identity.\n\nWork retains all 138877 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, every actual failed input/raw report, full public types/actual allowed axiom subsets and all six-artifact resource families. Exactly 26 prior NativeIndex publication inputs and separately sealed assessment/peer context remain protected. The fresh owner is copied once. All old owner/amendment/failure history remains baseline data. No current failure or revision is invented.\n\nForce-add every manifest path and SHA256SUMS, including ignored logs. Publication requires every sealed path in HEAD, exact filesystem/index/tree/modes and a singleton ordinary formalize destination. Root supplies actual public/build/axiom outcomes after execution. No future check, seal or push success is asserted.\n\nMachine arithmetic and native map/set extraction, flag/partition provenance, initial-only query admission, whole fragment production and full driver correspondence remain open. H6 remains strongest. The whole goal is ACTIVE and incomplete. The optimized core and earlier proofs remain protected. All six imported Haskell repair handoffs remain first in FINDINGS. No Haskell change is claimed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
