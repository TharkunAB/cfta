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
(evidence / 'INDEX.md').write_text("# Captured-slot fragment finalization\n\nThis is an unselected source-only checkpoint draft. The tentative module is SourcePruningEnumerationFinalize. Root has not selected its exact public interface, owner inventory or source budget. No theorem or validation outcome is asserted.\n\nThe prospective suffix follows enumerateOutUVarWith at the captured original uv. It clears expansion ancestry, reads that slot's CURRENT value and uses NativeIndex.write with the enumerated fragment, no gained references and references lost from that actual current value. The current slot can differ from the terminal winner and can be eliminated. Pre-expansion references must not substitute for the current read. The precise finite producer and invariants await Root's selected headers.\n\nWork retains all 138877 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, all actual failed inputs/raw reports, complete public output/allowed actual axiom subsets and each six-artifact resource family. Exactly 26 prior NativeIndex publication inputs and separately sealed assessment/peer context remain protected. Prior owner revisions and metadata overlays remain baseline history. No current revision or failure is invented.\n\nForce-add every manifest path and SHA256SUMS, including ignored logs. Publication requires every sealed path in HEAD, exact filesystem/index/tree/modes and a singleton ordinary formalize destination. Actual outcomes remain unbound. No check, seal or push success is predicted.\n\nNative machine arithmetic and map/set extraction, original flag/partition provenance, initial-only range admission, final Safe/LiveRoots and complete driver correspondence remain open unless an exact selected contract proves a narrower statement. H6 stays strongest. The whole goal is ACTIVE and incomplete. The optimized core, earlier proofs and all six imported Haskell repair handoffs remain protected. The handoffs remain first in FINDINGS. No Haskell change is proposed.\n")

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
