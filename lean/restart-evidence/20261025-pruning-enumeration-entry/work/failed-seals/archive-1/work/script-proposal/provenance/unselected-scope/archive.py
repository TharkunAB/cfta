import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-entry-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-entry'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == '80c5c783b5f488b23b1744fced2076c06de367acf6e6724fdd2b7a4102f23bc6'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-entry-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-entry-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-entry-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-entry-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-entry-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationEntry.lean', production / 'SourcePruningEnumerationEntry.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-entry.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-entry-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("# Captured-root expansion entry\n\nThis is an unselected source-only checkpoint draft. The tentative module is SourcePruningEnumerationEntry. Root has not selected the exact public headers, declaration owner, source budget or proof domain. The preceding Finalize result and the sealed prospective assessment are the source context. No new mathematical result or validation outcome is asserted.\n\nWork retains all 139264 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, all actual failed inputs/raw reports, complete public types/actual allowed axiom subsets and all six-artifact resource families. Exactly 26 prior Finalize publication inputs remain in their actual summary order, including the actual push-1 family. The already sealed assessment and separate peer context remain protected; there is no 27th custody input. Older owner revisions and metadata corrections remain baseline history. No new revision or failure is invented.\n\nThe generic readers retain dynamic actual public kinds/counts, local instance count, source cap, source/cut/import identities and actual attempted/failed checks. Current results and the source-review binding remain unbound. Templates await Root's scope selection.\n\nForce-add every manifest path and SHA256SUMS, including ignored logs. Publication requires every sealed path in HEAD, exact filesystem/index/tree/modes and a singleton ordinary formalize destination. No check, seal or push success is predicted.\n\nH6 stays strongest. The whole goal is ACTIVE and incomplete. Machine arithmetic/maps/IDs, native extraction, full driver and language composition, resource bounds and convergence remain open unless an exact selected contract establishes a narrower result. The optimized core, older proofs and all six imported Haskell repair handoffs remain protected. Those handoffs remain first in FINDINGS. No Haskell change is proposed.\n")

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
