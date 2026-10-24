import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-native-index-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-native-index'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'eaa51d5e2c495972ed633423b73ceeb2494e3f89deb4d08bfb0386af7fb00b72'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-native-index-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-native-index-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-native-index-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-native-index-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-native-index-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationNativeIndex.lean', production / 'SourcePruningEnumerationNativeIndex.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-native-index.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-native-index-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Native terminal scheduling indexes\n\nThis is an unselected source-only checkpoint draft. Root has not selected its exact interface, owner schema or source budget. The prospective route concerns the native Value classifier, current representative counts and cached scheduling indexes at the actual terminal write prefix. It does not claim a new theorem or any validation result.\n\nThe native gained/lost update already resolves references through the current UnionFind root. Native recursiveBoundary includes both Mu and InternedUnion. A bridge must preserve that classifier rather than assume equality to the older Graph-based candidate model. The preceding Terminal result returns a moved waiting map as staging data. It does not establish the final native maintained-index projection.\n\nWork retains all138475 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, all actual failed inputs/raw reports, complete public output/actual allowed axiom subsets and every six-artifact resource family. Exactly26 prior Terminal publication inputs and the separately sealed assessment/peer context remain protected. The current owner path is provisional. Existing Terminal owner revisions, gates and failures remain baseline history. No current revision or failure is invented.\n\nRun verify-checkpoint.py only after Root selects the exact owner/source and actual receipts. Force-add every manifest path and SHA256SUMS, including ignored logs. Publication requires every sealed path in HEAD, exact filesystem/index/tree/modes and a singleton destination for ordinary formalize push. Actual outcomes remain unbound. No check, seal or push success is asserted.\n\nNative machine bounds and map/set extraction, original-root flags, terminal partitioning, later captured original-uv installation, initial-only range admission, Safe/LiveRoots and full driver correspondence remain open. H6 stays strongest. The whole goal is ACTIVE and incomplete. The optimized core, previous proofs and six imported Haskell repair handoffs remain protected. Those handoffs remain first in FINDINGS. No Haskell change is claimed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
