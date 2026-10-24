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
(evidence / 'INDEX.md').write_text('# Native terminal scheduling indexes\n\nThe selected interface is candidate, count, write, count_complete and gained_complete. It reuses existing Cached state and the native recursiveBoundary classifier, including both Mu and InternedUnion. There is no Graph parameter or new carrier. One local List Monad instance serves the actual enum prefix. The selected source budget is260–420 ordinary lines, hard560. Actual owner controls supply the complete literal contracts and local inventory.\n\nNative gained/lost updates already resolve references through current UnionFind roots. The count action follows those reads. gained_complete consumes the SAME actual Terminal write/inherit observation, old stored value, initial index alignment/native flags/counts/Roots, Keeps between the actual heaps and the actual new decoded value at the next heap. It derives finite cached-write execution, exact raw fields and returned flags/counts/Roots/alignment through Cached.frame. No desired successful final index is an input premise. The earlier moved waiting pair remains staging data.\n\nWork retains all138475 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, all actual failed inputs/raw reports, complete public output/actual allowed axiom subsets and every six-artifact resource family. Exactly26 prior Terminal publication inputs and the separately sealed assessment/peer context remain protected. The current owner is copied once. Existing Terminal owner revisions, gates and failures remain baseline history. No current revision or failure is invented.\n\nRun verify-checkpoint.py only after Root selects the exact owner/source and actual receipts. Force-add every manifest path and SHA256SUMS, including ignored logs. Publication requires every sealed path in HEAD, exact filesystem/index/tree/modes and a singleton destination for ordinary formalize push. Root supplies actual public/build/axiom outcomes after execution. No check, seal or push success is asserted in advance.\n\nMachine bounds and native map/set extraction, original-root flags, terminal partitioning, later captured original-uv installation, initial-only range admission, Safe/LiveRoots and full driver correspondence remain open. H6 stays strongest. The whole goal is ACTIVE and incomplete. The optimized core, previous proofs and six imported Haskell repair handoffs remain protected. Those handoffs remain first in FINDINGS. No Haskell change is claimed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
