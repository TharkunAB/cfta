import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-union-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-union'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == '5667d52c463447a3fa7779c7b715151f88f4ef0b3f5385150eb67b047badfc71'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-union-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-union-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-union-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-union-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-union-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationUnion.lean', production / 'SourcePruningEnumerationUnion.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-union.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-union-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Union normalization caller preservation\n\nThe selected module has one theorem complete, zero new definitions, actions, instances, helpers, carriers, Graph parameters or inductions. Only complete EdgeKey equality is a typeclass premise. Four typed haves and three obtains with 17 fields are selected; two duplicate fields are unused. The source estimate is 100–220 ordinary lines, hard limit 320. The frozen owner records exact contracts and inventories.\n\nGenuine current Context, the same available closed literal Union and PendingRealized derive the actual Head internally. Its existing constructor retains a finite nodeEdges read and subsequent makeNode reconstruction at the actual intermediate and final heaps. Dependent HeadReads uses that SAME Head and retains the actual saved-global receipt. The concrete advanced Caller has the full existing Post, query equality and unfolding-table extension. The actual result is Available, closed and Ordinary, with independent finite-term language equivalence. Ordinary includes Empty; no nonempty result or later expansion success follows. Every pending slot remains realized in the unchanged enum state. No successful Head, future Context/Post, desired endpoint or Graph law is an input. No extra StorageValid input, cross-fuel saved-global equality or new executable global-normalization action is claimed.\n\nWork retains all 140653 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, all actual failed inputs/raw reports, complete public signatures/actual axiom subsets and complete resource families. The separate audit-addition.json record remains required. Exactly 26 prior Mu inputs retain actual archive-1/local-publication-1/push-1 custody; the sealed assessment peer is separate context. Earlier Entry archive-2 and its failed archive-1 snapshot remain baseline history. No current failure or passing result is inherited.\n\nForce-add every manifest path and SHA256SUMS, including ignored logs. Publication requires all sealed paths in HEAD, exact filesystem/index/tree/modes and a singleton ordinary formalize destination. Only actual retained reports supply validation. No passing check, seal or push is predicted.\n\nInitial Context admission, native identity/set-order extraction, wrapper expansion/reset/final installation, cache-history integration, machine bounds, Safe/LiveRoots and full scheduler/driver correspondence remain open. H6 stays strongest and the whole goal remains ACTIVE and incomplete. The optimized core and older proofs remain protected. All six Haskell repair handoffs remain first in FINDINGS. No Haskell source change is claimed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
