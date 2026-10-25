import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-mu-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-mu'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == '4a00b17048eae33fd84acbea8ad24f83e06da787cff8897a0bab8b065fba9495'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-mu-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-mu-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-mu-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-mu-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-mu-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationMu.lean', production / 'SourcePruningEnumerationMu.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-mu.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-mu-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Memoized Mu caller preservation\n\nThe selected module has one theorem complete about the existing memoized Mu unfolding action. It has zero new definitions, actions, instances, helpers, carriers, Graph parameters or inductions. Only complete EdgeKey equality is a typeclass premise. The selected source estimate is 100–220 ordinary lines, hard limit 320. The actual frozen owner records exact contracts and inventories.\n\nGenuine current Context, an available closed literal Mu and PendingRealized derive the same actual memoized unfolding result, native heap and saved globals, the underlying unfold equation and concrete Caller advance/advancePhysical endpoint. The full existing Post, equal query table, extending unfolding table, Available/closed result, independent finite-term language law and every pending slot in the unchanged enumeration state remain. No successful unfold, future readiness, desired result or Post is assumed. There is no ordinary/nonempty result promise. No intersection, callback, ancestry update, final store or Union normalization executes.\n\nWork retains all 140084 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, all actual failed inputs/raw reports, complete public signatures and actual axiom subsets, and complete six-artifact resource families. The separate audit-addition.json record remains required. Exactly 26 prior Entry inputs retain actual archive-2/local-publication-1/push-1 custody. Its failed archive-1 is already protected by the baseline. The sealed assessment and separate peer remain protected without item 27. Current owner revisions and failures are recorded only if they actually occur.\n\nForce-add every manifest path and SHA256SUMS, including ignored logs. Publication requires all sealed paths in HEAD, exact filesystem/index/tree/modes and a singleton ordinary formalize destination. Only actual retained reports supply validation. No passing check, seal or push is predicted.\n\nWrapper integration, Union normalization/reconstruction, native NodeId/key extraction, original flags/partition, cache-history integration, machine bounds, Safe/LiveRoots and full driver correspondence remain open. H6 stays strongest and the whole goal remains ACTIVE and incomplete. The optimized core and older proofs remain protected. All six Haskell repair handoffs remain first in FINDINGS. No Haskell source change is claimed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
