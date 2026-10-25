import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-cached-fold-completion-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-cached-fold-completion'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == '1101937df686a179baa851015231bb922f89ada42e7ba90abad438bad3810405'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-cached-fold-completion-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-cached-fold-completion-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-cached-fold-completion-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-cached-fold-completion-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-cached-fold-completion-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationCachedFoldCompletion.lean', production / 'SourcePruningEnumerationCachedFoldCompletion.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-cached-fold-completion.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-cached-fold-completion-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("# Native cached ordered fold completion\n\nRoot selected one theorem complete, with no new runtime definition, instance, helper, type, predicate, carrier or Graph. The initial public head contains 42 lines and context contains 16 lines. It uses one structural List induction; final typed local fragments and owner/schema binding remain pending. Source estimate 330–530 ordinary lines, hard limit 800. Source review binding is pending. No validation outcome is claimed.\n\nThe producer concerns the existing CachedFold.run. Genuine inputs are initial Context, StorageValid, pending realization, Roots, canonical waiting counts, all-Nat native flags, a pending target, pending-or-eliminated selected source slots and explicit recursive Fold.Ranges. It derives common finite fuel and worker/reader ceilings for the actual complete or first-rejected run. It does not supply a successful continuation, desired endpoint, final cache or initial-only numeric admission premise.\n\nThe returned raw list is the exact encoding of zero or one cached row, with the same actual Caller, saved queries, after.core and some after receipt. Post and final.query equality retain that endpoint. The result preserves counter, representatives, Roots, storage, pending realization, waiting counts, the original waiting map and all-slot native flags at the reached heap. It retains a pending target and all originally eliminated slots. Only the completed singleton conclusion eliminates every selected source distinct from target; the rejected empty stream retains its actual completed prefix. Equal IDs, duplicates and optional pending payloads remain in the genuine domain. Prior query effects on rejection remain visible.\n\nAll 148916 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend and separate audit-addition.json remain guarded. Exactly 26 actual prior CachedFold artifacts retain order, the full 15149-byte summary, canonical assessment and separate sealed peer. Original owner literals must occur exactly once and equal the body gate. All failure/raw/public/axiom checks, six-artifact 4 GiB caps, documents-1 non-Lean ledger, manifest files in HEAD, exact files/index/tree/modes and singleton ordinary publication destination remain unchanged. Only the current owner is copied once; earlier owner revisions and draft history remain protected by baseline and custody.\n\nH6 remains strongest and the whole goal ACTIVE; all six Haskell repair handoffs remain first. No Haskell extraction or full runtime/driver result is claimed. Initial-only mixed numeric admission, changing guard-carrier resources, general arbitrary-fault cache invariants, terminal/incoming integration, native selector/partition/fallback, wrappers, physical maps/machine integers, extraction and Safe/LiveRoots remain open. Actual source/owner controls, check results, public axiom sets and seal/push outcomes remain unbound. Independent review and Root's separate gate precede activation.\n")

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
