import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-cached-adapter-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-cached-adapter'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'd3f3c8c28b241a7b80cebcfb3271870da12e34a83cee69db9ddad30b7093efda'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-cached-adapter-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-cached-adapter-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-cached-adapter-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-cached-adapter-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-cached-adapter-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationCachedAdapter.lean', production / 'SourcePruningEnumerationCachedAdapter.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-cached-adapter.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-cached-adapter-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("# Native cached raw-row adapter\n\nRoot selected adapt and run definitions plus complete, four typed haves and one definition-local raw let. Nine exact fragments contain 95 lines. There are no proof lets, instances, induction, helpers, new types, predicates, carriers or Graph. Source estimate 260–420 ordinary lines, hard limit 640. Actual source review is bound; actual frozen owner/schema controls remain pending in this unactivated source-only draft. No validation outcome is claimed.\n\nrun obtains the original dispatcher observation once and executes a returned action once at its captured core. It keeps the actual native/worker fault sum or outer None, reached Caller and saved queries. On a returned action it retains the complete raw list before asking adapt for a separate optional cache. adapt returns the original cache for raw []; an exact singleton checks equal IDs first and an eliminated original source next, without target inspection. A live singleton reads its actual returned target slot and NativeIndex.candidate at the reached heap. It sets the source flag false, the target to that Bool, and keeps other flags/waiting with the actual returned core. Missing target, classifier failure, raw error and unexpected row shapes keep the exact raw observation but no cache witness. No default false, closure inspection, repeated query or Prop-witness extraction is used.\n\ncomplete consumes existing CachedDispatch.complete once, derives adequate stable bounds and uses the SAME actual returned heap, raw/core and full cache facts. Raw projection alone is not injective on Cached; target classification, source/other flags and unchanged waiting establish whole-cache equality. Genuine initial Context, StorageValid, PendingRealized, Roots, canonical counts, all-Nat flags, lazy slot domain and current initial WordRanges remain inputs. No desired successful callback, merged payload, final endpoint or future Fold.Ranges is assumed. The new smaller result retains original Post and saved/final query equality and completed cache laws; it does not copy the full intersection-language receipt telescope. That original theorem remains imported.\n\nAll 147603 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend and separate audit-addition.json remain guarded. Exactly 26 actual prior CachedDispatch artifacts retain order, complete 13618-byte summary, canonical assessment and separate sealed peer. Original owner literals must occur exactly once and equal the body gate. All failure/raw/public/axiom checks, six-artifact 4 GiB caps, documents-1 non-Lean ledger, manifest files in HEAD, exact files/index/tree/modes and singleton ordinary publication destination remain unchanged.\n\nH6 remains strongest and the whole goal ACTIVE; all six Haskell repair handoffs remain first. No Haskell extraction or full runtime/driver result is claimed. Arbitrary fault cache laws, future Fold admission, terminal/incoming composition, native selector/partition/fallback, wrappers, physical maps/machine integers, extraction and Safe/LiveRoots remain open. Actual check results, public axiom sets and seal/push outcomes remain unbound. This draft must not activate before actual owner binding, independent review and Root's separate gate.\n")

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
