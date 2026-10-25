import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-cached-dispatch-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-cached-dispatch'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == '0a3e4af2cfabf6969b8827d68a0fcd47e73659b26241fec27358f6a008d42593'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-cached-dispatch-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-cached-dispatch-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-cached-dispatch-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-cached-dispatch-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-cached-dispatch-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationCachedDispatch.lean', production / 'SourcePruningEnumerationCachedDispatch.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-cached-dispatch.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-cached-dispatch-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("# Native cached dispatcher completion\n\nRoot selected one public theorem complete, four typed haves and no new definitions, lets, instance declarations, induction, helper, type, predicate, carrier or Graph. Six selected literal strings contain 126 lines. Source estimate 300–480 ordinary lines, hard limit 720. The actual source review is bound. Owner/schema binding remains pending in this unactivated source-only draft. No future check result is claimed.\n\nThe theorem obtains existing Dispatch.dispatch_complete once. The SAME actual returned Caller, query tables, final memos, inventory, Post and branch packet provide the observation. Post.effects.keeps derives all-Nat old-slot native flags at that returned heap. Optional-origin slot equations and returned-heap realization derive optional merged readiness; the two-present branch retains actual lookup, Available and closed facts from its original query receipt. No native query is repeated, no closure is inspected and no desired returned handle or successful callback is assumed.\n\nConsume existing CachedAssimilation.complete at that returned heap and the SAME captured enum core. Its real zero-delta target/source writes and recursion-ancestry update give exact raw cached rows, storage/realization/Roots/counts, unchanged waiting and native flags. The source action's raw stream equals those rows. Equal-ID and eliminated-source no-ops retain the original enum cache, Caller and memos and skip unused reads. Modeled Empty yields raw [] with a separate pre-write enum cache; actual earlier Caller/memo effects remain. Optional merged None, outer missing/decode None and raw rejection remain distinct.\n\nInputs retain genuine initial Context, storage/realization/index laws, the lazy slot-domain disjunction and the conditional WordRanges law for the one initial decoded two-present request. Context does not imply that range bound. It is not a future Fold.Ranges premise. The full original TargetQuery.Receipt, intersection-language statement, disabled native-call effects, enabled guard and fourth-worker Call/CallReads, saved query equality and final tables remain. A false emptiness answer retains query, which may already be Empty.\n\nThis is an observational cached composition theorem. Existing runtime actions remain opaque. An executable cached dispatcher must retain its merged payload at the same decision or justify a separate raw-row adapter; no runtime implementation is claimed here. Success Post does not establish arbitrary native/worker fault-path preservation. Wider bounded observations, later Fold admission, terminal ranges, native selector/partition/fallback, wrapper normalization/finalization, physical maps/machine integers, extraction, Safe/LiveRoots and the full driver remain open.\n\nAll 146810 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend and separate audit-addition.json remain required. Exactly 26 actual CachedAssimilation inputs retain three complete six-artifact archive-1/local-publication-1/push-1 families plus eight canonical tails and the full 13330-byte summary. The canonical assessment and separately sealed peer remain. Earlier failures and histories stay protected by the baseline; no current failure is invented.\n\nAll original owner literals must occur exactly once with original owner/body-gate equality. All failed-input/raw/public/axiom/cap checks, the documents-1 non-Lean ledger, manifest membership in HEAD, exact file/index/tree/mode checks and singleton ordinary publication destination remain. Actual validation metrics, failures, public axiom sets and seal/push outcomes remain unbound. All six Haskell repair handoffs remain first. H6 stays strongest and the whole goal ACTIVE. No Haskell or full-runtime change is claimed.\n")

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
