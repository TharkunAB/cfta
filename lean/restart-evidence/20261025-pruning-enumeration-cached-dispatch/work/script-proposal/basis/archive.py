import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-cached-assimilation-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-cached-assimilation'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'fc59c6ec7df4adc68ca8d9ecfef8a4cad0e9b97e2e5c6f2c8d95f4913fa21630'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-cached-assimilation-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-cached-assimilation-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-cached-assimilation-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-cached-assimilation-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-cached-assimilation-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationCachedAssimilation.lean', production / 'SourcePruningEnumerationCachedAssimilation.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-cached-assimilation.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-cached-assimilation-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("# Native cached assimilation mutation\n\nRoot selected finish and complete: one computable definition and one theorem, five typed haves, one proof let and one definition let, with no instance, induction, helper, new type, predicate, carrier or Graph. Ten selected literal strings contain 66 lines. Source estimate 190–310 ordinary lines, hard limit 460. The actual source review and frozen owner are bound: 120 payloads, 84 scoped types, three obtain packets / eight fields, six case groups, 12 whole sources / 17 cuts / 217 lines and nine project import routes / 14 defining identities. No future check result is claimed.\n\nThe cached action tests merged = some 0 before either write. On early rejection it returns no raw row and retains before as a separate reached-prefix cache. Otherwise it performs two real NativeIndex.write calls with empty gained/lost deltas: target receives .unenumerated merged (sourceScs ++ targetScs), then the raw source becomes .eliminated. The final ancestry-only record update combines recursion ancestry. It does not append expansion ancestry or traverse representatives. Both writes and all fuel values remain explicit.\n\nThe producer derives the two slot bounds from the actual distinct pending raw-slot equations and StorageValid. A present supplied merged handle needs actual lookup, Available and closed facts at the fixed heap. None makes that obligation vacuous. The merged handle is a genuine input, not a derived native-intersection result. No Coherent, Ready, successful callback, desired endpoint, future Ranges, Graph or new monadic dictionary is supplied.\n\nThe exact raw comparison uses the existing Dispatch.finishOptional action. Nonempty success has the exact assimilated core, source eliminated, concatenated target payload, unchanged counter/forest/Roots, StorageValid, all pending realization, unchanged waiting with completed-pair canonical counts, and all-Nat candidate flags. Source is false, target is classified and every other flag stays unchanged. The count law is required at the completed pair, not at the intermediate target write. Optional merged None is distinct from an outer decode failure and from the empty raw list on modeled Empty rejection.\n\nAll 146226 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend and separate audit-addition.json remain required. Exactly 26 actual CachedBranches inputs retain three complete six-artifact archive-1/local-publication-1/push-1 families plus eight canonical tails, including the full 13423-byte summary. Its canonical assessment and separately sealed peer remain. Existing histories are protected by the baseline. No earlier failure is inherited as a current failure.\n\nEvery new owner literal must occur exactly once with original owner/body-gate equality. All raw/failed-input/public/axiom/cap checks, the documents-1 non-Lean ledger, all-manifest-in-HEAD/file/index/mode checks and singleton ordinary publication destination remain. Actual source metrics, failures, public axiom sets, seal and push outcomes remain unbound.\n\nThe SAME native query's merged-handle origin/language and subsequent Keeps-based flag transport remain open. Equal-ID and eliminated-source dispatcher no-ops, later cached Dispatch/Fold integration, terminal range admission, native selection/partition/fallback, wrapper normalization/finalization, physical maps/machine integers, extraction, Safe/LiveRoots and the full driver remain separate. All six Haskell repair handoffs stay first in FINDINGS. H6 remains strongest; the whole goal remains ACTIVE. No Haskell or full-runtime change is claimed.\n")

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
