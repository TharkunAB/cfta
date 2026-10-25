import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-cached-own-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-cached-own'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'dbc3a0dd5d1209007d2014d7fbc1d121fc9f3b1abed5a52992022e23850c82a2'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-cached-own-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-cached-own-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-cached-own-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-cached-own-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-cached-own-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationCachedOwn.lean', production / 'SourcePruningEnumerationCachedOwn.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-cached-own.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-cached-own-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("# Native cached own-class prefix\n\nThe selected interface has suspendMany and noncomputable prepare definitions, plus suspendMany_complete and complete theorems. Root selected three typed haves, one staged proof let and two public result-header lets, with one list induction and no instances, new types, predicates, helpers or Graph carrier. The source estimate is 160–280 ordinary lines, hard limit 400. Nine exact selected fragments / 105 lines and the actual source review are retained. Final owner/schema binding remains pending; no source or compiler outcome is supplied by this template.\n\nThe own-class loop executes actual cached absent-node allocation once per projected trie occurrence, in original order with duplicates. Genuine inputs are StorageValid, every PendingRealized slot, current Roots, canonical waiting Correct and the full all-Nat native flag law. No heap coherence, decoded value, availability, closedness, trie-validity or successful-loop premise is required. Alignment and the all-Nat law derive false at each old fresh slot. The loop derives the actual cached endpoint, exact suspendedVars/suspendedState core, storage, realization, unchanged forest/Roots, waiting and the entire flag function.\n\nThe edge producer checks actual inherited arity before projection or allocation. False arity returns some [] and the existing core reject action, without an after-cache. Projection absence remains outer None and performs no allocation. Successful projection uses the computed trie list, allocates consecutive variables, captures children in zipIdx order with inherited descent followed by own descent, and returns the exact residual constraint. It matches the existing prepared action and raw core singleton through the same derived suspendedState endpoint. Child actions are captured, not executed. Returning Suspended values does not add waiting counts because their references have not been stored. No inherited-scs bound or child-bucket bound is claimed here.\n\nThe loop reuses the existing optional-node allocation producer, suspendMany_exact and EdgePrefix.prepare_complete. It adds no local Monad or LawfulMonad instance and no new core mapM law. No successful callback, desired future state, Graph classifier, changing-slot Cached.frame or extra inheritance replaces the actual execution. The equality accessor and class normalization remain noncomputable at this interface boundary.\n\nWork retains all 143834 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend and separate audit-addition.json. Complete actual failed inputs/raw logs, full public signatures/actual axiom subsets and all cap families remain. The existing separate non_lean_cap_attempts=['documents-1'] ledger is retained with its strict singleton assertion; six-artifact receipt checks remain unchanged. Exactly 26 prior CachedPrepare inputs retain archive-1/local-publication-1/push-1, canonical already sealed assessment and full 12613-byte summary. Its sealed peer remains separate context. Prior failures, metadata repair and documents ledger correction are prior facts, not current outcomes.\n\nForce-add every manifest path and SHA256SUMS, including ignored logs. Publication requires every sealed path in HEAD, exact filesystem/index/tree/modes and a singleton ordinary formalize destination. Future source/report counts, axiom sets, failures and publication outcomes remain unbound. No passing check, seal or push is predicted.\n\nCached child execution and reached interruption state, residual installation, same-before ordered alternatives, independent nonterminal fallback, current-resource admission, native maps/machine integers, extraction, configured selector order, Safe/LiveRoots, wrapper reconstruction and the full driver remain open. H6 stays strongest and the whole goal remains ACTIVE and incomplete. All six imported Haskell repair handoffs remain first in FINDINGS. No Haskell source change is claimed.\n")

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
