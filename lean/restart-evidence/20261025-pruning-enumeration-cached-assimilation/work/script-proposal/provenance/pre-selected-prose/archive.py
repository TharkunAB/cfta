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
(evidence / 'INDEX.md').write_text("# Native cached assimilation mutation\n\nRoot selected run and complete, one noncomputable definition and one theorem. Five selected literals / 66 lines contain two typed haves and one list induction; no lets, instances, helper, new type, predicate, carrier or Graph is selected. Source estimate 140–240 ordinary lines, hard limit 400. The actual source review and frozen owner are bound: 62 payloads, 126 scoped types, three obtain packets / 15 fields, two case groups, 12 sources / 18 cuts / 346 lines and six project import routes / 14 defining identities. No future check result is claimed.\n\nThe worker maps the actual supplied selected-edge list in order, including duplicates, with every occurrence starting from the SAME original cache. A derived common finite bound stabilizes the full ordered outcomes. Language.All₂ retains each occurrence's exact preparation classification, raw action rows and separate branch endpoint invariants. The encoded flattened rows equal the existing OrdinaryBranches.run stream. No future callback-success or desired endpoint premise is supplied.\n\nAbsent edge preparation maps to an outer unsupported row at before. A prepared inner unsupported singleton retains its own real prefix cache. Arity or child rejection contributes no raw row while preserving its separate edge prefix receipt. Rejecting one alternative does not suppress later alternatives; rejecting one child stops that child sequence. Same-before alternatives have no merged final cache, summed allocation counter or combined waiting map. Fuel-bound combination does not sum branch allocations.\n\nInputs remain genuine fixed Ready heap, available closed ordinary parent, selected-list membership in stored edges, inherited bounds, StorageValid/all pending realization, current Roots, canonical counts and all-Nat native flags at the same before. Per-edge counter monotonicity, alignment, forest/Roots, storage, realization, both indexes and successful fragment bounds retain each actual endpoint. No arbitrary-fuel or outer-None cache promise is introduced.\n\nAll 146226 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend and separate audit-addition.json remain required. Exactly 26 actual CachedEdge inputs retain three six-artifact archive-1/local-publication-1/push-1 families plus eight canonical tails, including the complete 14936-byte summary. Its canonical assessment and separate sealed peer remain. Earlier namespace/proof/prose repairs remain historical, not current failures or literal exceptions.\n\nThe new owner requires every original literal exactly once with unchanged owner/body-gate equality. Only the prior current-component two-literal frame exception is removed; its complete actual 269-line basis and exact reversible delta remain. All other failed-input/raw/public/axiom/cap guards, documents-1 non-Lean ledger, all-manifest-in-HEAD/file/index/mode checks and singleton ordinary publication destination remain. Actual results/counts/axiom sets and seal/push outcomes remain unbound.\n\nConfigured/canonical/weighted native edge selection, terminal partition/fallback, wrapper admission, physical maps/machine integers, extraction, Safe/LiveRoots and the full driver remain open. All six Haskell repair handoffs remain first in FINDINGS. H6 stays strongest; the whole goal stays ACTIVE. No Haskell change or full-runtime claim is supplied.\n")

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
