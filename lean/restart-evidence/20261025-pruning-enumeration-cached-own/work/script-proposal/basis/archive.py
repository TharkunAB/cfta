import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-cached-prepare-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-cached-prepare'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'd9ac05a718f3945feda1cbc3893ada021c5a9ad33fcd653af109296db3efe3d9'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-cached-prepare-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-cached-prepare-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-cached-prepare-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-cached-prepare-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-cached-prepare-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationCachedPrepare.lean', production / 'SourcePruningEnumerationCachedPrepare.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-cached-prepare.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-cached-prepare-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("# Native cached child shape preparation\n\nThe selected interface has prepareChild and allocate_complete, boundary_complete and complete. There is one definition and three theorems, with 11 typed haves, no lets, instances, induction, new type or Graph carrier. The source estimate is 330–520 ordinary lines, hard limit 720. The frozen owner records 16 exact literal contracts / 124 lines, 290 scopes, 16 whole-source snapshots and 34 cuts / 534 lines, with five import routes through 20 project identities. All 16 new source literals must match the owner byte-exactly. The actual source review is bound. No proof or check outcome is supplied by these templates.\n\nGeneral cached allocation uses the actual optional-handle readback, available closed value when a handle is present, StorageValid, PendingRealized, current Roots, canonical waiting counts and the all-Nat native candidate flag invariant. The old counter slot is absent by alignment. Its genuine previous flag is false. This fact handles false classification without assuming a desired new flag law. Absent-node allocation has no some-handle realization obligation. Allocation inherits ancestry once and keeps waiting and the forest unchanged.\n\nFor nonterminal available closed Mu/Union, readback derives the handle and actual core action. The stored bucket is empty even when the input nonterminal bucket is nonempty. No full-scs write or second inheritance is added. Their fresh native flag is false and waiting remains unchanged. Ordinary nodes reuse CachedChild.complete with their genuine inherited-scs bounds and native full-scs write. The independent nonterminal test is not derived from storage bounds.\n\nEmpty returns some [] before allocation or terminal tests. No cache endpoint is claimed for that rejection. Reference remains model unsupported; native unresolved-reference errors are not equated with None. Missing decode, unsupported terminal buckets on nonempty shapes and insufficient ordinary-write fuel remain partiality. The producer derives a stable adequate bound and exact raw core rows. It does not assume successful callbacks, desired future states or Graph index laws.\n\nWork retains all 143150 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, actual failed inputs/raw reports, full public signatures/actual axiom subsets and complete resource families. The separate audit-addition.json record remains required. Exactly 26 prior CachedChild inputs retain archive-1/local-publication-1/push-1, the canonical already sealed assessment and complete 13800-byte summary. Its sealed peer is separate context. Old four strict failures, exact header/type repairs and metadata overlays remain prior history, not current outcomes.\n\nForce-add every manifest path and SHA256SUMS, including ignored logs. Publication requires every sealed path in HEAD, exact filesystem/index/tree/modes and the singleton ordinary formalize destination. Only actual retained reports supply validation. No passing check, seal or push is predicted.\n\nWhole-edge cached sequencing, reached interrupted prefixes, own-class allocation, residual ordering and same-before branch alternatives remain open. Native maps/machine integers, configured selector order, Safe/LiveRoots, wrapper reconstruction and complete scheduler/driver correspondence remain open. H6 stays strongest and the whole goal remains ACTIVE and incomplete. All six imported Haskell repair handoffs remain first in FINDINGS. No Haskell source change is claimed.\n")

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
