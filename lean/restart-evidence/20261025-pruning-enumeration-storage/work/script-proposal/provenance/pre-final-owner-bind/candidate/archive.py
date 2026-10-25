import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-storage-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-storage'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == '98f6324694af7eb1752c1354d2d384f9aeba0f78bc18cb815322d1abe8beeb2a'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-storage-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-storage-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-storage-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-storage-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-storage-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationStorage.lean', production / 'SourcePruningEnumerationStorage.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-storage.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-storage-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Ordinary branch storage admission\n\nThe selected module has four theorems child_storage, staged_storage, edge_storage and complete. It adds no definitions, actions, types, predicates, carriers or Graph parameters. One local Monad List instance is selected, with no LawfulMonad/global instance. Six typed haves, one proof let and one structural staged-list induction are selected. The source estimate is 220–380 ordinary lines, hard limit 520. Frozen owner controls and source-review binding remain pending in this unactivated source proposal.\n\nActual child, staged-child and edge observations preserve StorageValid and counter monotonicity. Present fragments and completed child lists receive the corresponding bounds. The complete producer calls existing run_complete once and uses All₂.imp to enrich the SAME ordered raw stream, preserving duplicates and all alternatives from the SAME before. False arity remains raw [], missing projection remains the initial before, and unsupported-child results retain their actual completed-prefix endpoint. Existing alignment and all pending realization remain. No successful callback or desired-output law is an input to complete. Genuine initial StorageValid and bounded inherited scs are explicit; StorageValid alone does not bound arbitrary scs. Deriving that bound from a later actual pending-slot equation remains separate. StorageValid does not assert full Safe/LiveRoots.\n\nWork retains all 141237 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, all actual failed inputs/raw reports, complete public signatures/actual axiom subsets and complete resource families. The separate audit-addition.json record remains required. Exactly 26 prior Union inputs retain archive-1/local-publication-1/push-1 and the explicitly selected next-assessment-v2 report. Its sealed V2 peer is separate context. Historical immutable V1 and the failed report-alias copy remain in the previous summary, neither a proof nor a seal failure. No current failure or passing result is inherited.\n\nForce-add every manifest path and SHA256SUMS, including ignored logs. Publication requires all sealed paths in HEAD, exact filesystem/index/tree/modes and a singleton ordinary formalize destination. Only actual retained reports supply validation. No passing check, seal or push is predicted.\n\nInherited-scs provenance, wrapper/terminal current-range admission, native cached-index mutation, canonical edge extraction and full wrapper/driver correspondence remain open. H6 stays strongest and the whole goal remains ACTIVE and incomplete. The optimized core and older proofs remain protected. All six Haskell repair handoffs remain first in FINDINGS. No Haskell source change is claimed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
