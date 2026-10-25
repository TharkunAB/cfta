import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-cached-child-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-cached-child'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'a4091150505fc7418247e3d6bddb7a68266e08d1c729d2d4e4ce6fe575383623'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-cached-child-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-cached-child-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-cached-child-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-cached-child-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-cached-child-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationCachedChild.lean', production / 'SourcePruningEnumerationCachedChild.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-cached-child.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-cached-child-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Native cached ordinary child preparation\n\nThe selected interface has allocate, writeSlot and prepareOrdinary definitions, plus allocate_node_flags and complete theorems. Root selected 18 typed haves and one proof let, with no instances, induction, new type or Graph carrier. The source estimate is 280–480 ordinary lines, hard limit 680. Actual frozen owner controls and source-review binding remain pending in this unactivated source proposal.\n\nThe ordinary nonterminal producer starts from genuine current coherence, a closed available ordinary child value, StorageValid, PendingRealized, Roots, exact canonical waiting counts, actual native classified flags and bounded scs. The actual scs.any terminal=false guard is an independent premise; storage bounds do not derive it. The handle/readback is derived, and existing prepareChild supplies the same actual core child singleton. No supplied successful callback, final state or final index law replaces execution.\n\nThe cached allocation runs the actual native candidate, appends the empty-scs slot at the current counter, updates the flag, leaves waiting unchanged and inherits ancestry once through the allocated core. writeSlot reads that actual raw old slot and calls NativeIndex.write with the full gained scs and old lost references. Counts retain current read-only roots, source order and all duplicate occurrences. The final write does not add a second inheritance. The producer derives matching intermediate/final core states, slots, classified flags, exact waiting counts, storage, realization, unchanged forest/Roots, counter growth and the returned fresh hole. It does not use Graph Cached.allocate or changed-slot Cached.frame as a native proof.\n\nWork retains all 142364 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, all actual failed inputs/raw reports, complete public signatures/actual axiom subsets and complete resource families. The separate audit-addition.json record remains required. Exactly 26 prior Admission inputs retain archive-1/local-publication-1/push-1, canonical assessment and the complete 39372-byte summary with optional Git whitespace diagnostics. Its sealed peer and explicit nonterminal-domain qualification remain separate context. Older strict failures, metadata repairs and optional diagnostics remain historical facts, not current outcomes.\n\nForce-add every manifest path and SHA256SUMS, including ignored logs. Publication requires all sealed paths in HEAD, exact filesystem/index/tree/modes and a singleton ordinary formalize destination. Only actual retained reports supply validation. No passing check, seal or push is predicted.\n\nWhole-edge cached sequencing, interrupted prefixes and branch alternatives, current-resource admission, native Int/IntMap/IntSet extraction, selector order, full Safe/LiveRoots, wrapper reconstruction and complete scheduler/driver correspondence remain open. Existing Mu/Union and optimized-core proofs remain protected. H6 stays strongest and the whole goal remains ACTIVE and incomplete. All six imported Haskell repair handoffs remain first in FINDINGS. No Haskell source change is claimed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
