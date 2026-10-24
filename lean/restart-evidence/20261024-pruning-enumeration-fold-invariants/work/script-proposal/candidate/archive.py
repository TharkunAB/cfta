import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-fold-invariants-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-fold-invariants'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == '8ffe68cd3df8dfa5ca61d581d134ad70408035a6ef9f7d237a408af75cdafa3c'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-fold-invariants-20261024-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-fold-invariants-20261024-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-fold-invariants-20261024-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-fold-invariants-20261024-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-fold-invariants-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationFoldInvariants.lean', production / 'SourcePruningEnumerationFoldInvariants.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-fold-invariants.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-fold-invariants-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Storage and waiting counts through the checked fold\n\nThe three state-preservation theorems use existing actions. assimilated_preserves starts from the two actual pending slots, distinct source and target, StorageValid and canonical waiting counts. It retains storage and counts for the literal concatenated-reference assimilation. The fixed external waiting map and root function stay unchanged.\n\ndispatch_preserves uses the actual selected action and its observed successful singleton. Selection and execution use the SAME before state. The action captures suspended references from that state. Context, range admission, Graph, native completion and desired query meaning are not input premises for this state-only result.\n\nrun_preserves observes the existing ordered Fold once. It covers every actual returned outer enum endpoint, including native interruption, no selected action, raw rejection, errors and malformed raw lists. One List induction follows the exact successful-singleton recursive branch. It does not construct a completed Fold. Existing Fold completion can later supply that execution without a duplicate completion packet.\n\nThe selected interface has three public theorems and no new definition, action, instance, helper, carrier or type. Root selected a220–340 ordinary-line estimate and hard460 before owner/body freeze. Actual owner metadata supplies exact contracts and counts. No source estimate predicts a compiler outcome.\n\nWork retains all baseline blobs/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, full actual public output and allowed axiom subsets including empty sets, every real failed input/raw report and all six-artifact resource families. Exactly26 prior IncomingNode publication inputs and already sealed assessment/peer context remain protected. The current fresh owner is copied once. Earlier owner revisions remain protected in the baseline. No current revision or failed attempt is assumed.\n\nRun verify-checkpoint.py with an explicit repository root. Force-add every manifest path and SHA256SUMS, including ignored raw logs. Publication requires every sealed path in HEAD, exact filesystem/index/tree/modes, a singleton push URL and ordinary formalize push. Root supplies actual build/public/axiom outcomes after execution. No future check, seal or push result is asserted.\n\nStorageValid does not establish Safe or LiveRoots. Fixed logical count preservation does not establish native gained-only cancellation, expandable-index maintenance, Int/IntSet/physical-ID extraction or root-map correspondence. Current reached WordRanges, full terminal composition, flag/partition provenance, shared driver language and initial-only future query admission remain separate. Full typing/pruning/solver/runtime/resources/convergence remain open. H6 stays strongest; the whole goal is ACTIVE and incomplete. The optimized core and earlier proofs remain. Six imported Haskell repair handoffs stay first in FINDINGS. No Haskell source change is claimed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
