import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-incoming-node-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-incoming-node'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'bf78359344ea2400354ae2364f278d0ba0bdcec07a50edaa82dac0e961125f2a'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-incoming-node-20261024-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-incoming-node-20261024-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-incoming-node-20261024-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-incoming-node-20261024-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-incoming-node-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationIncomingNode.lean', production / 'SourcePruningEnumerationIncomingNode.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-incoming-node.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-incoming-node-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Incoming node merge at the current root\n\nThe literal consumer reads the actual current representative and complete raw pending payload. A genuine current IsRoot, PendingAt, StorageValid and all-slot realization domain identifies that SAME target without Safe or LiveRoots. Incoming suspended references must be allocated. No projected optional-node read substitutes for the complete pending payload.\n\nOld optional-none encodes the incoming complete available closed value and bypasses native query/checking. Old optional-some decodes the actual old value and uses existing IncomingQuery with incoming FIRST and old SECOND, then encodes its SAME derived replacement. The false flag still intersects; it skips only descendant/fourth checking. Current-entry decoded-pair WordRanges remains conditional and explicit. Receipt, Post, saved query memos, unfolding extension, readback and old-some intersection language remain evidence of the actual result.\n\nfinish writes incomingScs++oldScs to the actual root, inherits expansion ancestry and only THEN rejects an Empty replacement. There is no source elimination. The finite producer records the actual completed write/inherit prefix endpoint even when the final raw list is empty. Rejection returns no successful enum state. The outer product retains the actual representative-read endpoint; the surviving raw singleton carries the later written/inherited endpoint. These states are distinct. A full compression Frame is proved only for the read stage, not across the value write. StorageValid and all-slot realization are retained at the separately derived prefix endpoint.\n\nThe selected interface has finish/run definitions and finish_complete/run_complete theorems. It uses one named local List Monad instance and no LawfulMonad instance, induction, new carrier or helper. Root selected a300–430 ordinary-line estimate and hard560 before the owner/body freeze. Actual owner metadata supplies exact contracts and counts. No earlier rough source budget predicts a result.\n\nWork retains all baseline blobs/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, full actual public output and allowed axiom subsets including empty sets, every real failed input/raw report and all six-artifact resource families. Exactly26 prior IncomingQuery publication inputs and already sealed assessment/peer context remain protected. Old revisions remain baseline history; no current revision or failure is invented.\n\nRun verify-checkpoint.py with an explicit repository root. Force-add every manifest path and SHA256SUMS, including ignored raw logs. Publication requires every sealed path in HEAD, exact filesystem/index/tree/modes, a singleton push URL and ordinary formalize push. Root supplies actual build/public/axiom outcomes after execution. No future check, seal or push result is asserted.\n\nNative gained=incoming/lost=[] waiting updates, expandable indexes, Int/IntSet/physical-ID extraction, Fold final storage composition and initial-only future range admission remain separate. Full terminal/driver language, typing/pruning/solver/runtime/resources/convergence remain open. H6 stays strongest; the whole goal is ACTIVE and incomplete. The optimized core and earlier proofs remain. Six imported Haskell repair handoffs stay first in FINDINGS. No Haskell source change is claimed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
