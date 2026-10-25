import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-cached-incoming-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-cached-incoming'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'fa67d7602cec27735848b60824c2f5f5aeb1a6a8f177950c4535d51c79aa1cf3'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-cached-incoming-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-cached-incoming-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-cached-incoming-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-cached-incoming-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-cached-incoming-20261025-proposal-v2', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationCachedIncoming.lean', production / 'SourcePruningEnumerationCachedIncoming.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-cached-incoming.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-cached-incoming-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("# Native cached incoming-node completion\n\nRoot selected one theorem complete for the existing incoming-node action. It adds no new runtime definition, instance declaration, induction, helper, type, predicate, carrier or Graph. Ten selected strings contain 107 lines: context 17, public head 80 and eight typed local have heads 10. Source estimate 180–320 ordinary lines, hard limit 520. Actual source review and the frozen owner/schema are bound: 167 payloads / 169 files, ten exact strings / 107 lines, 154 typed scope positions, five packets / 50 fields and zero case groups. The V2 context activates one existing public named Monad List dictionary, SourcePruningEnumerationIncomingNode.incomingNodeMonadList; it declares no new instance or dictionary body. This pre-body source correction is not a compiler failure. Complete V1 owners/programs and prior drafts remain separately protected by whole-area custody. The owner retains 27 whole sources, 33 inclusive cuts / 394 lines, 19 literal import edges and 27 project identities. No check result or future publication outcome is claimed.\n\nGenuine inputs are the initial Context, StorageValid, pending realization, Roots, canonical waiting counts, all-Nat native flags, a representative target with an actual pending slot, available closed incoming value, bounded incoming suspended variables and the current conditional WordRanges. The producer derives the actual representative read and compression Frame, raw incoming run, actual setValue/inheritAncestry prefix and after-write core. It retains the full Post, saved-query equality, unfolding extension, availability, closure, encoding/decoding, optional old value and present-value semantic receipt. No desired write prefix, final cache or successful callback is supplied.\n\nThe selected result derives finite native gained-only indexes at the same actual after-write heap/core. It frames the original cache onto the derived read core, performs the actual NativeIndex.write with gained=incomingScs and lost=[], then frames that result onto after.core. It retains counter, read representatives, Roots, canonical counts, the exact occurrence-sensitive waiting update and all-slot flags. The target predicate uses the actual replacement boundary and concatenated suspended list. Original order and duplicate occurrences remain. The old-none branch retains incoming and the unchanged Caller/memos/inventory; the old-some branch retains the actual checked-query receipt and intersection language. The false flag retains the original query endpoint and memos as specified.\n\nThis is a logical after-write witness. The existing runtime returns its earlier read endpoint. Replacement Empty performs write/inherit before raw rejection []; that raw stream does not contain the after-write cache. The theorem does not implement executable cache recovery or replace the existing action. Earlier incoming Empty and terminal moved-waiting composition remain separate.\n\nAll 149682 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend and separate audit-addition.json remain guarded. Exactly 26 actual prior CachedFoldCompletion artifacts retain their order, FULL 16168-byte summary, canonical assessment and separate sealed peer context. Original owner strings must equal the body gate and occur exactly once. All failure/raw/public/axiom checks, six-artifact 4 GiB caps, documents-1 non-Lean ledger, full manifest membership in HEAD, exact files/index/tree/modes and singleton ordinary publication destination remain unchanged. The current owner is copied once; older owners, raw attempts and drafts remain protected by baseline/custody.\n\nAll six Haskell repair handoffs remain first. H6 stays strongest and the whole goal ACTIVE. Terminal moved-waiting/mergedRoots packaging, Safe and InputsPending admission, explicit mixed-loop ranges, initial-only numeric admission, arbitrary-fault cache recovery, selector/partition/fallback, wrapper normalization/reconstruction, physical maps/machine integers, extraction and full driver correspondence remain open. No Haskell change, future passing check, seal or push is asserted.\n")

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
