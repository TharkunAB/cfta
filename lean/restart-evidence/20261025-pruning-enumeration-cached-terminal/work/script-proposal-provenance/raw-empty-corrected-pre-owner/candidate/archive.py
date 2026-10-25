import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-cached-terminal-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-cached-terminal'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'd6b8904d798026b23116ec3171c0638aa247d6eb78238b658a5d718421c540a1'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-cached-terminal-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-cached-terminal-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-cached-terminal-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-cached-terminal-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-cached-terminal-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationCachedTerminal.lean', production / 'SourcePruningEnumerationCachedTerminal.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-cached-terminal.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-cached-terminal-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("# Native cached terminal completion\n\nRoot selected one theorem complete for the existing nonempty terminal arm. It adds no new definition, action, instance declaration, helper, type, predicate, carrier or Graph. It uses eight typed local haves, one typed proof let for an inline existing Cached value and no induction. Context activates the existing public named SourcePruningEnumerationTerminal.terminalMonadList dictionary once, with no new dictionary body. Context contains 21 lines and the public head contains 148. Source estimate 360–600 ordinary lines, hard limit 900. Actual source review is bound; owner/schema binding remains pending. No check, axiom set or future publication outcome is claimed.\n\nGenuine initial inputs are Context, Safe, Roots, canonical waiting counts, all-Nat native flags, bounded first/rest suspended variables, InputsPending, pending realization, nonempty available closed incoming value and bounded incomingScs. Explicit conditional admission supplies recursive Fold.Ranges at every actual prefix and current incoming WordRanges at every actual completed fold. It does not supply a desired prefix, final cache, successful callback or initial-only numeric forecast.\n\nThe prefix derives recorded representatives in original order with duplicates, winner and actual joined core. Only waiting-transfer keys use ascending distinct nonwinners. Inline Cached packaging keeps the original flags and attaches the computed moved waiting map; plain frame alone would keep the wrong waiting map. Roots/counts use mergedRoots. Winner rootness and pending source/target facts justify one CachedFoldCompletion result on the same recorded list. CachedFold.erase identifies the original Fold at the same bounds. Actual rejected fold rows stop before incoming and retain their reached Caller, saved queries, cache prefix and Post.\n\nOnly the completed-fold branch invokes CachedIncoming.complete at its actual current Context, heap, target and ranges. It retains the full original read/run/write-prefix, Post, query/unfolding, available/closed/codec and optional/present intersection-language receipts. One actual gained-only write attaches the logical cache to the same after-write core and reached heap. Exact Terminal.run remains the observed runtime, including returned read core and joined moved map. Replacement Empty performs write/inherit before raw rejection. That raw stream does not itself carry the after-write cache. Under the admitted incoming domain, raw [] identifies Empty replacement and fixed handle 0; returned read data may support a partial post-observation adapter without a second query. This theorem implements no adapter or correspondence law. The incoming Empty arm runs before the prefix and is outside this nonempty theorem. The returned fragment is a bounded winner hole, not a write at captured wrapper uv-prime.\n\nAll 150635 baseline blobs/modes/refs/stashes/worktrees, nine document inverses, Audit prepend plus separate audit-addition.json and original owner/body-gate equality/exact-once strings remain guarded. Exactly 26 actual prior CachedIncoming inputs retain their order, FULL 16218-byte summary, canonical assessment and separate sealed peer context. All actual failures/raw/public axiom sets, six-artifact 4 GiB caps, documents-1 non-Lean ledger, manifest-in-HEAD and exact files/index/tree/modes, singleton ordinary publication destination remain unchanged. The current owner is copied once; old revisions and complete program/draft history remain protected by baseline and custody.\n\nH6 remains strongest, the full goal ACTIVE and all six Haskell handoffs first. No Haskell change is claimed. A post-observation adapter and its erasure/correspondence, initial-only mixed numeric admission, final Safe/LiveRoots, selector/partition/fallback, wrapper normalization/reconstruction at captured original uv-prime, physical maps/machine integers, extraction and full driver correspondence remain open. No future check, seal or push result is inferred.\n")

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
