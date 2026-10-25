import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-cached-terminal-adapter-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-cached-terminal-adapter'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'fc9a373141ae25e5a57f74940b049fa5219b8286495b75e32f4d0420df92c1c0'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-cached-terminal-adapter-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-cached-terminal-adapter-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-cached-terminal-adapter-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-cached-terminal-adapter-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-cached-terminal-adapter-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationCachedTerminalAdapter.lean', production / 'SourcePruningEnumerationCachedTerminalAdapter.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-cached-terminal-adapter.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-cached-terminal-adapter-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Native cached terminal adapter\n\nRoot selects one noncomputable run definition and erase/complete theorems. Five typed haves and one three-line typed definition let are selected. There is no proof let, induction, helper, new type, predicate, carrier, Graph or instance declaration. Context activates the existing terminalMonadList dictionary once and adds no dictionary body. The adapter adds no native query or mutation primitive. Context has 28 lines; public heads have 181; ten exact strings contain 221 lines. Source estimate 400–700 ordinary lines, hard limit 1000. Actual source review and the single frozen owner/schema are bound: 255 payloads / 257 files, ten exact strings / 221 lines, 457 typed positions, five packets / 96 fields and 28 case groups (eight runtime and twenty proof). It retains 37 whole sources including two separate standard-library provenance sources, 61 cuts / 889 lines, eighteen literal import edges and 34 project identities.\n\nThe run definition follows actual terminal stages. Incoming Empty stops before Prefix and retains the original observation with the prior cache candidate. Otherwise it observes Prefix once, packages the actual joined core with original flags and moved waiting, then observes the ordered CachedFold once. Recorded order and duplicates remain. Fold faults, outer None, raw nil, errors and unmatched lists retain original tags and reached Caller/Queries/outer core. Cache absence does not stop an original successful singleton continuation: use original Incoming once when the fold cache is absent, or IncomingCacheAdapter once on the actual singleton core framed into the recovered cache. The typed incomingObserved let shares this stage result. No query is rerun.\n\nAt every fixed representative/native/P/H/index bound, erase preserves the complete original Terminal.run five-tuple by first projection. Successful Unit rows map to the winner hole; raw errors stay errors. Returned Caller, Queries, outer read core and moved staging waiting map remain outside optional cache data. The admitted incoming cache retains its write/inherit endpoint and gained waiting; it is not framed back to the earlier outer read. Whole nil remains stage-sensitive: direct Empty, folded rejection and incoming Empty-after-write are different branches. Candidates outside the admitted completion domain are unverified; neither erasure nor their presence is an invariant checker.\n\nNonempty admitted complete consumes CachedTerminal.complete once. It keeps that full original semantic packet. Rejected folding returns its actual folded cache and endpoints. Completed folding derives the exact read slot using getter/root uniqueness, then reuses the same mapped native-write cache receipt for Empty handle0 or singleton success. No second existential completion producer, frame injectivity, query execution or count proof is introduced. The same final cache has counter, roots, storage, realization, canonical counts and all-slot native flags. The completed incoming subpacket retains full Post/query/unfolding, optional/present intersection-language, codec and raw/write receipts and identifies after with the result cache.\n\nGenuine initial Context, Safe, Roots/counts/all-slot flags, InputsPending, bounded first/rest, realization, nonempty available closed incoming and bounded incomingScs remain. Conditional recursive Fold.Ranges and actual current incoming WordRanges are still required. No successful callback, desired final cache or initial-only numeric forecast replaces them. The terminal winner hole is not the later captured-original-variable installation target. H6 remains proved and strongest; full goal ACTIVE, six Haskell handoffs first and no Haskell/native extraction change.\n\nAll 152148 baseline blobs/modes/refs/stashes/worktrees, nine document inverses, Audit prepend/separate audit-addition.json, original owner/body-gate equality and all exact strings once remain guarded. Exactly 26 actual prior IncomingCacheAdapter inputs retain FULL 17113-byte summary, original order, canonical assessment and separate sealed peer context. Actual failed raw/public axiom sets, six-artifact 4 GiB caps, documents-1 non-Lean ledger, manifest in HEAD, exact files/index/tree/modes and ordinary singleton publication destination remain unchanged. All old owners, programs and drafts remain protected. Initial-only mixed numeric admission, final Safe/LiveRoots, selector/partition/fallback, full captured-variable wrapper normalization/installation, physical maps/machine integers, extraction, whole typing/pruning, concrete solver, practical resources, convergence and full driver correspondence remain open. No future validation, seal or push result is asserted.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
