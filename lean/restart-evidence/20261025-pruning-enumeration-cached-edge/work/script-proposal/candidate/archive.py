import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-cached-edge-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-cached-edge'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == '6e3d681532b1eb9387a3478cd042af9e0d53e06e1ea71fcd83cd96f563d2da68'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-cached-edge-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-cached-edge-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-cached-edge-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-cached-edge-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-cached-edge-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationCachedEdge.lean', production / 'SourcePruningEnumerationCachedEdge.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-cached-edge.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-cached-edge-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Native cached selected-edge execution\n\nRoot selected prepare and complete: one noncomputable definition and one theorem. Fifteen selected fragments / 98 lines contain seven typed haves, three proof lets and two definition lets. No new instance, induction, helper, type, predicate, carrier or Graph is selected. The source estimate is 300–480 ordinary lines, hard limit 680. The frozen owner records 90 payloads, 172 scoped entries, 8 obtain packets / 45 fields, 7 case groups, 17 whole sources and 28 cuts / 510 lines, plus 10 routes / 17 project identities. All 15 selected literals remain exact. Independent source review and the separate Root body gate remain required; source controls are not compiler evidence.\n\nThe selected producer derives one stable whole outcome above a finite bound, exact unprepared iff outer None, and exact raw rows for every actual prepared EdgeTraversal action. Its genuine inputs retain fixed-heap Ready, an available closed ordinary parent, stored-edge membership, initial bucket bounds, storage/realization, Roots and both native index laws. No callback-success premise, desired endpoint or future Ranges input is supplied.\n\nActual CachedOwn preparation precedes ordered CachedStages execution. Arity rejection, projection absence, Empty rejection, captured unsupported singleton and successful fragment construction remain distinct. Reject retains its separate completed-prefix cache; outer None carries no such cache. Only successful some-fragment rows record the computed residual. Cached.frame attaches indexes to that exact obligations update; it is not a changed-slot law. Counter monotonicity, alignment, forest/Roots, storage, realization, counts, native flags and fragment bounds use the actual derived endpoint.\n\nAll 144967 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend and separate audit-addition.json remain required. Prior custody is exactly 18 CachedStages archive-1/local-publication-1/push-1 receipt artifacts plus eight canonical tails (26 total), including the complete 12204-byte summary. Its sealed canonical assessment and separate sealed peer remain. The actual source-review and custody-index hashes are bound. No old failure, owner revision or result count is inherited as a current outcome.\n\nAll actual strict failures/full inputs/raw logs, complete public signatures and actual permitted axiom subsets remain required. The documents-1 non-Lean cap ledger remains separate. Force-add every manifest path and SHA256SUMS, including ignored logs. Publication retains all-manifest-in-HEAD, exact filesystem/index/tree/modes, original ref/stash/worktree checks and the singleton ordinary formalize destination. Actual check/source/public/build counts, axiom sets and seal/push results remain unbound.\n\nLater ordered alternatives must start from the same original cache and preserve duplicates. Native terminal fallback, configured/canonical selection, physical maps/machine integers, extraction, wrapper normalization/reconstruction, Safe/LiveRoots and the full driver remain open. All six Haskell repair handoffs stay first in FINDINGS. H6 remains strongest and the whole goal remains ACTIVE and incomplete. No Haskell change or full-runtime result is claimed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
