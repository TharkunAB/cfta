import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-ordinary-branches'
assert not evidence.exists()
assert Path('/tmp/mcfta-pruning-enumeration-raw-exact-20261024-next-assessment.md').is_file()
assert Path('/tmp/mcfta-pruning-enumeration-raw-exact-20261024/post-publication-summary.json').is_file()
assert Path('/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024-' + name + '-review.md').is_file()
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
for path in sorted(Path('/tmp').glob('mcfta-pruning-enumeration-ordinary-branches-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-ordinary-branches-20261024-archive-1.'):
        shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024-proposal-v2', evidence / 'owner-proposal')
shutil.copytree('/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024-proposal', evidence / 'owner-proposal-v1')
prior = evidence / 'previous-publication'
prior.mkdir()
for stem in ['archive-1', 'local-publication-1', 'authorized-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'usage.json', 'source.py', 'peaks.txt']:
        path = Path('/tmp/mcfta-pruning-enumeration-raw-exact-20261024-' + stem + '.' + suffix)
        assert path.is_file()
        shutil.copyfile(path, prior / path.name)
for name in ['seal-result.json', 'local-publication.json', 'remote-publication.json', 'push.log', 'publication-spec.json', 'post-publication-summary.json']:
    shutil.copyfile(Path('/tmp/mcfta-pruning-enumeration-raw-exact-20261024') / name, prior / name)
shutil.copyfile('/tmp/mcfta-pruning-enumeration-raw-exact-20261024-publication.py', prior / 'publication.py')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-raw-exact-20261024-next-assessment.md', prior / 'next-assessment.md')
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationOrdinaryBranches.lean', production / 'SourcePruningEnumerationOrdinaryBranches.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-ordinary-branches.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-ordinary-branches-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("""# Ordered selected-edge branch body

The concrete branch body chooses one selected edge first. It then uses its
actual captured edge preparation once. A derived Language.All₂ certificate
pairs each selected occurrence with its complete raw list. The whole stream
is their ordered flatten. Each alternative starts from the same before.
Duplicate edges and outputs remain. False inherited arity contributes raw[].
Projection absence is a partial-model domain signal. It stays distinct from
successful unsupported-child none. It is no invented Haskell return or error.

Work retains the baseline, actual checks, complete public types, axiom reports,
resource receipts and all actual failures. Inputs retain independent reviews.
Owner-proposal retains exact declarations, scoped inventories and source cuts.
Previous-publication retains all26 post-seal RawExact custody records. Its
prospective assessment was already sealed. Earlier failures, proofs, drafts,
repairs and both verifier corrections remain in the protected baseline.
Only refs/codex/turn-diffs/ is excluded from fixed-reference checks.

Run verify-checkpoint.py with --root set to the repository root. It checks
every baseline blob/mode, nine exact document inverses, one Audit prefix,
frozen contracts, actual reports/receipts and the complete manifest set.
Ready, the same available closed ordinary parent, selected-row membership,
PendingRealized and aligned supply are actual producer inputs. No desired
Success or arbitrary deterministic callback law is assumed. The worker takes
a concrete selected list. Canonical callers must derive its actual order and
membership; no synthetic reordered parent or new Graph is introduced.

This is the shallow branch BODY. Actual terminal-root dispatch remains separate.
Public runsInterned uses eager traversal; termsPruneUntil uses canonical order.
This result proves neither full public entry point. Native canonical sorting,
containers/IDs, terminal intersection/assimilation/emptiness and slot/count/
ancestry, all-producer edits, selector/index/memo2, extraction/signed bounds,
cutoff language and full typing/pruning/driver/runtime/solver/resources/
convergence remain. H6 stays strongest combined; H23 and older work remain.
No Haskell source changes. Six repair handoffs stay first in FINDINGS.
The full goal stays ACTIVE and incomplete.
""")

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
