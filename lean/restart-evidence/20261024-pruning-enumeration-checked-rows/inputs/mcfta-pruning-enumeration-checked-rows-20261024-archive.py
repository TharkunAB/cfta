import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-checked-rows-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-checked-rows'
assert not evidence.exists()
assert Path('/tmp/mcfta-pruning-enumeration-selected-row-20261024-next-assessment.md').is_file()
assert Path('/tmp/mcfta-pruning-enumeration-selected-row-20261024/post-publication-summary.json').is_file()
assert Path('/tmp/mcfta-pruning-enumeration-checked-rows-20261024-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-checked-rows-20261024-' + name + '-review.md').is_file()
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
for path in sorted(Path('/tmp').glob('mcfta-pruning-enumeration-checked-rows-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-checked-rows-20261024-archive-1.'):
        shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-checked-rows-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for stem in ['archive-1', 'local-publication-1', 'authorized-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'usage.json', 'source.py', 'peaks.txt']:
        path = Path('/tmp/mcfta-pruning-enumeration-selected-row-20261024-' + stem + '.' + suffix)
        assert path.is_file()
        shutil.copyfile(path, prior / path.name)
for name in ['seal-result.json', 'local-publication.json', 'remote-publication.json', 'push.log', 'publication-spec.json', 'post-publication-summary.json']:
    shutil.copyfile(Path('/tmp/mcfta-pruning-enumeration-selected-row-20261024') / name, prior / name)
shutil.copyfile('/tmp/mcfta-pruning-enumeration-selected-row-20261024-publication.py', prior / 'publication.py')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-selected-row-20261024-next-assessment.md', prior / 'next-assessment.md')
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationCheckedRows.lean', production / 'SourcePruningEnumerationCheckedRows.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-checked-rows.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-checked-rows-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("""# Finite checked-row construction histories

Read current-note.md for the actual finite checked constructor requests,
operation/native endpoints and intervening native child-work histories.
The finite history derives all row residency and child closure. Every row
selected from its actual normalized parent has an indexed checked origin,
complete receipt, original constraint and projected own bounds.
The existing selected-row consumer keeps inherited arity and unsupported
terminal behavior separate. This component adds no enumeration action.

Work retains the complete baseline, all actual checks, full public types,
axiom reports, resource receipts and actual failures. Inputs retain reviews.
Owner-proposal retains literal declarations, all scoped types and exact
project/library API cuts. Previous-publication retains the preceding
selected-row checkpoint's26 post-seal inputs. Its prospective assessment
was already sealed. Older proof/display/setup failures and gate history
remain protected in the baseline. Only refs/codex/turn-diffs/ is excluded
from fixed-reference checks.

Run verify-checkpoint.py with --root set to the repository root. It checks
all baseline blobs and modes, exact document inverses, one Audit import,
frozen declarations, actual reports, receipts and the complete file set.
Native-only prework does not cover unrelated operation-table child effects.
All-producer origins/edits, terminal intersection/assimilation, native
selection/order/IDs/index/memo2, extraction/signed bounds, cutoff language
and full typing/pruning/driver/runtime/solver/resources/convergence remain.
H6 stays strongest combined. H23 and all older work remain. No Haskell
source changes. FINDINGS retains all six imported repair handoffs first.
The complete goal stays ACTIVE and incomplete.
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
