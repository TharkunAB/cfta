import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-outer-narrow-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-outer-narrow'
assert not evidence.exists()
assert (area / 'source-plan/plan.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-outer-narrow-20261024-' + name + '-review.md').is_file()
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
for path in sorted(Path('/tmp').glob('mcfta-pruning-outer-narrow-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-pruning-outer-narrow-20261024-archive-1.'):
        shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-outer-narrow-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for stem in ['archive-1', 'local-publication-1', 'authorized-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'usage.json', 'source.py', 'peaks.txt']:
        path = Path('/tmp/mcfta-pruning-enumeration-narrowing-20261024-' + stem + '.' + suffix)
        assert path.is_file()
        shutil.copyfile(path, prior / path.name)
for name in ['seal-result.json', 'local-publication.json', 'remote-publication.json', 'push.log', 'publication-spec.json']:
    shutil.copyfile(Path('/tmp/mcfta-pruning-enumeration-narrowing-20261024') / name, prior / name)
shutil.copyfile('/tmp/mcfta-pruning-enumeration-narrowing-20261024-publication.py', prior / 'publication.py')
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningOuterNarrow.lean', production / 'SourcePruningOuterNarrow.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-outer-narrow.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-outer-narrow-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("""# Outer pruning wrapper evidence

Read current-note.md for the exact definition, branch equations and finite
completion result. The Mu branch and raw type-position branch retain the
complete input Value and heap. The fallback calls the existing actual
narrowAt with the original selected raw UVar in holeKey metadata.typing uv.
Ready, availability and closedness derive an actual finite result, complete
retained cache and chosen-run larger-fuel stability.

Work retains the complete baseline, raw attempts, public signatures and axiom
reports. Inputs retain independent reviews and fresh capped resource receipts.
Owner-proposal retains every frozen declaration, scoped type and source cut.
Previous-publication retains the narrowing checkpoint's post-seal receipts.
Work/source-plan retains the original source-only wrapper assessment and sources.

Run verify-checkpoint.py with --root set to the repository root. It checks every
manifest entry, baseline blob/mode, nine exact document inverses, one Audit
import, frozen owner identities and complete raw/source/public receipts.
Concrete typing/key laws, native IDs and cached indices, memo2, the full
pruning/enumeration caller, solver/runtime correspondence and convergence
remain open. H6 remains strongest combined. Earlier proofs, counterexamples,
repairs, drafts and optimized code remain. FINDINGS keeps all six imported
Haskell repair handoffs first. No Haskell source changes.
The full goal remains active and incomplete.
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
