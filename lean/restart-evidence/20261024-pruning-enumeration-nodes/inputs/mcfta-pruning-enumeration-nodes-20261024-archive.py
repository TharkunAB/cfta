import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-nodes-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-nodes'
assert not evidence.exists()
plan = Path('/tmp/mcfta-pruning-enumeration-observation-20261024-plan.md')
assert plan.is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-nodes-20261024-' + name + '-review.md').is_file()
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
for path in sorted(Path('/tmp').glob('mcfta-pruning-enumeration-nodes-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-nodes-20261024-archive-1.'):
        shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-nodes-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for stem in ['archive-1', 'local-publication-1', 'authorized-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'usage.json', 'source.py', 'peaks.txt']:
        path = Path('/tmp/mcfta-pruning-native-view-20261024-' + stem + '.' + suffix)
        assert path.is_file()
        shutil.copyfile(path, prior / path.name)
for name in ['seal-result.json', 'local-publication.json', 'remote-publication.json', 'push.log', 'publication-spec.json']:
    shutil.copyfile(Path('/tmp/mcfta-pruning-native-view-20261024') / name, prior / name)
shutil.copyfile('/tmp/mcfta-pruning-native-view-20261024-publication.py', prior / 'publication.py')
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationNodes.lean', production / 'SourcePruningEnumerationNodes.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-nodes.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-nodes-20261024-verify.py', evidence / 'verify-checkpoint.py')
shutil.copyfile(plan, evidence / 'next-enumeration-observation-plan.md')
(evidence / 'INDEX.md').write_text("# Stored enumeration-node handle evidence\n\nRead current-note.md for the exact source contracts and remaining obligations.\nThe computed decoder checks issued keys and canonical winner identities before\nreturning complete payloads. Coherent/Available/closed inputs derive exact\nreadback. Actual Keeps growth retains each successful lookup.\nThis does not prove native NodeId extraction or enumeration-slot realization.\n\nWork retains the complete baseline and all five compiler/build/public attempts.\nThe first source attempt retains its unclosed Option contradictions and deprecated\nconditional-lemma diagnostics. Only proof text changes in the successful retry.\nThe final strict log is empty. All four public signatures and both actual axiom\nreports remain; each uses only propext and Quot.sound. Inputs retain complete\nreviews, exact commands, fresh allowance and capped 4 GiB/no-swap receipts.\nOwner-proposal retains all41 frozen payload files and five exact contracts.\nPrevious-publication retains the prior checkpoint's post-seal receipts.\nThe next plan connects actual pending-slot observations to decoded Values.\n\nRun verify-checkpoint.py with --root set to the repository root. It checks the\nmanifest, every baseline blob/mode, nine exact document inverses, one Audit\nimport, frozen proposal/source cuts and actual source/public/raw identities.\nIt does not compile or prove native extraction, slot writes or semantic pruning.\nEarlier proofs, counterexamples, repairs, drafts and optimized interned code remain.\nFINDINGS keeps its external repair index first. All six repairs are on main.\nNo Haskell source changes. The full goal remains active and incomplete.\n")
files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
