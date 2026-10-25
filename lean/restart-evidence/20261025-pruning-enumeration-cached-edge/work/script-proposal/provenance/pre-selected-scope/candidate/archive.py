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
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'CURRENT_CUSTODY_INDEX_SHA_PENDING'
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
(evidence / 'INDEX.md').write_text("# Native cached selected-edge execution\n\nUNFROZEN source-only draft. Root has not selected the exact public interface, source premises or budget. The owner and source review remain unbound. This draft supplies no new mathematical or validation claim and must not be activated. Selected prose and literal templates will follow actual Root selection and frozen owner controls.\n\nThe proposal retains all 144967 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend and the separate audit-addition.json requirement. All actual failed inputs/raw logs, strict flags, full public signatures and actual permitted axiom subsets remain required. The separate documents-1 non-Lean cap ledger and every six-artifact resource family remain.\n\nPrior custody is exactly the 26 actual CachedStages publication inputs, including archive-1/local-publication-1/push-1 and the complete 12204-byte summary. Its canonical next assessment and separate sealed peer remain. The actual current custody index hash and source-review hash are deliberately unbound in this draft. No prior failure, owner revision or runtime count is inherited as a current outcome.\n\nForce-add every manifest path and SHA256SUMS, including ignored logs. Publication retains complete manifest membership in HEAD, exact filesystem/index/tree/modes, original ref/stash/worktree checks and the singleton ordinary formalize destination. Future attempts, source/public/build counts, actual axiom sets and seal/push outcomes remain unbound.\n\nAll six imported Haskell repair handoffs stay first in FINDINGS. H6 remains strongest and the whole goal remains ACTIVE and incomplete. No Haskell change, next proof, full driver, extraction or runtime result is supplied by this unselected draft.\n")

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
