import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-cached-branches-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-cached-branches'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == '2da7b977548ad7ded887f75f59c91bfef7eb4cd7af57f434f2beba9a5b922afd'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-cached-branches-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-cached-branches-20261025-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-cached-branches-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-cached-branches-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-cached-branches-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationCachedBranches.lean', production / 'SourcePruningEnumerationCachedBranches.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-cached-branches.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-cached-branches-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Native cached same-before alternatives\n\nUNFROZEN SOURCE-ONLY DRAFT. Root has not selected the exact public headers, owner controls or source budget. The new source-review binding remains pending. No candidate may be activated before actual selection, independent reviews and Root gate. Current results, attempts, failures, source/public counts and axiom sets are unbound.\n\nThe planned bounded route uses a supplied finite selected-edge list. Every occurrence starts from the same original cache, in original order with duplicates. Outer unprepared and inner unsupported options remain distinct. Each edge retains its own actual prefix cache; reject contributes no raw row. Rejecting one alternative does not suppress later alternatives. There is no merged after-cache, sum of allocation counters or combined waiting map. No future endpoint, callback-success, ranges or selector-correctness premise is supplied by this draft.\n\nAll 145664 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend and separate audit-addition.json remain required. Exactly 26 actual CachedEdge inputs retain archive-1/local-publication-1/push-1 and eight canonical tails, including the complete 14936-byte summary. The canonical next assessment and separate sealed peer remain. Earlier namespace/proof/prose repairs remain historical, not current outcomes or literal exceptions.\n\nThe new owner uses exact strings once, with original owner/body-gate equality. The old component-specific two-literal frame exception is removed; its entire original active source remains as the basis and in the prior checkpoint. All other failed-input/raw/public/axiom/cap guards, the separate documents-1 non-Lean ledger, six-artifact receipts, all-manifest-in-HEAD/file/index/mode guards and singleton ordinary publication destination remain.\n\nAll six Haskell repair handoffs remain first in FINDINGS. H6 remains strongest and the whole goal remains ACTIVE. Native configured/canonical selection, terminal partition/fallback, physical containers/machine integers, extraction, Safe/LiveRoots and the full driver remain open. No Haskell change or full-runtime claim is supplied.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
