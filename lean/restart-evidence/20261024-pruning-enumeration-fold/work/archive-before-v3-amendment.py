import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-fold-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-fold'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'ed044da411bc27ebc6975f962ce0f96b6ab184d5467b4d0a8294b1e02331950c'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-fold-20261024-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-fold-20261024-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-fold-20261024-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-fold-20261024-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-fold-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationFold.lean', production / 'SourcePruningEnumerationFold.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-fold.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-fold-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Ordered checked pending-slot assimilation\n\nThe selected suffix uses the ORIGINAL ordered recorded list, including duplicates and the winner. It starts after the supplied observed representative/union/count-transfer prefix. It does not construct that prefix, merge the incoming node or claim full terminal completion.\n\nFor each reached occurrence, run computes dispatch once and executes its captured action once at the current enumeration state. Only the exact successful singleton advances the suffix. Rejection, enum errors, mixed/multiple raw rows and malformed results remain literal. Native/worker interruptions and model-domain absence remain distinct. The returned Caller/query pair retains reached native effects; the enum field is the last completed prefix state. No whole-fold resume is implemented.\n\nThe finite theorem starts from genuine Context, all-slot realization, a pending target and selected pending/eliminated source slots. The recursive Ranges proposition constrains reached two-present requests and tails at actual singleton transitions. It does not assume that a successful transition exists. The result derives stable bounds, full Post and query identity, all-slot realization, exact state frames and either completion or an actual first-rejection prefix/action witness. H6 remains strongest; goal ACTIVE/incomplete.\n\nWork retains the complete baseline, actual frozen contracts, all raw inputs, reports, real failures and complete resource receipts. Prior publication retains exactly26 actual inputs. Its primary next assessment and independent review are already sealed. Older Dispatch V1/V2 metadata, reader/layout/note-format histories remain protected by baseline; no new owner revision or compiler failure is invented.\n\nRun verify-checkpoint.py with --root set to the repository root. All baseline blobs/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, complete actual public signatures/axiom subsets and cap families remain checked. Force-add every manifest path and SHA256SUMS, including ignored raw logs. Publication requires all sealed paths in HEAD, exact index/tree/files/modes, singleton push URL and ordinary formalize push.\n\nNo future check, seal or publication success is assumed. Six imported Haskell repair handoffs remain first in FINDINGS. No native flag/index/container extraction, code generation, solver, full-driver, runtime/resource or convergence result is claimed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
