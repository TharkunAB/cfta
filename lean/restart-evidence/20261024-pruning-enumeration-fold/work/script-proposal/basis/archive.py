import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-dispatch-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-dispatch'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'be5742afba59dcd12847e6bf0bc52776fcf40e345ac6ffd296887ff34e5347a6'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-dispatch-20261024-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-dispatch-20261024-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-dispatch-20261024-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-dispatch-20261024-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-dispatch-20261024-proposal-v3', evidence / 'owner-proposal')
shutil.copytree('/tmp/mcfta-pruning-enumeration-dispatch-20261024-proposal', evidence / 'work/old-owner-v1')
shutil.copytree('/tmp/mcfta-pruning-enumeration-dispatch-20261024-proposal-v2', evidence / 'work/old-owner-v2')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationDispatch.lean', production / 'SourcePruningEnumerationDispatch.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-dispatch.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-dispatch-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Raw pending-slot assimilation dispatch\n\nThe exact frozen owner and complete public types fix finishOptional,\nafterQuery, dispatch and dispatch_complete. The interface uses existing\nExcept/sum/product/Option and native Demand/Worker outcomes. No new outcome\ncarrier or instance is introduced. Exact no-op and optional-node branches\nremain separate from checked-query and enabled-emptiness computation.\n\nEqual raw IDs bypass every lookup. An eliminated source bypasses target\nlookup. Absent raw slots differ from present optional-none slots; the finite\nproducer has an explicit safe-entry domain. Optional-node branches use the\nliteral value/ancestry action without a query. Two-present branches retain\none actual checked query and its receipt. Enabled emptiness reuses the\nexisting producer and Finish at the actual returned heap. The flag-disabled\nbranch does not run enabled guard/worker effects.\n\nExisting native or worker interruption observations retain their reached\nstate and query memos. Returning that observation is not a whole-dispatch\nresume implementation. Global unfolding evidence remains logical Post and\nCallReads, not an invented computational return. Native cached indexes,\nroot-flag provenance, handle/container extraction and full terminal scheduling\nremain separate. H6 stays strongest; the whole goal is ACTIVE/incomplete.\n\nWork retains the entire baseline, actual frozen contracts, all raw inputs,\nreports, failures and complete resource receipts. Prior publication contains\nexactly26 actual custody inputs. The separately sealed clarification is a\nretained current design input, not an invented27th post-seal path.\n\nRun verify-checkpoint.py with --root set to the repository root. Baseline\nblobs/modes/refs/stashes/worktrees, nine exact document inverses, one Audit\nprepend, public actual axiom subsets and complete cap families are checked.\nForce-add every manifest path and SHA256SUMS, including ignored raw logs.\nPublication requires sealed-path membership in HEAD and exact index/tree/file\nbytes and modes, the singleton push URL and ordinary formalize destination.\nNo future check result, seal or publication success is assumed. The six\nimported Haskell repair handoffs stay first in FINDINGS; no Haskell change\nor whole runtime, solver, resource or convergence result is claimed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
