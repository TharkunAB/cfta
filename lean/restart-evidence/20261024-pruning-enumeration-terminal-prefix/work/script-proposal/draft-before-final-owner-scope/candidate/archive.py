import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-terminal-prefix-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-terminal-prefix'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == '334494aa557677ceaa146e3f35b8fbc453ba6a773429b8a6f47462611acea870'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-terminal-prefix-20261024-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-terminal-prefix-20261024-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-terminal-prefix-20261024-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-terminal-prefix-20261024-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-terminal-prefix-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationTerminalPrefix.lean', production / 'SourcePruningEnumerationTerminalPrefix.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-terminal-prefix.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-terminal-prefix-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("# Native terminal representative and waiting prefix\n\nThe selected prefix scans ALL original suspended variables, unions the first ORIGINAL variable with each remaining ORIGINAL variable, resolves the actual winner and transfers distinct old nonwinner waiting buckets. It retains the ORIGINAL recorded order, including duplicates and the winner, for the later checked assimilation fold. It does not union the recorded-root list or deduplicate that later fold.\n\nThe finite producer uses genuine initial safety, allocated input references and pending-input conditions, together with an initial root map and correct canonical waiting counts. Safe alone does not establish those root/count premises. Existing finite representative/union/mapM/forM producers construct the observations; observed-success schedule/canonical theorems then identify the SAME actual endpoint. No scan, union, winner or desired-output equation is assumed as a replacement for construction.\n\nThe action uses the existing enumeration state and existing product result, without a replacement Graph, new carrier or shared native/enumeration monad. This prefix changes the union forest and computes the transferred waiting-count view in its existing product result. Values and the required nonforest fields remain unchanged. The action has no native Caller or memo parameters and executes no native Caller or memo actions. Pending slots and the actual winner's pending slot provide the later fold domain. No Safe/LiveRoots or compression Frame is asserted at the union-only endpoint.\n\nWork retains all baseline blobs/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, complete actual public signatures and permitted axiom subsets including empty sets, failed inputs/raw reports and six-artifact resource families. Root supplies actual check counts/results after execution. Prior custody is exactly26 actual inputs; Fold's58 evidence-data whitespace diagnostics are embedded in its summary, not a27th input, new Lean attempt or failed seal. The sealed assessment and its independent review remain protected. Older Fold V1/V2/V3 owners and real failures remain unchanged in the baseline. No current owner revision or failure is invented.\n\nRun verify-checkpoint.py with an explicit repository root. Force-add every manifest path and SHA256SUMS, including ignored raw logs. Publication requires every sealed path in HEAD, exact filesystem/index/tree/modes, a singleton push URL and ordinary formalize push. No future check, seal or publication result is asserted.\n\nH6 remains strongest; the whole goal is ACTIVE and incomplete. Initial-only range admission for the later checked fold, native root flags, cached indexes, Int/IntSet extraction, incoming-node write-before-Empty merge and full terminal/driver language remain separate. Six imported Haskell repair handoffs remain first in FINDINGS. No Haskell source change, code generation, solver or runtime/resource/convergence result is claimed.\n")

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
