import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-incoming-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-incoming'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'be78e347eb990b8506182fcb5b4deb484000f43cd8e9de00201ace203cbd3039'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-incoming-20261024-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-incoming-20261024-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-incoming-20261024-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-incoming-20261024-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-incoming-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationIncomingQuery.lean', production / 'SourcePruningEnumerationIncomingQuery.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-incoming-query.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-incoming-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Checked replacement for incoming node values\n\nThis dependency takes two supplied complete available closed native values in the SAME current heap. Existing TargetQuery.finite constructs the actual next inventory, query, checked endpoint and complete Receipt. The derived Demand execution is stable at every sufficient larger native fuel. No second pending source slot, decoded slot fiction, replacement Graph or desired computed result is supplied.\n\nThe native intersection always runs, including when checkEmpty is false. The false flag skips only the descendant query guard and fourth-memo worker. It retains the queried endpoint, original fourth memo, original query memos and computed query. Enabled checking uses the existing EnabledEmpty.check and concrete SourceEndpointMemo.run. A false reachability result retains the checked query state while updating query memos. A true reachability result retains the actual conjunction Call and CallReads with the physical endpoint and logical global memo evidence. Stable p/h bounds describe that SAME call.\n\nThe theorem derives replacement Empty on true answer and query on false answer. Query may already be Empty on false. AnswerSound provides no acceptance or nonempty conclusion for false. Existing readback derives the encoded handle and actual lookup from the SAME complete replacement. Its language is the intersection of both supplied inputs. Full Receipt, Post, query memo equality and unfolding extension remain distinct evidence. Current-entry WordRanges remains explicit; this is not initial-only resource admission for a future sequence.\n\nThis component has one theorem complete and adds no definitions, actions, instances, helper, carrier or induction. The actual owner supplies the exact contracts and hard source cap. No enumeration state/write, ancestry effect, source elimination or final raw Empty guard is performed. The full incoming-node operation remains a separate consumer: actual pending-root observation, optional-old bypass, target write and expansion ancestry inheritance BEFORE Empty rejection.\n\nWork retains all baseline blobs/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, full actual public output, allowed axiom subsets including empty sets, every real failed input/raw report and all six-artifact resource families. Prior custody is exactly26 actual inputs. The primary TerminalPrefix V2 assessment and independent review already match sealed copies. Prior owner V1/V2/V3 and all prior failures remain protected by the baseline. No current revision or failure is invented.\n\nRun verify-checkpoint.py with an explicit repository root. Force-add every manifest path and SHA256SUMS, including ignored raw logs. Publication requires every sealed path in HEAD, exact filesystem/index/tree/modes, a singleton push URL and ordinary formalize push. Root supplies actual build/public/axiom outcomes after execution. No future check, seal or push result is asserted.\n\nH6 remains strongest and the whole goal remains ACTIVE and incomplete. Full terminal composition, initial-only range admission, native cached indexes/Int/IntSet extraction, code generation, full typing/pruning/solver/runtime/resources/convergence remain separate. Six imported Haskell repair handoffs remain first in FINDINGS. No Haskell source change is claimed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
