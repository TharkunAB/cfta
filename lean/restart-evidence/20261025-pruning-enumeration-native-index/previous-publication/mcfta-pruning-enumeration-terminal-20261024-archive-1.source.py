import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-terminal-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-terminal'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == '6f9984db794cfbbc4f64907cb4898ec7e6624bbf719cd6aefe0426923d0b78c8'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-terminal-20261024-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-terminal-20261024-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-terminal-20261024-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-terminal-20261024-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-terminal-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationTerminal.lean', production / 'SourcePruningEnumerationTerminal.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-terminal.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-terminal-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Checked terminal-arm composition\n\nThe staged action uses the existing TerminalPrefix, ordered Fold and IncomingNode at their SAME returned endpoints. Incoming Empty rejects before Prefix. Prefix preserves the actual recorded order and duplicates. Its distinct sorted nonwinner keys are used only for waiting transfer. Fold [] stops before IncomingNode, incoming count gains or a returned fragment. Unmatched raw shapes and native/worker interruptions remain explicit existing Sum/Except outcomes.\n\nOn a successful Fold singleton, IncomingNode performs the actual representative read, checked query when the old handle is present, then value write and ancestry inheritance before Empty rejection. The read endpoint and write/inherit prefix endpoint stay distinct. Raw [] returns no successful enum state. A successful row returns Fragment.hole winner at its actual written state; it does not install an enumerated hole at winner. The later enumerateOutUVarWith store at the captured original uv remains separate.\n\nThe action returns the moved waiting map with its outer read/staging endpoint. That pair is staging data, not the final waiting table for a returned raw state. gained_correct independently derives the logical gained-only count map at the actual incoming write/inherit prefix, including an Empty rejection. Its fixed roots and external waiting parameters do not establish native IntMap/index extraction. Canonical zero-entry facts remain necessary for map equality.\n\nThe finite producer assumes genuine initial Safe/Roots/counts, pending slots, current native Context/realization, an available closed nonempty incoming Value and allocated suspended references. It derives one actual Prefix, Fold and IncomingNode execution with retained bounds, current Post/receipt/language evidence and separate read/write endpoints. Current reached Fold.Ranges and conditional incoming WordRanges are explicit; no successful future execution is assumed. Runtime early Empty is outside this nonempty producer domain.\n\nThe selected interface is run, gained_correct and run_complete. One local named List Monad header is selected, with no LawfulMonad or new carrier. Root selected300–450 ordinary lines and hard650 before owner/body freeze. Actual immutable owner metadata supplies the complete literal contracts, counts and exact schema. No check outcome is predicted.\n\nWork retains all137786 baseline files/modes/refs/stashes/worktrees, nine exact document inverses, one Audit prepend, all real failed input/raw reports, complete public output/actual allowed axiom subsets and all six-artifact resource families. Exactly26 prior FoldInvariants publication inputs and separately sealed assessment/peer context remain protected. The current fresh owner is copied once. Earlier amendments and revisions stay baseline history. No current revision or failure is invented.\n\nRun verify-checkpoint.py with an explicit repository root. Force-add every manifest path and SHA256SUMS, including ignored logs. Publication requires every sealed path in HEAD, exact filesystem/index/tree/modes and a singleton destination for ordinary formalize push. Root supplies actual build/public/axiom outcomes after execution. No future check, seal or push result is asserted.\n\nOuter terminal/descendant partitioning, root-flag provenance, later original-uv installation, native maintained indexes/Int extraction, initial-only mixed-query admission, Safe/LiveRoots preservation and the complete shared driver remain open. H6 stays strongest; the whole goal is ACTIVE and incomplete. Full typing/pruning/solver/runtime/resource/convergence boundaries remain. The optimized core and earlier proofs stay protected. The six imported Haskell repair handoffs remain first in FINDINGS. No Haskell source change is claimed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
