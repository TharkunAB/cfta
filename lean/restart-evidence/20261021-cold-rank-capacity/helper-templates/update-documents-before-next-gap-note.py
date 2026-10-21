import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-semantic.txt').read_text().strip()
cfg = json.loads((HERE / 'checkpoint-result.json').read_text())
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
for tag, module, strict in [
    ('cold-capacity', 'SourceCurrentColdRankCapacity', 'producer-strict-1'),
    ('cold-semantic', 'SourceCurrentColdRankSemantic', 'semantic-strict-1'),
]:
    source = ROOT / 'lean/MicroCFTA' / (module + '.lean')
    pin = cfg['modules'][tag]
    assert hashlib.sha256(source.read_bytes()).hexdigest() == pin['source_sha256']
    assert len(source.read_text().splitlines()) == pin['source_lines'] < 250
    assert not (HERE / (strict + '.log')).read_bytes()
    full = (HERE / pin['full_relative_path']).read_bytes()
    assert len(full) == pin['full_bytes']
    assert hashlib.sha256(full).hexdigest() == pin['full_sha256']
audit = (HERE / 'audit-2.log').read_text()
assert f"Build completed successfully ({cfg['audit_jobs']} jobs)" in audit
assert f"{cfg['audit_dependencies']} MicroCFTA theorems" in audit
assert {item['path'] for item in json.loads((HERE / 'components.json').read_text())} == {
    'capacity-plan', 'semantic-next-plan', 'semantic-plan-review',
    'cold-capacity', 'capacity-independent-review', 'cold-semantic', 'semantic-independent-review'}
update = f'''## Cold node termination and exact stored language

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-cold-rank-semantics.md`.

ColdRankCapacity.constructed_initial_node_call constructs a genuine cold
initial packet at a sufficient mathematical width. Its inputs are a valid
initial constraint cache, actual guard-allocation History, literal source
syntax whose guards occur in that History, formula operations, a solver,
and a budget. It assumes no Room, Fits, Context or successful outer call.

The actual source build supplies one value and heap. Their counters,
literal guard alphabet and stored mass supply the initial seed. The
unchanged finite envelope C supplies W and an output profile. A join
covers that profile and the old schedule at W. roomBits supplies sufficient
mathematical width before the fresh cold caller is constructed. Actual
initialization supplies the remaining initial facts. phaseNeed supplies
all nine lower fuels. The initial constraint interner is retained.

For every outer fuel F at least W, the literal nodeCall returns the SAME
result and complete final caller. The initial state and nine lower fuels
stay fixed. Successful execution is a conclusion, not a premise.

ColdRankSemantic.constructed_initial_node_call adds availability of that
SAME result in its actual final heap and exact independent stored-value
language equivalence for every ambient and finite ordered term. It uses
the producer once. Its success at W supplies the existing semantic theorem.
The actual inherited equality payload is empty, so its satisfaction
condition holds. No second successful call or source build is assumed.
The language uses SourceEqualityPCSGuard.holds formulas solver. It remains
relative to the supplied guard evaluator.

The selected sources have 139 and 120 lines, each below its 250-line stop.
Their original 25- and 30-line headers remain retained. Each header has
one explicit alpha correction from built to _built. Types, order, lets
and conclusions are unchanged. All failed and warned inputs, raw logs,
namespace placement and two SAME-heap goal corrections remain retained.
No linter exception or declaration proof-limit increase is used.

Author/root strict checks, one sole complete FULL per module, independent
review and Audit pass: {cfg['audit_jobs']} jobs /{cfg['audit_dependencies']} dependencies.
There are {cfg['actual_jobs']} actual Lean/Lake commands, including {cfg['failed_jobs']} failure.
One earlier producer check passed with a warning. Selected strict logs
are empty. Whole checked/printed type identity, all eight printer
settings, public type scope and actual standard axioms pass. Only the
old Audit warning remains. No runtime or reviewer proof job ran.
Counts do not measure completion of the whole-library goal.

The semantic TYPE contains one existing imported private Formula equality
instance. The original reader missed its dagger spelling. An additive
scope erratum records that instance and corrects the broad metadata field.
No new private helper, premise or axiom is introduced. The original
reader, its actual output and the complete FULL remain retained.

The envelope remains noncomputable in Lean. These theorems give finite
mathematical bounds, not an executable fuel calculator or practical host
width. The coarse-capacity obstruction remains a source-only argument.
No populated warm caller is widened. Practical fixed-width feasibility,
warm-state capacity, repeated-pass convergence, declarative solver-contract
evidence, exported-table composition and concrete Haskell refinement
remain separate work. One whole-library theorem is not established.

All earlier proofs, counterexamples, marked drafts and optimized interned
sources remain. Older constructor and equality targets remain secondary
targets. All Haskell and package files remain unchanged. No new Haskell
defect or repair is claimed. FINDINGS keeps its external Haskell repair
index FIRST. Work continues at the user's request.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
ColdRankCapacity constructs the genuine initial packet, sufficient
mathematical width and nine lower fuels from actual covered source
construction and valid guard-allocation history. It proves successful
nodeCall return with the SAME result and full caller for every outer
fuel at least W. No successful-run or Room premise is supplied.

ColdRankSemantic attaches availability in that SAME final heap and exact
independent stored-value language equivalence for every ambient and finite
term. The inherited equality payload is empty. Its language is relative
to SourceEqualityPCSGuard.holds formulas solver. Success and the language
law concern the same modeled cold execution.

The 139- and 120-line sources, author/root strict, one complete FULL per
module, independent review and Audit pass: {cfg['audit_jobs']} jobs /{cfg['audit_dependencies']} dependencies.
{cfg['actual_jobs']} actual commands include {cfg['failed_jobs']} failure and one warned success.
Selected strict logs are empty. Each public header has one explicit
built-to-_built alpha correction. Original headers, complete failed inputs,
raw logs and all repairs remain. Default declaration limits, all eight
printer settings, whole type identity and standard axioms pass.
Only the old Audit warning remains. No Haskell runtime check ran.
An additive TYPE scope erratum records one existing imported private
Formula equality instance that the original name check did not report.
The theorem and its proof are unchanged. No FULL repeat occurred.

The bounds remain mathematical and the envelope noncomputable. Practical
fixed widths, populated warm-state transport, repeated-pass convergence,
solver-contract and exported-table composition, and whole-library Haskell
correspondence remain open. No Haskell source, package, repair or runtime
result changes. The external Haskell repair index stays FIRST.
Read `lean/notes-current-cold-rank-semantics.md`.
'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    if name == 'FINDINGS.md':
        marker = '# Current formalization findings\n\n## Haskell fix handoff for external work\n\n'
        marker += (HERE / 'haskell-repair-index.md').read_text().rstrip() + '\n'
        assert original.startswith(marker + '\n')
        changed = marker + '\n' + findings + '\n' + original[len(marker) + 1:]
        assert changed.replace(findings + '\n', '', 1) == original
    else:
        first, rest = original.split('\n', 1)
        changed = first + '\n\n' + update + rest
        assert changed.replace(update + '\n', '', 1) == original
    (ROOT / name).write_text(changed)
(HERE / 'current-update.md').write_text(update)
(HERE / 'findings-update.md').write_text(findings)
note = '# Cold node termination and exact stored language\n\n' + update
for tag, pin in cfg['modules'].items():
    note += f"\n{tag}: source SHA256 {pin['source_sha256']}.\n"
    note += f"Sole FULL: {pin['full_bytes']} bytes; SHA256 {pin['full_sha256']}.\n"
(ROOT / 'lean/notes-current-cold-rank-semantics.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
