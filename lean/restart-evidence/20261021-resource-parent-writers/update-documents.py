import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-writers.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
source = ROOT / 'lean/MicroCFTA/SourceCurrentResourceParentWriters.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == '404f9ba2b58cbdb403608465e375d6f1af66686aaa3201288ba6ea219f75f4d2'
assert not (HERE / 'writers-strict-1.log').read_bytes()
audit = (HERE / 'audit-1.log').read_text()
assert 'Build completed successfully (3597 jobs)' in audit and '74955 MicroCFTA theorems' in audit
assert {item['path'] for item in json.loads((HERE / 'components.json').read_text())} == {'writers','independent-review','prefix-plan'}
full = (HERE / 'writers/resource-writers-public-1.log').read_bytes()
full_sha = hashlib.sha256(full).hexdigest()
update = f'''## Current original Parent writer resources

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-resource-parent-writers.md`.

ResourceParentWriters now records one complete historical Parent entry.
Written keeps the actual caller, literal Parent execution, inventory,
profile, global memo bundle, Context, Frame, Fits, request readiness and
residency, field/child availability, numeric reservation and five store
laws together in ONE existential. Origins attaches this joint witness to
the captured request and complete value in each returned edge cell.

initial proves Origins for empty edge tables. edge_call preserves Origins
and returns Written for its actual request/result. Cold calls use the same
captured owner and running caller. Warm hits recover the old stored witness;
current readiness/coherence identifies the full request. The reader does
not supply facts about the old writer. Generic memo lifecycle laws protect
the actual evaluating handle. No old weak writer record is conjoined with
an unrelated stronger existential.

This is one local completed-call theorem. Its integration through recursive
outer workers and unfinished prefixes remains. Completed outer store laws
are already proved; their unfinished-prefix extension has a frozen exact
plan. Initial semantic, numeric and store contracts remain genuine inputs.
Owner exclusion, renewal, final retention, general outer completion,
convergence, broader initial-resource production and Haskell refinement
remain open. The whole-library termination target is unchanged.

Root strict, complete FULL and independent review pass. Audit passes 3597
jobs /74955 dependencies. Five actual Lean/Lake commands include one retained
strict failure with three eliminated-name references. Selected/root strict
logs are empty. All four public heads have identical complete checked and
printed types, all eight settings and only standard axioms. No canonical,
infrastructure, constructed or reviewer proof job ran. Only the old Audit
warning remains. Counts do not measure completion.

All old sources, evidence and version exceptions remain. Haskell/packages/
main, stashes and other worktrees stay unchanged. No new Haskell defect or
repair. FINDINGS keeps the external repair index FIRST. Goal active.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
One returned edge cell now retains ONE complete original Parent execution
and its correlated historical resources/store laws. Local cold calls
install the actual writer; local warm hits recover that same stored witness.
Current coherence proves full request identity without inferring old facts
from the reader. Empty tables establish the initial ledger without history.

Strict/FULL/independent review pass; Audit 3597 jobs /74955 dependencies.
Five actual commands include one retained failed strict, no warnings there.
Selected checks are clean; only the old Audit warning remains. Four public
heads are two definitions and two theorems. No canonical, infrastructure,
constructed or reviewer proof job. Prelaunch source and exact repairs stay.
Recursive ledger integration, unfinished-prefix store transport, owner
exclusion, renewal, retention, completion, convergence, broader initial
resources and Haskell refinement remain. Counts do not measure completion.
No Haskell source, runtime result, imported main or external repair changes.
Read `lean/notes-current-resource-parent-writers.md`. Goal active.
The external Haskell repair index stays FIRST.
'''
note = f'''# Resource witnesses from original cached Parent writers

Updated: {now}. Proof: `{proof}`.
SourceCurrentResourceParentWriters has 250 lines and four public heads:
Written and Origins are definitions; initial and edge_call are theorems.
Selected SHA256:
404f9ba2b58cbdb403608465e375d6f1af66686aaa3201288ba6ea219f75f4d2.

Written uses ONE existential for every lower fuel/budget, the complete
historical caller, exact returned checked state/fourth/Merge, global memo
bundle, inventory and profile. Its same literal Parent.done starts from
that caller's checked/fourth/Merge. The same entry has Context, Frame,
Fits, inherited readiness, resident edge, conditional field/inherited/child
availability, residentReserved, UnionNormal, positive native Support,
Nonempty causal Mu History from empty, conditional Merge Stored Plain
and positive Merge Support. No resource witness is independent of the
recorded writer. Current can later derive from its same Frame.

Origins is public FlatMemoThunk.Valid with the generic CellSpec Written.
It ties each complete returned value to the cell's exact captured request.
initial is vacuous at empty edge tables. edge_call assumes genuine entry
Context/Frame/Fits/readiness/residency/numeric Reserved, prior Origins and
the five store laws. It returns Origins at the actual returned caller and
Written at the actual requested edge and complete result. A successful raw
worker equation does not create any entry resource requirement.

The cold branch uses actual CallSteps.edge_start. The running caller keeps
the literal checked/fourth/Merge components. The same context supplies the
captured owner and full request identity. Inverting actual edgeBody.done
retains its literal Parent.done and that SAME running caller/resources.
The body leaves outer edge cells unchanged. Generic finish_spec installs
the one witness at the actual protected evaluating handle and retains all
other cells.

The warm branch uses demand_ready_original, lookup validity and the
linked table cell to recover the ORIGINAL stored Written. Current ready
constraint identity and resident-edge coherence identify its full request
with the candidate, including inherited payload and complete edge value.
No historical resource or history law is inferred from the reader state.
No event uniqueness or equality between independently chosen global memo
bundles is needed. The old weak OuterParentHistory source stays unchanged.

Root and independent review read the complete original source and each
exact delta. Before launch, request_eq moved before unrelated section
instances; its proof stayed unchanged. The original unexecuted source and
zero-job note remain. Strict1 genuinely failed at three references removed
by cases actual. Its exact five-line repair uses the surviving result/after
variables from the SAME equation. No public type, premise or proof route
changed. Strict2 and root strict passed with literal empty logs.

ONE complete FULL for all four heads has {len(full)} bytes and SHA256
{full_sha}.
Each definition/theorem has all eight printer settings, complete checked/
printed type identity, no private public-type identifier, no omissions and
exactly propext, Classical.choice and Quot.sound. The selected source
stayed unchanged after its passing strict. Three author proof commands
plus root strict and Audit give five actual Lean/Lake jobs with one failed.
No canonical, infrastructure, constructed or reviewer proof job ran.
Every actual command retains fresh usage, effective max/high 4 GiB,
zero swap and a five-minute cap. Audit passes 3597 jobs /74955 dependencies
with only the old ClosedCompletion warning.

Completed recursive outer store preservation is already proved. Existing
OuterInitialPrefix.reached already supplies ordinary same-cut resources
without a future enclosing return. The frozen next prefix plan adds only
the new five state laws, retaining all old resource tuple clauses. It uses
a private store-only induction on literal ExecutionAncestry.Reached and
completed preceding siblings. It does not require richer ActiveAncestry
graph premises or copy the old resource induction. Its proposed source
and type are not counted as a proved prefix theorem in this checkpoint.

The new local Origins still needs propagation through all completed outer
phases and actual unfinished prefixes. Those later proofs must combine
new completed-store endpoints and genuine scheduled resource producers at
each SAME writer entry. Parent certificate/owner-pair consumers can then
use the stored resources. Do not combine an old weak Written with a new
unrelated existential or obtain historical facts from current growth.

The broad semantic statement remains conditional: a supported successful
model traversal with empty inherited constraints preserves exactly the
accepted finite terms. The whole-library target requires termination and
each public Haskell specification from valid supported INITIAL inputs.
Owner exclusion, renewal, bounds on fresh calls, final retention, general
outer completion, repeated-pass convergence, broader initial-resource
production and Haskell refinement remain open. Counts are not completion.
All old proofs/counterexamples/logs and version exceptions stay. Haskell/
packages/main remain unchanged. FINDINGS keeps its repair index first.
The full goal stays active.
'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    if name == 'FINDINGS.md':
        prefix = '# Current formalization findings\n\n## Haskell fix handoff for external work\n'
        marker = prefix + '\n' + (HERE / 'haskell-repair-index.md').read_text().rstrip() + '\n'
        assert original.startswith(marker)
        rest = original[len(marker):]
        assert rest.startswith('\n')
        changed = marker + '\n' + findings + '\n' + rest[1:]
        assert changed.replace(findings + '\n', '', 1) == original
    else:
        first, rest = original.split('\n', 1)
        changed = first + '\n\n' + update + rest
        assert changed.replace(update + '\n', '', 1) == original
    (ROOT / name).write_text(changed)
(HERE / 'current-update.md').write_text(update)
(HERE / 'findings-update.md').write_text(findings)
(ROOT / 'lean/notes-current-resource-parent-writers.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
