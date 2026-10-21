import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-done-or-exhausted.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
source_sha = 'b6485bba37a65fd0358d00517605198c7ad74d53d1341d13ab0c6093f10cc3ce'
assert hashlib.sha256((ROOT / 'lean/MicroCFTA/SourceCurrentOuterDoneOrExhausted.lean').read_bytes()).hexdigest() == source_sha
assert not (HERE / 'done-or-exhausted-strict-1.log').read_bytes()
audit = (HERE / 'audit-1.log').read_text()
assert 'Build completed successfully (3615 jobs)' in audit and '75096 MicroCFTA theorems' in audit
assert {v['path'] for v in json.loads((HERE / 'components.json').read_text())} == {'done-or-exhausted', 'independent-review', 'adequacy-plan', 'adequacy-plan-review'}
full = (HERE / 'done-or-exhausted/outer-done-or-exhausted-public-1.log').read_bytes()
assert len(full) == 225212 and hashlib.sha256(full).hexdigest() == '660f2aced7f49b23d8a1bcb5ab1449abe804a9b39181259ae5c0398fa3658733'
update = f'''## Current formalized outer worker returns or exhausts outer fuel

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-outer-done-or-exhausted.md`.

OuterDoneOrExhausted.done_or_exhausted now proves that the actual formalized
outer run either returns normally or reports outer-fuel exhaustion.
It excludes every other modeled failure under its stated initial packet.
Both alternatives retain the same chosen phase, nine lower-worker fuels,
conjunction budget and actual returned Caller. ActiveAncestry.run erases
only successful phase output. This theorem records the resulting Unit
and state. It does not separately return that erased node or child list.

The exact 34-line public type keeps genuine initial Context, Frame, Fits,
annotation carrier, phase Inputs, chosen-fuel forecast Room, UnionNormal,
native positive Support, causal History, both Merge laws, writer Origins,
NodeStored, InputsClosed, initialNodeIdle and initial EdgeIdle. It also
keeps all nine phaseNeed inequalities. These remain hypotheses. Empty
outer tables are permitted but not required. Appropriate warm suspended
and returned cells remain permitted. No future success or supplied cut
is assumed, and no sufficient OUTER fuel is assumed or constructed.

The 83-line proof makes one actual Outcome split. It calls the checked
LocalFaults.failed_cases once. Existing Parent, edgeMemo, busy-node,
reference and absent-node exclusions consume that SAME failed equation
and Caller. Exhaustion remains as the only possible failed branch.
No new induction, helper predicate or fault datatype is introduced.
The complete source passed unchanged below the 150-total-line ceiling.

Author strict1 and root strict logs are empty. The sole complete FULL,
independent review and Audit pass: 3615 jobs /75096 dependencies.
Four actual Lean/Lake commands all pass. No new warning or compiler repair.
The old Audit warning remains. Whole checked/printed type identity,
all eight printer settings and actual standard three axioms pass.
No private names occur in the public type. No canonical, infrastructure,
constructed, runtime or reviewer proof job ran. Counts are not completion.
All earlier failed checks, counterexamples and sealed evidence remain.

The largest execution gap is now SOME sufficient OUTER fuel together with
noncircular INITIAL capacity for that SAME run. Chosen-fuel scheduling,
classification and stability of an existing success do not supply it.
The reviewed next survey finds existing one-Parent numeric producers
sufficient for local growth bounds. A duplicate wrapper adds no result.
It proposes a concrete rank envelope over Lex(count,mass), with the evolving
guard alphabet and numeric profile as additional input. A count decrease
can increase mass. Sequential siblings must carry the predicted growth.

That envelope C is UNDEFINED and unproved. No fuel F is constructed by the
survey, and no public adequacy header or implementation is proposed.
Finite rank images, joined profiles and alphabets, retained intermediate
Parent peaks, cumulative worker-fuel arithmetic and same-cut physical
coverage still need proofs. Initial Room for the root schedule must also
cover every controlled Parent reservation. Prove profile domination or
check an initial finite join with C.output and prove its coverage.
The lower fuels need analogous domination or an accumulated initial-only
maximum L. Preserve the same global initial packet and literal Reached
cuts; restarting Prefix at a controlled child needs extra unproved Room.
The ten-source, twenty-range survey makes these open obligations explicit.
NativeWidthTrace bounds a supplied trace. It does not widen state.

General finite renewals, final retention, successful completion, convergence,
broader resources and Haskell refinement remain open. Whole-library
termination is not proved. The broadest semantic claim remains exact
finite-term language preservation for a supported successful traversal
with empty inherited constraints. General inherited constraints give
narrowing, with exactness under inherited satisfaction.

Haskell, packages, imported main, stashes and other worktrees stay unchanged.
No new Haskell defect or repair. FINDINGS keeps its external repair index
FIRST. Work continues at the user's request.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
The actual formalized outer run now returns normally or reports outer-fuel
exhaustion under its complete stated initial packet. Every other modeled
failure is excluded. The theorem keeps closure/store laws, both idle laws,
genuine semantic/resources laws and all nine lower-fuel inequalities.
It preserves the chosen phase and actual resulting Caller. The successful
phase output is erased to Unit by the existing run definition.

The unchanged 83-line proof has the exact approved 34-line public type.
One actual Outcome split and one LocalFaults call compose the existing
fault exclusions at the same failed equation. Author/root strict, sole
complete FULL, independent review and Audit pass: 3615 jobs /75096
dependencies. Four actual commands all pass without new warnings or
source repairs. Whole type identity, all eight settings and actual
standard axioms pass. No runtime, canonical, infrastructure, constructed
or reviewer proof job ran. All prior failures and counterexamples remain.

SOME sufficient OUTER fuel and matching noncircular INITIAL capacity remain
unproved. The next survey proposes an UNDEFINED controlled Lex(count,mass)
envelope with evolving profile/alphabet, finite joins and sibling folds.
Existing one-Parent numeric producers need no new wrapper. Initial Room
must cover controlled Parent peaks, and lower fuels must cover their
forecasts. Same-root physical coverage, cumulative fuel arithmetic,
finite renewals, retention, completion, convergence, broader resources
and Haskell refinement remain open. No C or F is constructed by the survey.
Its ten sources and twenty ranges are reviewed source evidence only.
Counts are not completion. No Haskell source, runtime or repair changes.
Read `lean/notes-current-outer-done-or-exhausted.md`.
The external Haskell repair index stays FIRST.
'''
note = '# Formalized outer execution: result or outer-fuel exhaustion\n\n' + update + f'''
The selected source SHA256 is {source_sha}.
The sole complete public print has 225212 bytes, SHA256
660f2aced7f49b23d8a1bcb5ab1449abe804a9b39181259ae5c0398fa3658733.
Its printer SHA256 is
a4cf1653140fbc76362863c31914a57dda917de228caa2a6011c2853884719f2.
The normalized public type has 16923 characters. The complete printed
proof has 163301 characters. Root independently ran the hardened reader
and read the whole checked type. After one display was truncated, root
read its complete middle lines 130 through 285 again. The source and
full raw output remain unchanged. No extra compiler command was needed.

The frozen source-only plan keeps its original unchecked LocalFaults cue,
exact one-line status correction and later historical status record.
A separate proof-package record identifies the actual compiled dependency.
No historical plan is rewritten after its theorem becomes checked.

The adequacy survey is a mathematical design and source audit. It defines
no C, constructs no F and supplies no adequacy theorem. It keeps the actual
initial-data capacity condition distinct from a desired successful run.
It also keeps fixed-width capacity and state transfer as separate issues.
The original complete plan, candidate notes, report, numbered excerpts,
critical-bridge edits, depth clarification and same-root obligation remain.
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
(ROOT / 'lean/notes-current-outer-done-or-exhausted.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
