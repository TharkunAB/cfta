import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-parent.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
source = ROOT / 'lean/MicroCFTA/SourceCurrentActualParentNativeStores.lean'
selected = json.loads((HERE / 'selected-sources.json').read_text())
digest = hashlib.sha256(source.read_bytes()).hexdigest()
assert digest == selected[str(source.relative_to(ROOT))]['sha256']
assert not (HERE / 'parent-strict-1.log').read_bytes()
expected = json.loads((HERE / 'attempt-expectations.json').read_text())
audit = (HERE / 'audit-2.log').read_text()
jobs, dependencies = expected['audit_jobs'], expected['audit_dependencies']
assert f'Build completed successfully ({jobs} jobs)' in audit
assert f'{dependencies} MicroCFTA theorems' in audit
commands, failed = expected['actual_lean_lake_jobs'], expected['nonzero_lean_jobs']
update = f'''## Current native stores through every completed Parent branch

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-general-parent-native-stores.md`.

ActualParentNativeStores.parent retains ONE numeric Parent receipt and
proves positive native Support, causal Mu History, conditional Merge
Stored Plain and positive Merge Support at that exact returned state.
It covers raw rejection, unchanged children, early erasure, stopped Scan,
completed Required/pass, and both final constructor outcomes. Internal
class children remain separate from the sentinel's returned children.

The proof inverts the same receipt's source reads. Stopped Scan derives
its actual new inventory from existing ScanSoundness on that SAME Scan.
Completed work uses the same Scan/Retained/Required/Pass cuts, exact global
memo bundles, original false primary gates and RequiredPositiveChronology.
The constructor uses actual nodeRecords equality for causal retention.
Growth or native table equality alone does not create this History.

Genuine initial Context/Frame/Fits/Live/Reserved, normality, native
positive Support, causal History and both additional Merge laws remain.
Current comes from Frame. Numeric reservation derives entry Scan Ranges.
The theorem adds no caller graph, Ranges or future-return oracle.

Strict, complete FULL and independent review pass. Audit passes {jobs}
jobs /{dependencies} dependencies. {commands} actual Lean/Lake commands
include {failed} retained failed commands: author strict1 and root Audit1.
Audit1 had a misplaced import; Audit2 passes with it correctly placed.
The prelaunch stopped-inventory
correction is separately preserved and ran no failed proof command.
Selected checks are clean; the old Audit warning remains. Counts do not
measure completion. No canonical or constructed job is added.

The audit further narrows the next work. Existing OuterInitialActual
already supplies unrestricted completed-sibling Post/Frame/Fits/Carrier.
Existing OuterInitialPrefix.reached also supplies exact current resources,
SeedTrace and scheduled Room at UNFINISHED prefixes, from genuine initial
Room and inputs, without a future outer return. Existing normality laws
cover all Parent and outer stopping outcomes. Reuse these APIs unchanged.
The new four-law completed outer transport, its prefix extension and the
same-writer resource ledger remain. Establishing the broader initial
resource contract, owner exclusion, renewal, retention, outer completion,
convergence and Haskell refinement remain open.

All old sources and version exceptions remain. Haskell/packages/main,
stashes and other worktrees stay unchanged. No new Haskell defect or repair.
FINDINGS keeps its repair index FIRST. The full goal stays active.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
Every literal successful Parent branch now preserves positive native
Support, causal History, conditional Merge Stored Plain and positive
Merge Support while retaining ONE exact numeric receipt. Both stopped
Scan and rejected final constructor cases are included. Initial semantic,
numeric, normality and positive-store contracts remain genuine premises.
The actual final constructor retains nodeRecords for causal History.

Strict/FULL/independent review pass; Audit {jobs} jobs /{dependencies}
dependencies. {commands} actual commands include {failed} retained failed
commands: author strict1 and root Audit1. Corrected Audit2 passes.
The separate stopped-inventory source correction occurred before
compilation. Existing OuterInitialPrefix.reached ALREADY produces ordinary
resources at unfinished prefixes from initial scheduled Room, without a
future completion. New outer four-law transport and correlated historical
writer resources remain, followed by owner exclusion, renewal, retention,
completion, convergence and Haskell refinement. Counts are not completion.
No Haskell source, runtime result, imported main or external repair changes.
Read `lean/notes-current-general-parent-native-stores.md`. Goal active.
The external Haskell repair index stays FIRST.
'''
note = f'''# Native stores through every completed Parent

Updated: {now}. Proof: `{proof}`.
SourceCurrentActualParentNativeStores has {len(source.read_text().splitlines())}
lines, two private helpers and sole public parent theorem. Source SHA256:
{digest}.

For every literal successful allocated Parent worker return, genuine
initial Context, Frame, Fits, LiveInputs and Reserved produce one numeric
Parent receipt. Additional initial UnionNormal, positive native Support,
causal Mu History from empty, conditional Merge Stored Plain and positive
Merge Support produce those last four laws at the exact final checked
state and Merge memo. Frame supplies Current. The existing numeric receipt
retains the exact graph, strict reads, semantic law, Post, Frame and Fits.
This is a conditional preservation theorem. It does not derive its initial
contracts from arbitrary successful machine execution.

The proof calls ActualParentSemanticReads.parent once. It inverts that
receipt's own reads through rejection or the actual local reduction and
final constructor. It keeps the complete result, checked state, fourth
memo and Merge memo fixed. No selected-stage graph is a caller premise.

Raw rejection uses its actual reject receipt. Unchanged and early erasure
use the actual precheck receipt and literally unchanged native state.
Classes derive genuine entry-indexed Scan Ranges through the existing
Parent/Local/Classes reservation and ScanNumeric producer. Its independent
completion graph is discarded. Source reads retain the actual Scan.

Stopped Scan can perform native queries before it stops. ScanNativeStores
returns Current, positive Support and causal History at that actual cut.
ScanSoundness on the SAME Scan derives its new inventory and admission.
The old native table inventory cannot simply be retained after allocation.

Completed Scan derives its exact scan-memo validity, Required receipt and
prepared global memo validity from the same reads. Retained supplies the
original coherent active records. selected_primary gives original-forest
false gates at the actual final Scan heap. Worker completion and the
existing UnionNormalScan law give normality at that same cut.
RequiredPositiveChronology runs once on the actual Required receipt and
PassReads. Its four returned store laws concern the same complete pass
return. The original forest, prepared forest and actual class output are
separate indexed values. Empty retained records remain covered.

Final MkEdge.finite is aligned with the literal build by full pair and
Except injectivity. Its physical receipt gives genuine final readiness,
extension and unchanged native tables. SupportAdvance preserves positive
Support. The actual MkEdgeAllocation.build_receipt/work retains physical
nodeRecords in BOTH acceptance branches. This yields NoNewMu and an
actual History.retain interval. The prior History composes with it.
This step does not infer History from growth alone. Internal class children
need not equal the sentinel's result.children. Both final outcomes work.

Root read the full 259-line draft and every later source delta. Independent
review caught an invalid old-inventory At.advance at stopped Scan before
any proof command. The corrected branch calls existing ScanSoundness on
the same actual Scan. The unexecuted draft, exact patch and separate
erratum remain. This adds no premise and changes no public result.

Strict1 retained actual elaboration errors in an acceptance-test case
split and a beta-wrapped Scan equation, plus an omit style warning. The
repair uses the literal accessor expression, beta-reduces the same Scan
equation and localizes a private instance binder. The public signature
stays byte-identical to the approved proposal. Selected/root strict logs
are empty. Complete FULL uses all eight settings, identical checked and
printed types, complete proof and standard axioms. Independent review
discloses authored foundations. FULL has 8857109 bytes and SHA256
169f2c16b7183f23c109ff6b511eac29332ab56760146cf197a5de2d6e1568d6. All {commands} actual Lean/Lake commands and {failed}
failed commands remain. Root Audit1 also failed because its new import
was outside the initial import block. The exact input, raw log and separate
erratum remain. Audit2 passes with that one import correctly placed. The
Parent source stays unchanged. Audit passes {jobs} jobs /{dependencies} dependencies;
only the old ClosedCompletion warning remains. No canonical or constructed
job ran. Every command retains fresh usage and effective max/high 4 GiB,
zero swap and five-minute limits.

The source-only outer audit refines the earlier boundary. Existing public
OuterInitialActual handles unrestricted completed node/body/rows/
descendants/children/walk calls. OuterInitialPrefix.reached also handles
literal UNFINISHED prefixes. It retains the same Reached-indexed SeedTrace,
exact Post/Frame/Fits/Carrier/Inputs and current scheduled Room, from real
initial resources and Room, without any future enclosing return. Existing
UnionNormalLocalParent and UnionNormalOuter laws preserve normality for
all stopping outcomes. Resident Mu reconstruction retains the whole caller
under the existing physical probe invariant. No uncapped opaque-Mu positive
ancestry law is needed for that reconstruction branch.

The next proof should add only the four new store laws through completed
outer calls, using the existing scheduled semantic/numeric producers at
each completed head. A following Reached induction can add those laws at
the exact unfinished cuts. It must not copy an old inventory or Fits after
real allocations. A historical writer ledger must retain initial semantic,
numeric and positive-store contracts inside ONE actual writer existential.
Old SupportedWritten AND an independent new existential is insufficient.
Current reader laws do not supply historical writer-entry laws.

Connecting genuine initial Room and inventories to broader starts, actual
owner exclusion, renewal, final retention, outer completion, convergence
and Haskell refinement remain open. The selected owner geometry and delayed
descent results remain separate consumers. All old proofs, counterexamples,
logs, source versions and controlled exceptions stay. Haskell/packages/main
remain unchanged. FINDINGS keeps the repair handoff first. Goal active.
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
(ROOT / 'lean/notes-current-general-parent-native-stores.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
