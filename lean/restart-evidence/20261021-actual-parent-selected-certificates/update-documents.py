import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-selected.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
source = ROOT / 'lean/MicroCFTA/SourceCurrentActualParentSelectedCertificates.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == '0f42191fdba120681d238bc40fcde22176ff3c2ab1bebd9ff7d179f971eca732'
assert not (HERE / 'selected-strict-1.log').read_bytes()
audit = (HERE / 'audit-1.log').read_text()
assert 'Build completed successfully (3594 jobs)' in audit and '74931 MicroCFTA theorems' in audit
update = f'''## Current selected certificates from one actual Parent receipt

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-actual-parent-selected-certificates.md`.

ActualParentSelectedCertificates.selected_certificates now derives the
exact Retained records, Required receipt, PassReads and prepared global
memo validity from ONE resource-backed Parent receipt. The same receipt's
read graph supplies every selected stage and intermediate memo bundle.
Record uniqueness retains full records, trie fields, order and multiplicity.
Required and Pass uniqueness align their complete actual returns.

The result keeps that numeric receipt, actual MkEdge suffix, explicit
savedFourth = scanFourth, and HEq to the assembled live/classes/completed
graph. It also keeps all seven scanned state laws and scanned UnionNormal.
Entry Current comes from the existing OperandFrame.current theorem.
The initial numeric Scan producer supplies its entry-indexed Ranges.
Its separate completion witnesses are discarded. No caller Ranges,
Retained, Required receipt, PassReads or prepared-validity oracle remains.

Genuine Context/Frame/Fits/Live/Reserved and initial positive native
Support, causal History and UnionNormal remain. Context retains its
ordinary semantic memo laws. The later owner-pair consumer still needs
genuine conditional and positive Merge laws at that same writer entry.

Root strict, complete FULL and independent review pass. Audit passes
3594 jobs /74931 dependencies. Four actual Lean/Lake commands all pass.
FULL has 6419396 bytes, all eight settings, identical checked/printed
types, complete proof and standard axioms. No canonical, infrastructure
or constructed job. Only the old ClosedCompletion Audit warning remains.
The independent prelaunch correction fixed an ill-typed homogeneous graph
equality by returning explicit fourth equality and HEq. The original plan
and unexecuted draft remain. The corrected source passed without changes.

The sibling audit narrows the remaining work. Existing EdgeCallNumeric
and unrestricted OuterInitialActual node/descendants/rows/children/walk
APIs already return exact Post/Frame/updated Fits under real entry seed,
Carrier and Room contracts. Reuse them. Warm edge hits retain the complete
caller state. The new all-branch Parent positive Support/History and
required Merge preservation remain unproved, followed by the completed
node/descendants induction and same-writer ledger. Initial resource
contracts must still connect to the full outer proof. Owner exclusion,
renewal, retention, outer completion, convergence and Haskell refinement
remain open. Counts do not measure completion.

All old proofs, evidence and version exceptions remain. Haskell/packages/
main, stashes and other worktrees stay unchanged. No new Haskell defect
or repair. FINDINGS keeps its repair index FIRST. The goal stays active.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
Exact selected execution certificates now come from ONE actual Parent
receipt and its own read graph. The output keeps full retained records,
Required receipt, same PassReads/memo bundles, prepared Valid and seven
scanned state laws plus UnionNormal. Explicit fourth equality and HEq
retain the actual assembled graph. Entry Current derives from Frame.
Entry Ranges derive from the genuine numeric forecast. No future-state
or caller certificate oracle is added. Initial native Support/History,
normality and semantic/resource contracts remain genuine requirements.

Root strict empty; complete FULL and independent review pass.
Audit passes 3594 jobs /74931 dependencies. Four actual commands all pass.
The preserved prelaunch index correction ran no failed proof command.
Existing unrestricted completed-sibling APIs already provide numeric and
semantic resources. New positive Support/History and required Merge
preservation across all Parent/outer branches remain, along with historical
writer retention, owner exclusion, renewal, retention, completion,
convergence and Haskell refinement. Counts do not measure completion.
No Haskell source, runtime result, imported main or external repair changes.
Read `lean/notes-current-actual-parent-selected-certificates.md`. Goal active.
The external Haskell repair index stays FIRST.
'''
note = f'''# Selected certificates from the same actual Parent

Updated: {now}. Selected proof: `{proof}`.
SourceCurrentActualParentSelectedCertificates has 263 lines and one public
selected_certificates theorem. Selected source SHA256:
0f42191fdba120681d238bc40fcde22176ff3c2ab1bebd9ff7d179f971eca732.

The input contains genuine initial Context, Frame, Profile, Fits,
LiveInputs and Reserved resources, literal successful Parent/precheck/
RecordScan/Required/Pass cuts, and initial positive native Support, causal
History and UnionNormal. The class return is result.children, as exposed
by the actual owner-selection branch. This endpoint does not cover an
arbitrary constructor rejection whose class forest differs from that list.

One ActualParentScanNativeStores.selected_scan call returns one numeric
Parent receipt and the seven scanned state laws. Entry Current is derived
by the existing OperandFrame.current theorem from Frame. The private
selected_graph helper inverts THIS numeric.reads through Parent live,
LocalReduction classes and completed ScanClassPass reads.

Retained-to-record completion and full-result uniqueness align COMPLETE
kept records, full checked state and fourth memo with the observed call.
Record paths need not be injective. Trie fields, order, repeated paths and
multiplicity stay exact. Required uniqueness aligns prepared values and
heap. Pass completion/uniqueness aligns result children, full checked
state and Merge memo. The actual constructor suffix remains attached.

The conclusion retains the same numeric receipt, Scan, Retained, actual
Pass and MkEdge. It also retains savedFourth = scanFourth and HEq between
the numeric graph and the assembled live/classes/completed graph. This
documents exact indices and witnesses. It asserts no event uniqueness.
The original memos, Scan memos, prepared memos and final bundle remain in
the same read order. A second Parent receipt is not selected.

The actual Precheck receipt supplies proper paths, coherence, active
classes and full Ready. Its native state is literally unchanged, so
prefix Frame/Fits use the original inventory and profile. ParentReserved
reduces through LocalReserved to ClassesReserved. Its first component
supplies numeric Scan room for the actual initial guard alphabet.
ScanNumeric.complete is used only for its entry-indexed universal ranges.
Its other completion witnesses do not enter the returned read graph.

ScanReadValidity derives Valid for the same scanMemos. RequiredActual
constructs the receipt at the observed Required return. RequiredReadValidity
derives Valid for the same preparedMemos. The same literal RecordScan
retains UnionNormal. The theorem returns all seven scanned native state
laws, the actual stage certificates and prepared memo validity.

No caller Retained, Required receipt, PassReads, reached Ranges or desired
ancestry relation is an input. Initial native Support/History/UnionNormal
remain. Context still contains physical storage, semantic Merge coverage,
fourth-memo correctness and global memo validity. The later owner consumer
also needs initial conditional Merge storage and positive Merge Support.

Root read every original source line and the complete prelaunch delta.
Independent review found a genuine type issue before any proof command:
homogeneous graph equality mentioned independent fourth-memo indices.
The approved correction adds explicit savedFourth = scanFourth and HEq
at the same built witness. The final proof supplies rfl and HEq.rfl after
actual worker alignment. The old frozen plan and original e1ea source
remain unchanged with a separate erratum and corrected public signature.
This correction is not a failed Lean command or execution counterexample.

Selected and root strict logs are empty. Complete FULL has 6419396 bytes,
SHA256 cb0f055547bcb2985461258df2ca265c0fd24aad315b80a611ae54884f95d16c.
It has all eight settings, complete proof/type, identical checked and
printed types, no private public predicate and no omissions. Its actual
axioms are propext, Classical.choice and Quot.sound. The corrected source
passed without any post-launch delta. Two author Lean commands, root
strict and default Audit all pass. No canonical, infrastructure, reviewer
proof or constructed job ran. All retain fresh usage, effective max/high
4 GiB, zero swap and five-minute limits. Audit passes 3594 jobs /74931
dependencies; only the old ClosedCompletion warning remains.

The independent sibling audit identifies existing PUBLIC resource reuse.
EdgeCallNumeric retains exact Post, Frame and branch-specific Fits.
OuterInitialActual handles unrestricted completed node, body, rows,
descendants, children and walk calls under genuine entry Context, Frame,
Fits, finite guard Carrier and computed Schedule Room. This includes Mu;
the finite-ordinary domain is not the only route. Current derives from
Frame. Warm edge ready hits keep the complete caller unchanged.

Those resource APIs do not return new native positive Support or causal
History. A general Parent producer across rejection, unchanged, erasure,
stopped Scan, completed Required/pass and MkEdge remains unproved. Reusing
RequiredPositiveChronology also requires genuine conditional Merge depth
storage, positive Merge Support and normality. These laws do not follow
from physical Context or Frame. A causal interval alone does not supply
positive Support. History retention must use the actual constructor
interval or unchanged Mu records, not growth alone.

Completed node/descendant preservation and a correlated historical writer
ledger remain. A later reader cannot produce old writer-entry resources.
Connecting initial Room/Carrier to the complete outer proof, actual owner
exclusion, renewal, unfolding progress, final retention, outer completion,
convergence and Haskell refinement remain open. All older proofs, logs,
counterexamples and version exceptions stay. Haskell/packages/main remain
unchanged. FINDINGS keeps its external repair index first. Goal active.
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
(ROOT / 'lean/notes-current-actual-parent-selected-certificates.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
