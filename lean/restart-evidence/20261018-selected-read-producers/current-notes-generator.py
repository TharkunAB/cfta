import datetime
import json
from pathlib import Path
from zoneinfo import ZoneInfo

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
result = json.loads((HERE / 'checkpoint-validation.json').read_text())
proof = result['proof_commit'][:8]
now = datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
public = result['new_public_pairs']
constructed = result['constructed_pairs']
groups = result['groups']
entries = result['component_entries']
section = f'''## Current target-slot writers and initial native admission

Updated: {now}. Proof checkpoint is `{proof}`.
Starting local checkpoint is `136989d9`. Main source remains `c0cc8a05`.
Read `lean/notes-current-selected-read-producers.md` for exact boundaries.

Actual selected edits now derive target-table histories from their literal
successful equations. An initially absent target slot recovers its earlier
target call, complete captured class and forest, checked and merge states,
and both surrounding target histories. Each class starts fresh local slots.
Native and merge tables can already be warm. Target history alone asserts
no physical reachability, heap growth or semantic target receipt.

Initial exact native key validity, closed resident operands and original
numeric headroom now derive a checked Trace from actual raw Steps. A literal
completed request extracts its own steps. Initial causal native history
then derives the exact returned node cell and earlier full request writer.
No future Trace, WordRanges, InputsThrough or writer law is supplied.
Weak physical cells do not supply the stronger initial key invariant.

Source-built checks cover repeated target paths across actual ordered rows,
a recursive source admission, and a cold distinct-operand recursive request
with actual native node and edge work. Existing numeric semantic target
producers can align their bounded returns with literal completed workers.
Their Frame, Fits, domains, global validity and capacity must still be
derived at the recovered historical writer entry.

Full Audit passes 3230 jobs and 70896 checks. Three production and three
constructed strict logs are empty. All {public} public and {constructed} constructed
full pairs pass in {groups} groups with all eight settings and standard axioms.
Audit peak is 380 MiB under 4 GiB maximum/high and zero swap. Five component
manifests pin {entries} entries. Evidence is in
`lean/restart-evidence/20261018-selected-read-producers/`.

Next compose historical writer entry facts with semantic target receipts.
Carry native admission and global validity through actual earlier class
work. General recursive progress, all-owner separation, fresh-call bounds,
recursive language preservation, used-writer alignment, repeated convergence
and public Haskell correspondence remain open. The strongest complete
ordinary outer domain is unchanged. No Haskell patch is added. Field-pool
repair b9219b9e remains fixed in c0cc8a05. Keep FINDINGS first. The full-library
goal stays active. Publication awaits the existing direct approval.
No push is attempted or retried.

'''
anchor = '## Current selected class dispatch and literal native leaf events\n'
for name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
             'lean/API-COVERAGE.md', 'lean/COVERAGE.md']:
    path = ROOT / name
    text = path.read_text()
    assert section.splitlines()[0] not in text and text.count(anchor) == 1
    path.write_text(text.replace(anchor, section + anchor, 1))
path = ROOT / 'FINDINGS.md'
text = path.read_text()
registry = '## Haskell fix handoff for external work\n\n'
assert text.count(registry) == 1
entry = f'''Current proof update: {now}. Proof checkpoint is `{proof}`.
Actual edits now construct target-table history and recover earlier literal
target writers with their complete captured inputs and states. Initial
closed native admission derives checked traces from raw execution and
numeric headroom. Initial causal native history derives the exact returned
cell and captured request writer. Target history does not transport physical
or semantic entry facts. Weak cells do not supply exact native key validity.
Historical semantic target receipts and general recursive progress remain
open. Full Audit passes 3230 jobs and 70896 checks. No Haskell patch or new
production defect is added. Field-pool repair `b9219b9e` remains fixed in
`c0cc8a05`. Read `lean/notes-current-selected-read-producers.md`.
Keep this registry first. Record each later repair with failure, executable
reproducer, paths, commit, checks and upstream status. Preserve every earlier
repair entry below.

'''
path.write_text(text.replace(registry, registry + entry, 1))
path = ROOT / 'lean/notes-proof-status-20261017.md'
text = path.read_text()
assert 'Checked at proof checkpoint `aed82624`.' in text
text = text.replace('Checked at proof checkpoint `aed82624`.',
                    'Checked at proof checkpoint `' + proof + '`.', 1)
text = text.replace('[the current checkpoint](notes-current-selected-edit-events.md).',
                    '[the earlier checkpoint](notes-current-selected-edit-events.md).', 1)
anchor = '## Strongest current claim in plain technical English\n'
paragraph = '''Actual selected edits now recover the literal earlier target writers of
warm class slots. Their target-table histories fix the class, captured
forest, target path and complete worker states. They assert no physical
or semantic transport to those historical entries. Initial exact native
key validity, closed resident operands and numeric headroom now produce
checked traces from raw execution. An initial causal native history then
produces the exact returned node cell and earlier complete request writer.
Historical semantic target receipts and the stronger initial key invariant
still need transport through the full class schedule. General recursive
completion and the complete ordinary outer domain are unchanged. Read
[the current checkpoint](notes-current-selected-read-producers.md).

'''
assert text.count(anchor) == 1
path.write_text(text.replace(anchor, paragraph + anchor, 1))
note = f'''# Target-slot writers and initial native admission

Updated {now}. Proof checkpoint: `{proof}`.
Starting local checkpoint: `136989d9`. Main source: `c0cc8a05`.
This is verified progress. The full-library goal remains active.

## Strongest complete statement

For a validated finite explicit graph, including cycles, the checked model
lists exactly the distinct accepted finite terms at each node-count size.
Its counts are correct. Rank and unrank follow the specified order and are
inverses at valid indexes. Correct finite yes/no guard replies and the stated
ordering laws give these successful results. Finite unknown replies can
instead return an error. Supported closed resident Original operands have
exact recursive native intersection semantics. Initial resources construct
those executions. A complete finite ordinary constrained outer pass preserves
the full guarded language. That outer domain excludes Mu, references and
explicit unions in every descendant.

These are separate implementation-model results. Complete public contracts
and concrete Haskell correspondence remain the target. A support predicate
must describe initial inputs and resource limits. It must not assume success.
Read `notes-proof-status-20261017.md` for the target and remaining work.

## Actual target-slot writers

ActualTargetSlotHistory.History fixes the class, original forest and bounds.
It records actual completed target calls at missing slots. Other steps
retain the complete target function. History.keeps proves that a present
value cannot be overwritten. History.writer recovers an exact earlier
target call, its full checked and merge return, the absence before its
store, and both surrounding histories. It needs initial absence and the
actual present slot. No semantic target law is supplied.

Actual successful force, leaf, child scans, row scans, edits, edit lists
and class calls produce this history. Recursive Head and reconstruction
retain the same slots. A class starts fresh local slots over its literal
checked state and merge memo. Those underlying tables can already be warm.
The repeated-row fixture derives its prefix history from the actual first
row. A later row forces the same path [0,0]. It recovers the earlier target
writer and verifies an all-zero force hit at that same full state.

History.retained asserts only target-function equality. Its checked and
merge fields can change. The recovered prefix and suffix are target-table
histories, not complete control reachability traces. They do not themselves
transport Good, Grows, Frame, Fits, or semantic admission to the writer.
SlotReceipt requires additional semantic TargetReads and a full historical
TargetComplete.Receipt with heap and merge transport into the reader.

## Native checks from initial admission

NativeKeyAdmission.node_prefix takes initial PhysicalCompletion.Good,
semantic heap readiness, closed available operands and original numeric
headroom. Closed coherent availability derives Original source syntax.
Arbitrary nested Mu is permitted. No Cap or BinderFree condition is added.
Existing prefix admission produces a checked Trace from actual raw Steps.
The width producer then supplies final Good, fields, stored mass and
counter bounds. node_done extracts its own raw Steps from execute.done.
No future checked trace, word range or Inputs plan is an input.

Write N for the original node counter and bits for the untagged key width.
The explicit resource bounds are N < 2^bits, edge counter <= 2^(bits+2),
and domain counter + 2^(N+N*N) < 2^(bits+1). These conservative initial
bounds are formal support conditions. They do not prove host word capacity
for every public Haskell input or prove that supplied native fuel completes.

Strong PhysicalCompletion.Good retains exact native memo keys and key safety.
Weak NativeOperationHeap.Good retains physical cells with key predicate True.
Initial empty tables and actual key-safe publication can derive the stronger
invariant. Current identity bounds alone cannot repair arbitrary warm tables.
The new producer does not infer strong validity from the weak invariant.

## Actual native request writers

NativeAdmissionWriter.node_written uses the same initial admission and a
NativeEdgeWriterGrowth.History at entry. It derives the actual checked trace
from literal completion, then supplies it to the existing writer producer.
Both closed operand proofs exclude the unresolved direct branch. The output
has final native history, strong Good, heap growth, the exact returned node
cell and NativeWriterReadyRetention.Written for its complete original query.
No future cell or writer law is supplied. Initial native history is separate
from target-table history. No result-language theorem is added here.

One source-built admission fixture contains recursive Mu but uses the root
self branch. A separate source-built writer fixture uses distinct closed
recursive operands. Its actual cold request returns a nonempty result and
performs native node and edge work. Initial strong Good, causal history and
headroom are derived from that source. The fixture consumes node_written
and retains its exact full-request returned cell and earlier writer.

## Next semantic composition

TargetNumeric.complete and ClassPassNumeric.fold already construct bounded
semantic reads and full receipts from initial Frame, Fits, selected domains,
stored and covered merge entries, globals and Room. Their result uniqueness
laws align constructed returns with literal successful workers. Do not
reprove these cold semantic algorithms or assume their future receipts.

Derive those entry facts at the actual recovered historical target writer.
Carry exact native-key validity, causal native history and semantic globals
through earlier class work. Then construct the historical SlotReceipt and
compose actual shared leaf reads with native writer lineage. General
recursive progress, all-owner separation, fresh-call bounds, recursive
language preservation, used-writer alignment, repeated convergence,
concrete adapters and public Haskell correspondence remain open.
The complete ordinary outer domain is unchanged. Theorem counts do not
give a completion percentage or time estimate.

## Verification and preservation

Full Audit passes 3230 jobs and 70896 dependency checks. Only the unchanged
ClosedCompletion unused-variable warning remains. Three production and
three constructed strict logs have exactly zero bytes. All {public} public
and {constructed} constructed pairs have complete signatures, proofs and axiom
reports in {groups} groups. All eight required options are enabled. Only
standard axioms occur. Effective maximum/high memory limits are 4 GiB.
Swap maximum is zero. The Audit peak is 380 MiB. Five component manifests
pin {entries} entries. All numbered drafts and raw output remain present.
Evidence is in `restart-evidence/20261018-selected-read-producers/`.

All 26596 starting files remain present. All 3226 older non-Audit Lean sources,
242 Haskell files and 206 active-package files retain their bytes. Two stashes
and three other worktrees retain their metadata. Audit only adds three imports.
The preservation report checks 138 frozen manifests and 987 module entries.
Root FINDINGS retains every earlier repair entry. No Haskell patch or new
production defect is added. Field-pool repair b9219b9e remains fixed in main
c0cc8a05. Publication awaits the existing direct approval. No push is attempted.
'''
(ROOT / 'lean/notes-current-selected-read-producers.md').write_text(note)
print(json.dumps({'proof_commit': proof, 'updated_at': now, 'authority_documents': 8}))
