from pathlib import Path
import hashlib,json,re,subprocess
r=Path('/home/tritlo/Code/mcfta');a=Path('/tmp/mcfta-recursive-history-resources-20261027')
head=(a/'source-head.txt').read_text().strip();base=(a/'published-base.txt').read_text().strip()
assert json.loads((a/'public-validation.json').read_text())['status']=='pass'
raw=(a/'build-aggregate-final/raw.log').read_text(); jobs=re.search(r'Build completed successfully \((\d+) jobs\)',raw).group(1); count=re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',raw).group(1)
ms=json.loads((a/'modules.json').read_text());lines=sum(len((r/'lean/MicroCFTA'/f'{m}.lean').read_bytes().splitlines()) for m in ms)
native=json.loads((a/'native-summary.json').read_text())
prefix=f'''
## Original resources now derive full finite recursive histories

Source checkpoint: {head}.
Original Packet, full Memos, Fits, guard heap, input mass and finite reservation
now derive one sufficient work bound and the actual stable recursive result.
Every emitted output retains an admitted ResourceHistory at its actual work
bound. This includes outputs before a later stop. Depth induction supplies
all smaller recursive drivers. No recursive completion premise remains.
Each history retains actual prefixes, entry, completed heads, callbacks,
original callback seeds, mass ceilings and reservations. Siblings use their
actual post-hook endpoints and the SAME captured enumeration cache.

An isolated recursive boundary in the ORIGINAL input persists at each output's
own cache and heap. That output cannot be fully Discharged. Local creation
and opaque-suffix isolation are proved. Their attachment to every remaining
history is still open. Whole recursive assignment soundness, rendering
acceptance, enumeration coverage and physical correspondence remain open.
H6 remains the strongest global exact finite-tree construction theorem.

Eighteen modules, {lines} lines and 31 public theorems pass strict checking.
Audit passes {jobs} jobs and {count} theorem dependency checks. H6 and both
previous conditional captured renderers retain exact signatures and axioms.
Main extraction documentation and KBO definition preferences are integrated.
The CFTA runtime is unchanged. Imported Specftacular runtime is tested
separately; its integer-weight limitation is recorded below and in the note.
All earlier Haskell fixes and repair handoffs remain in FINDINGS.
Details: `lean/notes-current-recursive-history-resources.md`.
The whole-system goal stays ACTIVE.

'''
paths=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/README.md','lean/SYSTEM.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md'];records=[]
for name in paths:
 p=r/name;old=p.read_bytes();assert old==subprocess.check_output(['git','show',base+':'+name],cwd=r)
 dest=a/'prior-documents'/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(old)
 first,rest=old.split(b'\n',1); insertion=prefix
 if name=='FINDINGS.md':insertion+='''
### Haskell import and external repair handoff: KBO definition weights

Main c04686f7 integrates the extraction-progress documentation repair.
Main 8766699b integrates definition-weight KBO preferences and definition
pre-search in Specftacular. These runtime changes are imported without local
modification. They are outside the current recursive CFTA Lean theorem.
The LPO fix already in the branch remains preserved.

The new public KnuthBendix map uses Int weights without range validation.
A focused executable counterexample uses only nonnegative map entries:
a=maxBound, b=0, c=1. The leaf a is greater than b, but the equal-size
context app c [-] reverses their order after Int overflow. The recursive
computed definitionWeights recurrence can exceed Int mathematically. Its
large overflow case was not executed because evaluation repeats dependencies
exponentially. The executed public-map witness invalidates unrestricted
context closure. The result does not establish a false
emitted equation. Instantiated local rewrites still check their order.
The KBO function-position code relies on context closure. The actual public
reducible call accepts the local rewrite while the whole contextual term
increases. No rewrite cycle is claimed.

External repair: use exact nonnegative arithmetic for definition weights,
or validate a bound that excludes overflow for each accepted term. Reject
negative user weights if the substitution argument requires nonnegativity.
Keep a regression for context closure and for generated-weight overflow.
No local runtime repair is included in this checkpoint. Exact source pins,
executed witness and logs are in the new evidence archive. See the note for
validation status and scope. All older findings below remain unchanged.

'''
 data=first+b'\n'+insertion.encode()+rest;p.write_bytes(data)
 records.append(dict(path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),offset=len(first)+1,inserted_bytes=len(insertion.encode())))
note=f'''# Original resources and full finite recursive histories

Source checkpoint: {head}.
Published base: {base}.
Imported main: 8766699b594eaad80381af2eee034c378ccf3192.
The whole-system goal stays ACTIVE. Preserve the optimized interned core and
all older construction, equality, counterexample, repair and draft work.
The previous checkpoint is notes-current-recursive-admission.md.

## Target and strongest statements

The target remains source-connected correctness for the whole CFTA system:
exact finite-tree language preservation, enumeration soundness and coverage,
under explicit solver, selection and pruning contracts. It is not complete.

SourceCurrentColdFiniteWarmCalls.constructed_node_calls (H6) remains the
strongest global exact finite-tree construction theorem. Covered closed
construction, a valid original guard-allocation history and empty inherited
payload derive width and work fuels for every finite budget and round count.
Actual modeled node calls complete. Their final node remains available and
accepts exactly the original finite trees in every ambient environment.
This does not prove convergence or physical Haskell execution correctness.

The new strongest operational theorem is
SourcePruningEnumerationRecursive.run_finite_complete_resources_with_history.
For every finite recursive depth, original input resources derive a sufficient
work bound and one actual stable outcome. At every larger work bound, each
emitted output has its own complete admitted ResourceHistory. The result
retains the ENTIRE prior stable result and OutcomeResources. It covers outputs
before a later stop and actual stopped, done and stuck branches. The bound
precedes extra fuel and the choice of output. History witnesses may depend on
extra fuel. No single fixed trace for all work fuels is claimed.

Original Packet, full Memos, Fits, guard carrier, suspended input mass and
finite reservation remain the admission. Actual selector membership and
length contracts remain explicit. CompleteWithHistory is discharged by
finite depth induction. No desired output satisfaction, future success or
unproved recursive completion premise enters the public result.

SourcePruningEnumerationRecursive.run_finite_complete_resources_isolated
retains that full producer result. An ORIGINAL IsolatedPending boundary,
its actual decoded handle and recursiveBoundary fact persist at every emitted
output's OWN cache and native heap. That output cannot be fully Discharged.
This is exclusion of an original unresolved boundary. It does not attach an
arbitrary marker created later inside an operation to the remaining history.

The earlier captured renderer still proves original captured-edge and parent
acceptance under original resources, structural gates, Stratified order,
actual completion, Discharged, actual rendering and every returned residual
check. Those local semantic gates are not discharged by the new histories.

## Proof construction and exact endpoints

InvocationAdmission, SiblingInvocationAdmission and OrdinaryInvocationAdmission
retain the complete old finite scan and ordinary packets. They add the SAME
actual callback admission: original seed, inherited allocation, mass ceiling,
Fits, guard heap and reservation. Each head helper is used on its actual input.
The actual entry singleton identifies the same entered captured cache.
A sibling uses the previous hook's actual Caller and FULL Memos. Every sibling
restores the same captured enumeration cache.

FiniteHistoryContract defines HistoryAdmission, OrdinaryHistoryReceipt,
ResourceHistory and CompleteWithHistory. Histories retain original input
resources and full returned Memos at each tag. An ordinary tag retains its
actual selected prefix, entry, aggregate native Post, actual head invocation,
actual head run and complete CompletedHeadReceipt. The false callback retains
its exact singleton and its returned recursive admission. Callback and parked
producers use the stronger smaller-depth driver once on their actual inputs.

FiniteHeadHistory retains the whole prior head packet, completed receipt and
callback admission. It aligns actual old and new callback outcomes at a
common bound. FiniteSiblingHistory adds InvocationHistoryAt for each actual
emitted output, with its exact local head bound and callback-tail history.
FiniteOrdinaryHistory and its forecast retain their ENTIRE earlier packets.
The ordinary entry uses the same entered cache and native endpoint throughout.
FiniteExpansionHistory constructs the selected history at the actual prefix,
scan and callback work fuel. FiniteRunHistoryStep covers each actual decision.
FiniteHistoryResources closes the stronger depth induction from zero upward.

CreatedIsolation proves isolation of actual parked clears and actual shallow
opaque Mu/Union preparation under their original packet and read/check facts.
A retained external reference gives a concrete obstruction to clearing an
arbitrary bucket. That obstruction is not a newly claimed Haskell bug.
OpaqueSuffixIsolation retains the complete old suffix resource result. A
fresh opaque marker stays isolated in the SAME actual suffix result. Its
actual residual and finalizer preserve that marker when they write another
target. Finalizer preservation is an output conditional on its actual success.

HistoryReceiptIsolation transports an already isolated marker through the
same actual entry, head and callback. HistoryBoundaryIsolation uses the actual
Restart.decision, not just a constructor tag. The original boundary cannot
be the selected target. Actual prefixes and native Posts retain isolation
and the same decoded handle. The finite producer supplies histories once and
applies the consumer at each output. Done alone does not mean Discharged.

## Missing work, in order

1. Attach each marker created by an actual clear or opaque preparation to
   the remaining actual ResourceHistory. Preserve its exact creation endpoint.
   Use the local creation and opaque-suffix results. Do not assume that an
   original-marker theorem already covers an inside-head creation.
2. Derive the remaining fresh arity, child retention and Canonical conditions
   at each relevant semantic use. Relate them to original admission and actual
   receipts. Do not replace them with desired future satisfaction.
3. Compose backward assignment meaning across each whole admitted history.
   Recover parked constraints where possible and exclude structurally
   discharged outputs where a retained isolated boundary prevents recovery.
4. Apply actual rendering and residual checks to derive original acceptance
   for every eligible recursive output. Prove coverage separately under the
   exact pruning and solver contracts. Operational stability is not coverage.
5. Close remaining public API and physical Haskell correspondence boundaries.
   Audit the new Specftacular KBO/pre-search path separately. Retain all older
   constructor and equality targets and external Haskell repair handoffs.

## Upstream integration and Haskell findings

Main c04686f7a8fa163b98bcfb40b3cb5c5cab3fb157 incorporates the extraction
progress documentation repair. Four documentation conflicts were resolved to
main's final wording. All CFTA Haskell bytes outside block comments remain
identical to the published base. The LPO fix already present stays preserved.
Main 8766699b594eaad80381af2eee034c378ccf3192 merges cleanly. It changes
Specftacular's default order to KnuthBendix Map.empty, adds definition-weight
preferences, definition pre-search and quiet phase settings. The three imported
runtime/test files are byte-identical to main. No local runtime fix is added.
These files do not change the checked recursive CFTA Lean definitions.

The public KnuthBendix map accepts Int weights. Executed nonnegative-map
context reversal and the unexecuted generated-weight risk are in FINDINGS.
They limit the claimed order laws. Exact arithmetic or a proved accepted bound
is required for an unrestricted context-closure theorem. Negative maps also
require attention to substitution stability. Local instantiated order rechecks
remain in rewriteStep; no false equation or concrete rewrite cycle is claimed.
The KBO function-position branch relies on context closure. The computed
weights and pre-search are not formally verified by this checkpoint.

Native validation summary:
{json.dumps(native,indent=2)}

## Validation and preservation

All {len(ms)} modules ({lines} lines), 31 new public theorems and five data
declarations pass strict Lean 4.34.1 checks. Warnings and every linter are
errors. Source logs are empty. Audit passes {jobs} jobs and checks {count}
theorem dependencies. The strict Audit check passes. Lake replays one existing
warning in InternedFreshOrdinaryClosedCompletion; it is not suppressed.
Public readback prints all 31 new theorem signatures and their axiom sets,
plus the five definitions. H6 and both earlier captured-renderer signatures
and axiom blocks are byte-identical. Only propext, Classical.choice and
Quot.sound occur. No sorry, admit, new axiom, native_decide, linter suppression
or heartbeat change is introduced. Every heavy job is serial, capped at 4 GiB,
with MemoryHigh=MemoryMax and swap disabled. All failed checks and sources
remain in evidence. Passing native tests does not prove source correspondence.

Evidence: restart-evidence/20261027-recursive-history-resources.
The archive retains actual source identities, literal review cuts, every draft
revision, failed and final strict inputs and logs, original-contract comparisons,
full public readback, capped runtime checks, upstream before/after sources,
conflict resolution, KBO witness, native validation and independent review seals.
The portable verifier checks source identity, cut fidelity, seals, document
preservation and committed archive bytes. It does not reconstruct a Haskell
correctness proof. Do not edit earlier frozen evidence or marked drafts.
'''
name='lean/notes-current-recursive-history-resources.md';p=r/name;assert not p.exists();p.write_text(note)
records.append(dict(path=name,bytes=len(p.read_bytes()),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
paths.append(name);(a/'document-paths.json').write_text(json.dumps(paths,indent=2)+'\n');(a/'document-validation.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({'documents':len(paths),'new_module_lines':lines,'source_head':head}))
