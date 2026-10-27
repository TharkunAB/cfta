from pathlib import Path
import hashlib,json,re,subprocess
root=Path('/home/tritlo/Code/mcfta'); area=Path('/tmp/mcfta-recursive-admission-20261027')
head=(area/'source-head.txt').read_text().strip(); base=(area/'published-base.txt').read_text().strip()
raw=(area/'build-aggregate-final/raw.log').read_text()
jobs=re.search(r'Build completed successfully \((\d+) jobs\)',raw).group(1)
count=re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',raw).group(1)
assert json.loads((area/'public-validation.json').read_text())['status']=='pass'
modules=json.loads((area/'modules.json').read_text()); lines=sum(len((root/'lean/MicroCFTA'/f'{m}.lean').read_bytes().splitlines()) for m in modules)
prefix=f'''
## Actual selected-step meaning and recursive callback admission

Source checkpoint: {head}.
Actual receipts now restore original selected-input satisfaction across
narrowing, ordinary entry, a completed captured head and its false callback.
Canonical, nonterminal, fresh arity and child retention remain explicit gates.
The original finite ordinary producer retains its ENTIRE old result and derives
rich actual invocation receipts and a conditional backward language law.
The callback retains its actual false singleton, returned Packet, full Memos
and concrete restart equation at the same work bound.

A completed captured head now preserves any different isolated pending slot
at its actual completed cache, including IncomingAvoid. Original resources
suffice. No semantic gate or universal Ranges is added to this preservation.
A stronger head producer retains the original callback seed, mass ceiling,
Fits, guard heap, fragment allocation and reservation. An actual false callback
retains that same recursive admission. Earlier sibling/ordinary receipt
families do not yet carry this new admission. Rich whole-history induction
still needs one common bound and admission at every recursive input.

Nine modules, {lines} lines and 16 public theorems pass strict checking.
Audit passes {jobs} jobs and {count} theorem dependency checks.
H6 and both earlier conditional captured renderers retain their signatures.
Whole recursive acceptance, coverage and physical correspondence remain open.
No Haskell source changed. All earlier Haskell repair handoffs stay in FINDINGS.
Details: `lean/notes-current-recursive-admission.md`. The full goal stays ACTIVE.

'''
documents=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/README.md','lean/SYSTEM.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md']; records=[]
for name in documents:
 path=root/name; old=path.read_bytes(); assert old==subprocess.check_output(['git','show',base+':'+name],cwd=root)
 dest=area/'prior-documents'/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(old)
 first,rest=old.split(b'\n',1); data=first+b'\n'+prefix.encode()+rest;path.write_bytes(data)
 records.append(dict(path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),offset=len(first)+1,inserted_bytes=len(prefix.encode())))
note=f'''# Actual selected-step meaning and recursive admission

Source checkpoint: {head}.
Published base: {base}.
Imported main: 82258094c2c32bb93e517427bc649a5c7077adac.
The formalize pull and main fetch succeeded. Main did not change.
The previous goal turn made verified progress and published 9c60c42ee.
Its note is notes-current-recursive-receipts.md. The full goal stays ACTIVE.
Keep the optimized interned core and all older constructor/equality proofs,
repairs, counterexamples, proposals and marked drafts.

## Target and strongest current claims

The target remains whole-system source-connected correctness: exact finite-tree
language preservation, enumeration soundness and coverage under explicit
solver and pruning contracts. This checkpoint does not complete it.

SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains the strongest
global exact finite-tree construction result. Covered closed construction and
a valid original guard-allocation history derive width and fuels for every
finite budget and round count. The actual formal calls complete. Their final
node remains available and accepts exactly the original finite trees in every
ambient environment. The inherited payload is empty. This is no convergence
claim or physical Haskell correctness theorem.

The earlier flat captured renderer still restores original captured-edge and
parent acceptance under its original resource and structural gates. It also
requires original Stratified order, actual completion, Discharged, actual
rendering at that reached heap and checks of every returned residual.
It covers one captured step, not every recursive emitted output.

The strongest new semantic result composes one actual ordinary selected step.
Actual PrefixValid and its literal narrowed run supply the reached cache.
Actual entry, rich completed-head and false callback receipts then restore
satisfaction of the ORIGINAL selected cache at its ORIGINAL native heap.
Selected-edge and parent acceptance, all inherited Holds and fragment fill
remain in the result. Canonical, nonterminal, fresh arity and structural child
retention remain explicit. The theorem consumes those actual local receipts.
It does not derive a rich receipt for every tag of every recursive output path.

## Original ordinary and callback producers

SourcePruningEnumerationOrdinaryInvocationResources calls the old ordinary
producer once. It retains the entire earlier result: actual singleton entry,
RenderStable, unchanged counter/values/indexes, entered Packet, outer and scan
execution, native Post, full Memos, Fits, guard heap, processed/output/stop
certificates and finished OutcomeResources. At one common sufficient work
bound it appends rich receipts for every ACTUAL OrdinaryInvocation.
The actual entry singleton identifies target, handle, bucket, parent and core.
The aggregate Post starts at the original ordinary Caller. Each sibling uses
the same entered captured cache and its actual post-hook native endpoint.
The finite-depth corollary supplies the proven finite_complete contract.

SourcePruningEnumerationOrdinaryInvocationLanguage keeps that entire rich
producer result. No new admission is added. The appended implication proves
backward language soundness for each actual invocation under the current
structural gates. Original Canonical passes through actual entry. Native
Keeps and the same stored handle identify the ORIGINAL ordinary parent.
Fresh arity and retention refer to the original counter; entry preserves it.
The stable bound still precedes extra fuel, invocation and assignment.

SourcePruningEnumerationFiniteCallbackReceiptLanguage retains the entire old
finite callback contract from one producer call. It adds local assignment iff,
conditional Canonical, isolated-slot transport and FalseCallbackReceipt.
The receipt retains the original and returned Packets, full Memos, actual
false recording singleton, RenderStable/Frame, the concrete callback outcome
and the SAME concrete recursive restart outcome at every larger work bound.
The local iff concerns the returned callback core at its unchanged heap.
It does not assert assignment preservation through its later recursive output.
No semantic truth of callback rejection or future recursive success is assumed.

## Selected-prefix and ordinary semantic composition

SourcePruningEnumerationOrdinaryReceiptLanguage proves the backward law from
actual head completion to the original ordinary input. The false-callback
corollary prepends that callback's actual returned core. Actual entry supplies
Canonical and assignment transport. It can update expansion ancestry, so the
proof does not assert a full entry Frame. Aggregate native Post preserves the
same captured cache. The full head receipt supplies its own completed Packet.

SourcePruningEnumerationSelectedReceiptLanguage.narrowed_receipt_sound adds
the actual narrowing prefix. The original Packet and actual restart decision
derive Ready. Actual PrefixValid gives retained-cache safety, pending/cache
validity, counter/order facts and Canonical. The actual entry observer proves
its values unchanged, so the returned stored slot belongs to the original
narrowed input. PrefixMeaning then restores original selected satisfaction.
The original selected variable and actual ordinary returned target remain
explicit. The theorem does not silently identify them. Actual ordinary entry
producer receipts can supply that identity when required.

## Isolation at entry, callback and actual completed capture

SourcePruningEnumerationIsolationReads proves isolation through actual entry
and recordTypes on both sides and either Boolean result. The observers use
actual Success and Total. They do not infer Safe from a generic Frame.
SourcePruningEnumerationOrdinaryIsolationResources preserves the complete old
finite ordinary resource result and appends isolation of its same entered
cache. Its smaller-depth Complete argument is internally discharged.

SourcePruningEnumerationCapturedIsolation proves CompletedHeadReceipt.isolated.
An original IsolatedPending slot with held != uv remains isolated at the
ACTUAL completed captured cache. Original input resources and the receipt's
stable actual diagonal identify one selected-resource completion at a common
larger work fuel. Its Protected and IncomingAvoid facts survive the SAME
actual finalizer, which writes only uv. No universal Ranges, Canonical,
nonterminal, fresh arity, retention or desired after-isolation is an input.

The proof uses SelectedEdge.complete_with_fragments_resources once. The
captured resource interface exports Protected but omits IncomingAvoid for an
arbitrary pending held root. The selected interface retains both facts.
This is an interface distinction, not a missing runtime invariant.
An isolated empty native pending slot contradicts Discharged. Done alone is
not Discharged. Whole-history persistence and exclusion remain open.

## The missing callback admission is now explicit

The earlier CompletedHeadReceipt has the actual completed Packet and its
padded Fits/guard carrier. It omits capturedMass, the retained HeadCacheBounds
mass ceiling and the original callback reservation. Existing sibling/ordinary
rich families discard those fields. They cannot reconstruct smaller-depth
callback admission from their result's Fits alone.

SourcePruningEnumerationCallbackAdmission adds RecursiveCallbackAdmission.
It retains the actual inventory, Caller, full Memos, metadata, cache, fragment
allocation, Fits, guard carrier, original mass ceiling and finite reservation.
head_finite_complete_resources_with_callback_admission retains every old
with_receipt binder, witness and field. It only groups the final universal
receipt field before adding a separate universal callback-admission field.
The original head producer runs once. The actual complete case uses its
own completed Packet, Admitted fragment bound and retained HeadCacheBounds.
head_mass_le bounds the actual mass by massCeil. HeadReserved supplies the original
reservation at afterHead seed inherited. No final-heap reservation is invented.
RecursiveCallbackAdmission.after_false moves the same seed/ceiling/reservation
to the actual updated metadata and framed cache using the callback's exact
returned Packet, Frame.counter and Frame.values.

The new callback admission is NOT yet threaded into the older invocation
families. The stronger head helper retains the original smaller-depth Complete
argument; finite_complete already proves that argument. No stronger recursive
history or future semantic success premise is added.

## Validation and evidence

Nine modules ({lines} lines), 16 public theorems and two structures pass strict
Lean 4.34.1 checking with warnings and every linter enabled. Source checks have
empty logs. Audit passes {jobs} jobs and {count} dependency checks; its own
strict check passes. Lake replays one earlier dependency warning. It is not
suppressed or changed. Public readback checks all 16 new signatures and both
structures. H6 and both earlier captured renderer signatures/axiom blocks are
byte-identical. Only propext, Classical.choice and Quot.sound occur. No sorry,
admit, new axiom, native_decide or heartbeat setting is introduced.
Each heavy job runs serially at 4 GiB, MemoryHigh=MemoryMax, swap disabled.
No Haskell source changed or Haskell test was required for these Lean changes.

Evidence destination: restart-evidence/20261027-recursive-admission.
The checkpoint must preserve every failed strict source/log/report, corrected
variant, exact contracts and grouping differences, actual cap readback,
public declarations, source/cut identities, sealed reviews and old documents.
Publication requires the portable archive verifier and --committed byte check
to pass. The manifest and deterministic gzip restoration hashes cover the
stored payloads. Do not edit any sealed bundle or earlier frozen area.
The early isolation-entry bundle is source-only; root strict-check records
separately verify both exact installed module identities.

Root FINDINGS retains all earlier Haskell fixes and external repair handoffs.
No new Haskell defect or repair is claimed. The prior LPO and extraction
repairs remain integrated. The extraction progress boundary remains explicit;
the board reports its documentation port in upstream PR185. Main is unchanged.
The saved native opaque Mu/Union recipe remains UNEXECUTED. Canonical storage
and these local laws do not recover removed suspended constraints.

## Concrete next proof work

1. Lift the new callback admission through head/sibling/ordinary invocation
   producers. Retain each old full result and the same actual full Memos and
   captured cache. Do not recover a reservation from later Fits.
2. Strengthen Complete to retain its old stable outcome and OutcomeResources
   together with actual resource-decorated histories at ITS OWN common work
   bound. Prove that statement by recursive depth. A separately chosen richer
   bound is not automatically below the old finite-completion bound.
3. Thread the actual false callback admission and stable recording into that
   induction. Parked, stopped and done routes must retain their actual tags.
   Keep outputs emitted before a later stop. Do not add desired satisfaction,
   an after-state invariant or future success to original admission.
4. Derive initial isolation for each actual cleared/truncated slot. Compose
   prefix, entry, capture, callback and recursion isolation along the SAME
   output history, then exclude it from Discharged outputs or recover Holds.
5. Retain checked constructor arity origins and child-retention conditions at
   actual inputs. Storage Canonical alone does not supply them. Compose the
   full backward assignment proof with actual output rendering/residual checks.
6. Close whole recursive acceptance, coverage and the remaining physical
   Haskell correspondence. Keep the full goal ACTIVE until all are proved.

The focused source-grounded closure plan is preserved under
recursive-history-next-proof. Its rejected shortcut is comparison of an old
stable bound with a separately chosen richer bound without evidence.
Push only non-force to the explicitly authorized formalize branch.
'''
name='lean/notes-current-recursive-admission.md';data=note.encode();(root/name).write_bytes(data);documents.append(name);records.append(dict(path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
(area/'document-paths.json').write_text(json.dumps(documents,indent=2)+'\n');(area/'document-validation.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(dict(documents=len(documents),modules=len(modules),lines=lines,jobs=jobs,dependencies=count)))
