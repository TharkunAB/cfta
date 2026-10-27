from pathlib import Path
import hashlib,json,re,subprocess
r=Path('/home/tritlo/Code/mcfta');a=Path('/tmp/mcfta-recursive-marker-attachment-20261027')
head=(a/'source-head.txt').read_text().strip();base=(a/'published-base.txt').read_text().strip()
assert json.loads((a/'public-validation.json').read_text())['status']=='pass'
raw=(a/'build-aggregate-final/raw.log').read_text()
jobs=re.search(r'Build completed successfully \((\d+) jobs\)',raw).group(1)
count=re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',raw).group(1)
ms=json.loads((a/'modules.json').read_text());lines=sum(len((r/'lean/MicroCFTA'/f'{m}.lean').read_bytes().splitlines()) for m in ms)
assert len(ms)==11 and lines==1210
prefix=f'''
## Actual parked boundaries and canonical output caches

Source checkpoint: {head}.
An actual parked clear now retains its original stored handle and bucket
through its actual remaining ResourceHistory. The boundary stays isolated at
that output's OWN cache and native heap. The output cannot be fully Discharged.
Initial Canonical now reaches every actual finite output's own cache.
The finite producer keeps its ENTIRE old admission and result, adds an initial
Canonical premise and returns Canonical for all actual outputs.
Canonical describes storage. It does not establish assignment satisfaction.

Actual invocation receipts supply nonterminal gates. The actual narrowed
right step retains the original metadata. Opaque child events now retain their
actual consumed prefix, allocation, suffix and successful captured finalizer.
An adequate common work bound supplies the event's full Memos, Packet, Fits,
guard heap and remaining reservation. Actual own-allocation receipts supply
the local Packet link. Persistence of a NEW opaque marker through that SAME
suffix, finalizer, callback and remaining output history is still open.

Eleven modules, {lines} lines and 18 public theorems pass strict checking.
Audit passes {jobs} jobs and {count} theorem dependency checks. H6 and both
previous conditional captured renderers retain exact signatures and axioms.
H6 remains the strongest global exact finite-tree construction theorem.
Whole recursive acceptance, coverage and physical Haskell correspondence
remain open. No Haskell source changed in this checkpoint. FINDINGS retains
all earlier Haskell fixes and external repair handoffs, including KBO overflow.
Details: `lean/notes-current-recursive-marker-attachment.md`.
The whole-system goal stays ACTIVE.

'''
paths=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/README.md','lean/SYSTEM.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md']
records=[]
for name in paths:
 p=r/name;old=p.read_bytes();assert old==subprocess.check_output(['git','show',base+':'+name],cwd=r)
 dest=a/'prior-documents'/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(old)
 first,rest=old.split(b'\n',1);insertion=prefix
 if name=='FINDINGS.md':
  insertion+='''
### Haskell repair status for this checkpoint

No Haskell code or Cabal file changed. No new runtime repair is claimed.
The LPO fix and the extraction documentation repair remain integrated.
The earlier positive-Int KBO context-reversal counterexample and its external
repair instructions remain below without change. Exact nonnegative weights,
or a validated bound that excludes overflow for each accepted term, remain
required for unrestricted context closure. Generated-weight overflow was not
executed. The public-map context reversal was executed. Neither observation
establishes a false emitted equation or a concrete rewrite cycle.
The new Lean lemmas do not change that runtime finding or verify the new
Specftacular order/pre-search path. See the preceding checkpoint's evidence.

'''
 data=first+b'\n'+insertion.encode()+rest;p.write_bytes(data)
 records.append(dict(path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),offset=len(first)+1,inserted_bytes=len(insertion.encode())))
note=f'''# Actual marker attachment and canonical finite outputs

Source checkpoint: {head}.
Published base: {base}.
Imported main: 8766699b594eaad80381af2eee034c378ccf3192.
The whole-system goal stays ACTIVE. Preserve the optimized interned core,
all older constructor and equality work, drafts, counterexamples and repairs.
Previous checkpoint: `notes-current-recursive-history-resources.md`.

## Target and strongest statements

The target remains source-connected correctness for the whole CFTA system:
exact finite-tree language preservation, enumeration soundness and coverage,
under explicit solver, selection and pruning contracts. It is not complete.

SourceCurrentColdFiniteWarmCalls.constructed_node_calls (H6) remains the
strongest global exact finite-tree construction theorem. Covered closed
construction, a valid original guard-allocation history and empty inherited
payload derive width and work fuels for every finite budget and round count.
Actual modeled node calls complete. The final node remains available and
accepts exactly the original finite trees in every ambient environment.
This does not prove convergence or physical Haskell execution correctness.

The operational finite-depth producer already derives a sufficient work bound
and actual stable outcome from original resources. Every actual output,
including outputs before a later stop, retains its admitted ResourceHistory.
No unproved recursive completion premise remains in that producer.

The new run_finite_complete_resources_canonical retains the entire prior
producer admission and result. It adds initial Canonical and derives Canonical
for every actual output's OWN cache. ResourceHistory.canonical_output proves
the full induction without an extra actual-next premise. Ordinary receipts
retain Canonical through actual entry, completed head and either Boolean
callback. Initial Canonical is explicit. An arbitrary Packet alone does not
imply it. EnumerationValidity.initial_canonical supplies the concrete
initialized root case. Canonical is a storage property, not Satisfies.

The new parked_tail_created_isolated starts with the actual original Packet,
selected prefix, parked step and actual tail ResourceHistory. It retains the
original stored handle and bucket. The newly created recursive boundary stays
isolated at the SAME output's OWN cache and native heap. That output cannot be
fully Discharged. No after-isolation or desired output premise is assumed.
The result concerns the original parked root. It does not create a fresh root.
It does not filter the runtime result or prove that every rendering fails.

## Actual semantic gates and opaque event resources

OrdinaryInvocation.entry_nonterminal derives the nonterminal gate from actual
entry and retained-success receipts for the SAME bucket. The new ordinary
semantic consumer keeps the entire old conclusion. It derives that one gate.
SelectedStep.narrowed_right_identity proves that the literal right callback
keeps the ORIGINAL metadata and narrowed core. narrowed_receipt_sound_of_invocation
aligns the same updated metadata, entered Packet, completed head and callback.
It then applies the old semantic theorem once. Canonical, fresh child arity and
child retention remain explicit at these local semantic uses.

OpaqueEventTrace splits the ACTUAL completed captured traversal at a static
child occurrence. The event retains its actual consumed prefix, opaque cached
allocation, fresh hole, caller, queries, outer context, waiting index, residual,
exact remaining Trace and the SAME successful Finalize.run endpoint.
The result covers actual completed traversals. It does not assert that a
future finalizer succeeds or that a new marker survives the suffix.

OpaquePrefixResources retains the ENTIRE old traversal producer contract.
It invokes that old whole producer once and the old consumed-prefix producer
once. It derives one adequate diagonal work bound. ChildTraversal.trace_complete aligns the
actual consumed endpoint at that bound. The appended PrefixAdmission observer
supplies the actual event's aggregate native Post, FULL Memos, exact queries,
Packet, counter growth, remaining genuine children, Fits, guard heap and the
remaining reservation. Initial Packet is an antecedent of this appended
observer, not a new old-producer admission. No arbitrary low-fuel trace
uniqueness or assumed endpoint equality is used. The old contract has an exact
4,287-byte recovery check.

OwnPrefixPacket derives all six Packet fields at the SAME caller, FULL Memos
and metadata from original Packet and ACTUAL suspendedState-core/CacheValid
own-allocation receipts. Safe follows from the original Packet and actual
origin/protected/allocation facts. It is not inferred from Frame alone.
This closes the local own-allocation Packet link when those receipts are
available. These local connections are not yet one end-to-end head theorem.

## Missing work, in order

1. Combine the new own-prefix Packet and event-prefix resource receipts with
   the actual head receipt at ONE adequate work bound. If B is the sum of
   the returned resource bounds and H is the head bound, use W=B+H+extra.
   Supply H+extra to the prefix observer and B+extra to head.running.
   Align the same actual opaque event. Do not infer internal state equality
   only from equality of final captured results.
2. Apply the existing opaque suffix-isolation producer to that event's
   actual Packet, full Memos, Fits, guard heap and remaining reservation.
   Align its sufficient bound with the actual suffix at the same work fuel.
   Preserve the fresh marker through the SAME residual and actual successful
   finalizer. Then preserve it through the actual callback and its own
   remaining ResourceHistory. Derive non-Discharged at that actual output.
   A marker from sibling A does not enter sibling B's restored captured cache.
   Quantify the descendants of the marker's own hook, not all later siblings.
3. Derive fresh child arity from ACTUAL checked edge-construction receipts
   through native heap Posts. Context.annotation_heap proves normalized guard
   tries, not child arity. Existing checked-build/worker arity lemmas require
   actual constructor or intersection provenance. Do not add a universal Ranges
   premise. Retention does not follow from Canonical or completion alone.
   Preserve the checked Mu/Union nonterminal retention obstructions.
4. Compose backward assignment meaning through whole admitted histories.
   Recover cleared constraints where possible. Exclude relevant outputs when
   a retained isolated boundary prevents full discharge. The canonical and
   operational results do not imply this semantic composition.
5. Derive original acceptance from actual rendering and residual checks for
   every eligible recursive output. Prove coverage separately under the exact
   pruning and solver contracts. Close remaining public API and physical
   Haskell correspondence boundaries. Keep constructor and equality targets.

## Verification and handoff

Eleven modules contain {lines} lines and 18 public theorems. Every new module
passes warningAsError and linter.all with empty output. Strict Audit passes.
The aggregate build passes {jobs} jobs and {count} theorem dependency checks.
The new signatures and unchanged H6 plus both previous captured-renderer
signatures are read in full: 21 theorem signatures and one data definition.
The old three public blocks are byte-identical. Their only used axioms remain
propext, Classical.choice and Quot.sound. No proof holes, custom axioms,
heartbeat changes or linter suppression are added.

No Haskell source or Cabal file changed. The earlier main/LPO integration,
KBO runtime preferences and extraction documentation repair remain intact.
FINDINGS preserves every earlier repair handoff. The positive-Int public-map
KBO context reversal remains a runtime limitation. Its generated-weight
extension is algebraic and unexecuted. No new runtime fix or stronger runtime
correctness claim is made. Native checks were not repeated for Lean-only edits.

The new restart evidence archive is
`restart-evidence/20261027-recursive-marker-attachment`. It retains all strict
attempts, raw logs, installed source snapshots, literal inspected source cuts,
source identities, old contract recoveries and review seals. Failed drafts
remain evidence. Older documents remain byte-identical after removal of their
new prefix. The portable verifier checks manifests, compressed payloads,
literal source cuts, review seals, source snapshots and document preservation.
Use --committed after the evidence commit to verify tracked bytes.
Do not edit a sealed review bundle or an archived TEMP area. Write later work
in a new area. Publication receipts are stored outside this frozen area.
'''
name='lean/notes-current-recursive-marker-attachment.md';data=note.encode();(r/name).write_bytes(data);paths.append(name)
records.append(dict(path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
(a/'document-paths.json').write_text(json.dumps(paths,indent=2)+'\n')
(a/'document-validation.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(dict(status='pass',documents=len(paths),source_head=head,modules=len(ms),lines=lines,jobs=jobs,theorem_checks=count)))
