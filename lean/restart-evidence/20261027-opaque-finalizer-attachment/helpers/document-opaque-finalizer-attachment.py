from pathlib import Path
import hashlib,json,re,subprocess
r=Path('/home/tritlo/Code/mcfta');a=Path('/tmp/mcfta-opaque-finalizer-attachment-20261027')
head=(a/'source-head.txt').read_text().strip();base=(a/'published-base.txt').read_text().strip()
assert json.loads((a/'public-validation.json').read_text())['status']=='pass'
raw=(a/'build-aggregate-final/raw.log').read_text();jobs=re.search(r'Build completed successfully \((\d+) jobs\)',raw).group(1);count=re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',raw).group(1)
ms=json.loads((a/'modules.json').read_text());lines=sum(len((r/'lean/MicroCFTA'/f'{m}.lean').read_bytes().splitlines()) for m in ms);assert len(ms)==3 and lines==484
prefix=f'''
## Actual opaque boundaries now reach their own recursive outputs

Source checkpoint: {head}.
A stable completed head receipt and an actual nonterminal opaque child event
now derive a fresh isolated boundary at the SAME completed head cache.
The proof aligns the own allocation, actual consumed prefix, opaque allocation,
remaining suffix, residual and successful finalizer at one sufficient bound.
No final isolation, endpoint equality or future success is assumed.
The actual false callback and its admitted remaining ResourceHistory preserve
that boundary at the SAME output's OWN cache and native heap. The output
cannot be fully Discharged. This is a consumer of actual head and tail receipts.
It does not claim that every output contains an opaque event. Siblings restore
their captured cache. A marker does not transfer to another sibling.

The stable-prefix producer retains the ENTIRE previous resource contract.
It adds a fixed actual prefix result, which may be stopped. The original two
producer calls are retained. Initial Canonical and parked-marker preservation
from the previous checkpoint remain unchanged. Storage is not Satisfies.
H6 remains the strongest global exact finite-tree construction theorem.
Whole backward assignment meaning, remaining checked-arity and retention
obligations, recursive rendering acceptance, coverage and physical Haskell
correspondence remain open. The whole-system goal stays ACTIVE.

Three modules, {lines} lines and four public theorems pass strict checks.
Audit passes {jobs} jobs and {count} theorem dependency checks. H6 and both
previous conditional captured renderers retain exact signatures and axioms.
No Haskell source changed. FINDINGS preserves earlier fixes and records a
separate upstream KBO repair candidate. It is not integrated or executed here.
Details: `lean/notes-current-opaque-finalizer-attachment.md`.

'''
paths=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/README.md','lean/SYSTEM.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md'];records=[]
for name in paths:
 p=r/name;old=p.read_bytes();assert old==subprocess.check_output(['git','show',base+':'+name],cwd=r)
 dst=a/'prior-documents'/name;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(old)
 first,rest=old.split(b'\n',1);insertion=prefix
 if name=='FINDINGS.md':
  insertion+='''
### Haskell repair candidate found during upstream refresh

No Haskell source or Cabal file changed in this checkpoint. All earlier repair
records remain below without change. Main remains 8766699b594eaad80381af2eee034c378ccf3192.
The fetched branch origin/fix/kbo-definition-weights has candidate commit
 d7b6a9dfff464eb32c17c314d4825d5b027f1b2d.
It changes definition weights from Int to Natural. It computes the acyclic
weight map with Data.Map.Lazy. It adds the earlier public-map context-closure
witness to the golden suite. The source changes address the reported weight
representation and repeated evaluation. This is a source assessment only.
The candidate is not on main and is not integrated, built or executed here.
Do not mark the runtime finding fixed in the current branch on this evidence.
Re-evaluate and run the targeted regression when the repair lands on main.
The earlier LPO fix and extraction documentation repair remain integrated.
All earlier Haskell findings and external repair instructions remain preserved.

'''
 data=first+b'\n'+insertion.encode()+rest;p.write_bytes(data)
 records.append(dict(path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),offset=len(first)+1,inserted_bytes=len(insertion.encode())))
note=f'''# Actual opaque boundaries through finalizers and recursive outputs

Source checkpoint: {head}.
Published base: {base}.
Imported main: 8766699b594eaad80381af2eee034c378ccf3192.
The whole-system goal stays ACTIVE. Preserve the optimized interned core,
all older constructor and equality proofs, drafts, counterexamples and repairs.
Previous checkpoint: `notes-current-recursive-marker-attachment.md`.

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

The earlier finite-depth producer still derives sufficient work fuel and an
actual stable outcome from original resources. It retains each actual output's
admitted ResourceHistory, including outputs before a later stop. The earlier
Canonical theorem requires initial Canonical and retains it at each output's
own cache. Actual parked clears already retain their created boundary through
the same remaining history and exclude full discharge at that output.
These earlier results and their complete contracts remain unchanged.

The new completed_head_opaque_isolated takes an ACTUAL CompletedHeadReceipt,
actual constraint projection, a static child occurrence, a recursiveBoundary
fact and its nonterminal bucket. It derives a fresh IsolatedPending marker at
the literal completed headCache and a lookup of the SAME opaque value in the
literal reached caller's heap. Its input is the original completed head
receipt, not a desired final-state property or a standalone arbitrary Packet.

The new completed_head_opaque_output_not_discharged retains that entire head
conclusion. Its further inputs are the ACTUAL false recordTypes singleton and
the SAME remaining ResourceHistory at the literal callback restart decision,
framed cache, reached caller and full returned Memos. The result adds callback
isolation, output-own-cache isolation, output-own-native-heap lookup and
not-Discharged at that actual output. The head theorem is used once.
No final isolation or future callback/tail success is assumed as a shortcut.
The actual callback and admitted tail are explicit observed path inputs.
It does not assert that all outputs contain opaque events or that a marker
from one sibling enters another sibling's restored captured cache.

## One actual prefix, suffix and finalizer

complete_with_stable_prefix_resources retains the ENTIRE old traversal and
prefix admission contract. The old 5,226-byte contract recovers literally.
The entire old proof body also recovers after removal of the one added goal
and its proof. It uses the same old whole-traversal producer once and the same
consumed-prefix producer once. It appends a fixed prefixResult and its actual
adequate diagonal run family. The fixed result may be stopped. PrefixAdmission
continues to apply only when the observed prefix is complete. No old producer
admission or future-success gate is added.

The head consumer uses EdgeInputs.complete once to derive the actual own
allocation, its complete invariants and genuine child inputs. OwnPrefixPacket
derives the SAME caller/full-Memos/metadata Packet at that allocation.
Original head reservation supplies the complete child reservation.

Let B be the sum of the five returned prefix bounds and H the actual head
bound. Work B+H supplies both a stable head completion and an admitted actual
opaque event. The fixed completed prefixResult retains that event's caller,
cache and queries when work increases. PrefixAdmission independently supplies
full Memos, Packet, Fits, guard heap and genuine remaining inputs.

The old opaque suffix-isolation producer is used ONCE at that admitted event.
Its suffix reservation is weakened from the SAME event seed. No fictional
native advance is inserted for the cached opaque allocation. The next work
bound includes all suffix bounds. opaque_prepare_fuel proves that this Mu or
Union allocation is independent of the unused native-index fuel. Therefore
the enlarged actual head trace uses the SAME prepared cache.

The stable actual suffix aligns with the old resource producer's result.
A stopped producer shape contradicts the observed complete suffix. The exact
returned child cache, reached caller and saved queries then agree. The actual
residual and actual successful Finalize.run preserve the fresh isolated slot.
The parent target differs from that slot by original Ready.inside plus own
and prefix counter growth. Actual suffix Post.keeps retains the lookup in the
reached heap. Equality of queries is not used as equality of full Memos.

The output consumer uses the observed callback singleton to derive Success.
The actual recordTypes frame and separate Total from head.completed.safe
preserve the marker. ResourceHistory.isolated_boundary applies at the literal
restart decision. It retains the boundary and decoded value at the SAME
output's cache and heap, then not_discharged supplies the contradiction.

## Remaining work

1. Use the new parked and opaque consumers inside the whole-history semantic
   composition. A fully discharged output excludes those unresolved boundary
   events along its own path. State this as a history law with actual receipts.
   Do not replace actual head, callback or tail inputs with desired acceptance.
2. Derive the remaining fresh child-arity property from ACTUAL checked edge
   constructor or intersection provenance through native heap Posts.
   Context.annotation_heap supplies normalized guard tries, not child arity.
   Do not add a universal Ranges premise. Preserve existing checked-build and
   checked-worker arity proofs and all constructor/equality targets.
3. Recover child retention where the actual path permits it. Canonical and
   completion alone do not imply it. Keep the checked Mu/Union nonterminal
   retention obstructions. Use actual discharge and the new event exclusions
   where they rule out the path that loses constraints.
4. Compose backward assignment meaning for complete admitted histories.
   Apply actual rendering and residual checks to derive original acceptance
   for every eligible recursive output. Prove coverage separately under the
   exact solver, selector and pruning contracts. Operational stability is not
   semantic acceptance or coverage. Canonical is storage, not Satisfies.
5. Close remaining public API and physical Haskell correspondence boundaries.
   Keep the full original goal. Do not mark it complete for a local checkpoint.

## Haskell and upstream status

No Haskell source or Cabal file changed. Native checks were not repeated for
Lean-only edits. Main still points to 8766699b594eaad80381af2eee034c378ccf3192.
The LPO fix, extraction documentation repair and earlier Specftacular changes
remain integrated. FINDINGS retains every earlier repair handoff.

Upstream refresh fetched origin/fix/kbo-definition-weights at
 d7b6a9dfff464eb32c17c314d4825d5b027f1b2d. Its two changed files use Natural
rather than Int definition weights, use a lazy memoized acyclic weight map,
and add the public-map context-closure regression. Root inspected the source
patch. The candidate is not on main and is not integrated, built or executed
in this checkpoint. The current branch's prior KBO finding remains open.
Re-evaluate the repair and run the targeted regression after it lands on main.
No measured performance or runtime repair success is inferred from its message.

## Verification and restart evidence

Three new modules contain {lines} lines and four public theorems. Each installed
source matches its strict checked snapshot. Strict warningAsError and
linter.all pass with empty output. Strict Audit passes. The aggregate build
passes {jobs} jobs and {count} theorem dependency checks. The pre-existing
InternedFreshOrdinaryClosedCompletion warning is retained without suppression.

Full public readback checks seven signatures and their axiom sets. H6 and both
previous conditional captured-renderer public blocks are byte-identical.
The used axioms remain propext, Classical.choice and Quot.sound. No proof hole,
custom axiom, native_decide, heartbeat change or linter suppression is added.
The import-path setup failure and the wrong output-draft check path are
retained honestly with their source snapshots and corrected checks.

The restart archive is `restart-evidence/20261027-opaque-finalizer-attachment`.
It retains original drafts, immutable revisions, literal inspected source cuts,
whole-source identities, exact old contract/body recoveries, all strict and
build attempts, public readback, installed sources and independent review
seals. Nine old document bodies recover exactly after prefix removal.
The portable verifier checks manifests, compressed payloads, literal source
slices, review seals, installed source identity and document preservation.
Use --committed after the evidence commit to verify tracked bytes.
Archive creation, committed verification and publication occur after review.
Do not edit sealed review bundles or the frozen archive/TEMP area. Put later
proof work in a new area. Publication receipts stay outside the frozen area.
'''
name='lean/notes-current-opaque-finalizer-attachment.md';data=note.encode();(r/name).write_bytes(data);paths.append(name);records.append(dict(path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest()))
(a/'document-paths.json').write_text(json.dumps(paths,indent=2)+'\n');(a/'document-validation.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(dict(status='pass',documents=len(paths),source_head=head,modules=len(ms),lines=lines,jobs=jobs,theorem_checks=count)))
