# Independent native execution review

Reviewed at 2026-10-17T01:54:35.968428+02:00. Result: PASS. No material defect was found. This task changed no production source. The only repository artifact owned by this review is this note.

The final review uses these immutable production bytes:

| Source in lean/MicroCFTA | SHA256 | Status |
| --- | --- | --- |
| SourceCurrentHereditaryNativeControl.lean | 8eae5d6ffcd78bd2b04174a1a71965efbbe56431de106286dce968d3daefbfa9 | Final strict and canonical green |
| SourceCurrentHereditaryNativeTransition.lean | 17d9cc3b94a00271df59125cc0f860f0fe59ac701328749db6db4923c9bb588e | Final strict and canonical green |
| SourceCurrentHereditaryNativeTraceInduction.lean | 39389aee7ced388c5ef6e828d6c816dda54d15c663f181614ce02b5595e2db7f | Final strict and canonical green |
| SourceCurrentHereditaryNativeTrace.lean | 87c9be08eb447b0a6f9197464218fab4774000c58fbde17b9b758c72585b69f3 | Final strict and canonical green |
| SourceCurrentHereditaryNativeCold.lean | c6eea09f7d4e75998212eb5b8e5a369331d3795998a8191a6e9cf561131f78d4 | Final strict and canonical green |

The preliminary review read an earlier uncompiled Trace draft. This final assessment uses the final Trace above. Control was later cleaned to remove unused section instances. The final imported checks below ran after that cleanup and the final canonical rebuild. The earlier warning and failed probe logs remain intact.

`NativeControl.Certified` is a local source-code contract. Its demanded edge case retains the actual Bindings and annotations of both queried rows. Its continuation receives the actual returned machine, Extension, MuStored, physical residency, and the conditional law of that exact request. `Stored` contains two distinct causal invariants: constructor MuStored and native returned-cell laws. Neither field requires every resident guard to be plain.

`node_law` and `edge_law` use an already derived annotation of the actual result to produce a conditional cache law. They do not infer an annotation from a key or from physical readiness. The annotation predicate and fixed source remain the same. Thus a finished cell can retain a conditional law even when unrelated source records are constrained.

`NativeTransition` splits actual yielded requests into the literal direct, warm, and evaluating branches. A node direct branch preserves the full checked state. Warm branches use physical cache validity, current operands, and exact key bounds to recover the whole original request at the observed handle. They apply that entry's own NodeLaw or EdgeLaw. They do not reuse another candidate's law. Both lookup and demand preserve the actual native machine and equality-operation state. Evaluating branches retain the exact captured request at the actual running handle. Absent and busy outcomes cannot satisfy the supplied yielded equation. The proofs do not convert those outcomes to success.

`NativeTraceInduction.Preserves` describes supplied completed raw checked Steps. It contains no assertion that a trace exists. The bind, node_bind, and edge_bind helpers accept an IH only at counts below their bound. `steps_bind_inverse` identifies the exact earlier inner return and subsequent suffix. The main theorem calls each helper after one actual yielded source instruction. Therefore the helper fuel is strictly below the main induction count. Both the inner and suffix counts are also smaller. No same-size recursive call is hidden in a continuation.

Each helper obtains physical Current, Extension, actual result availability or residency, and operation growth from the previously proved raw-prefix admission theorem. That theorem uses explicit initial source facts, a source-closed finite domain inventory, initial domain-cache validity, source node and edge key bounds, and initial domain headroom. It does not require WordRanges, a completed enclosing query, or a future trace invariant as an input.

A captured finish uses the annotation produced by the smaller actual body trace. It derives the NodeLaw or EdgeLaw before publication. The protected-prefix theorem retains the exact evaluating request at the same handle until that finish. It requires the current physical Shape and actual body trace. The finish then updates that owner and retains other returned laws. Its checked state keeps the same constructor heap and equality operations. The suffix receives the stored laws and physical facts at this exact finished state. Forward ownership survival is not inferred merely from an absence of new active cells.

The main `NativeTrace.completed` theorem closes the bounded IH by strong induction. Its Work branch uses the companion WorkSafe producer before it invokes the local continuation. Its optional-binder branch uses the actual successful constructor result to derive both MuStored and the result annotation. Pending cannot yield a completed continuation. Enter changes only the domain cache. Read uses the literal current payload. Existing native returned-cell laws survive these machine changes because their request and result records remain unchanged.

Fresh node compilation receives actual original-source availability, Bindings, both input annotations, current physical readiness, MuStored, and source-to-current histories. Its compiler certificate is constructed internally. Checked edge-body compilation uses the actual field loads and conjunction result at the returned operation state. The emitted child or sentinel code supplies its own constructor-effect producers. No global Heap Plain condition replaces these local premises.

The helper continuation arguments are compositional code contracts. The main proof constructs them from the original local and physical certificates. They are not public assumptions that a future recursive body has succeeded or returned a desired result. The final cold endpoint constructs its initial certificates from source scope, local annotations, and empty native memo tables.

`NativeCold.cold_complete` calls the older initial-resource completion theorem to obtain its own exact finite receipt. It applies the new annotation theorem to `receipt.trace.steps`. The output is that same receipt, fuel, value, full checked state, language law, scope, idle condition, and closedness, with the new causal stores and result annotation added. It does not choose a second completion or replace the receipt's heap. It supplies no successful native execution as an initial premise. Original inputs, availability, closedness, initial physical and semantic readiness, finite key/domain resource bounds, and the causal constructor store remain explicit initial conditions.

The domain bound can be large. The cold endpoint uses the existing coarse inventory size 2^(N+N²). Its initial headroom condition can be impractical for a fixed machine width. The proof does not discharge this condition for every source program. It does not establish general selected-edit or outer completion, arbitrary residual guards, a GHC lazy schedule, signed conversion behavior, or whole-library implementation correspondence. This is a checked-model recursive query result under its stated initial conditions.

Final validation: the canonical Audit log `lean-audit-control-scope.log` records 2734 jobs and 61966 dependency checks. Imported independent probes then passed with all linters enabled. There are nine public axiom/full-signature pairs for Control, Transition, and Trace, plus three integration pairs. All twelve final pairs contain no warning, error, sorryAx, or truncated signature.

The two warm kernels derive the literal checked yielded state, both causal stores, and the actual value or full row annotation from an observed ready lookup. Their inputs describe only initial invariants, exact physical lookup/demand equations, and local queried operand annotations. The third kernel starts with a supplied literal node Steps trace. It constructs the static physical and local certificates from initial request scope, readiness, Bindings, and annotations, then derives the actual returned stores and annotation. It takes no WordRanges or final-result law.

To respect the single-file ownership, the probe source and raw logs were written under /tmp. Their final identifiers are:

- `/tmp/mcfta-native-control-transition-review.lean`: SHA256 `16f28e73e477d894d7b53ebbfa8bdf3c76d6031f0a352076794041a6c6d9bcc5`.
- `/tmp/mcfta-native-control-transition-review-control-scope.log`: SHA256 `14a7646479191abec60d0f42ac07fe627dc1694f8a8329cca37639c4d08a6dca`; exit 0.

The final probe source is retained below so the checks remain reproducible if /tmp is cleared. The older evidence-only namespace-error attempt and pre-cleanup logs remain under /tmp. They are not final validation.

```lean
import MicroCFTA.SourceCurrentHereditaryNativeTrace
import MicroCFTA.SourceCurrentHereditaryNativeControl
import MicroCFTA.SourceCurrentHereditaryNativeTransition

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.NativeExecutionReview
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityAnnotationLanguage
open SourceCurrentHereditaryNativeScope (Bindings)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A warm observed node uses the exact queried owner and the actual full returned state. -/
theorem warm_node (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (request : NodeRequest Symbol Guard) (before : Checked width) (chosen returned : Native width Symbol Guard)
    (handle : Nat) (value : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (stored : SourceCurrentHereditaryNativeControl.Stored annotation source before)
    (ready : NodeReady before.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (bindings : Bindings annotation source request.domain.key)
    (left : Annotated annotation request.left) (right : Annotated annotation request.right)
    (selected : lookupNode width request before.native = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.ready value, returned)) :
    let after : Checked width := ⟨returned, before.operations⟩
    SourceEqualityNativeDemand.step (.code (.node request .pure)) before = .yielded (.code (.pure value)) after ∧
      SourceCurrentHereditaryNativeControl.Stored annotation source after ∧
      Available after.native.machine.heap value ∧ Annotated annotation value := by
  dsimp only
  have receipt := SourceCurrentHereditaryNativeCache.node_observed_ready annotation source request before.native chosen returned handle value
    physical stored.native ready safe selected demanded
  have chosenMachine : chosen.machine = before.native.machine := by
    simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_machine request before.native
  have constructors : SourceCurrentHereditaryConstruction.MuStored annotation returned.machine.heap := by
    rw [receipt.2.2.1, chosenMachine]
    exact stored.constructors
  exact ⟨by simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded, lift],
    ⟨constructors, receipt.2.1⟩, receipt.2.2.2, receipt.1 bindings left right⟩

/-- A warm observed row retains its full guard and children at the same checked return. -/
theorem warm_edge (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (request : EdgeRequest Symbol Guard) (before : Checked width) (chosen returned : Native width Symbol Guard)
    (handle : Nat) (value : EdgeValue Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (stored : SourceCurrentHereditaryNativeControl.Stored annotation source before)
    (ready : EdgeReady before.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (bindings : Bindings annotation source request.domain.key)
    (left : SourceCurrentHereditaryConstructors.Edge annotation request.left)
    (right : SourceCurrentHereditaryConstructors.Edge annotation request.right)
    (selected : lookupEdge width request before.native = (handle, chosen))
    (demanded : demandEdge handle chosen = (.ready value, returned)) :
    let after : Checked width := ⟨returned, before.operations⟩
    SourceEqualityNativeDemand.step (.code (.edge request .pure)) before = .yielded (.code (.pure value)) after ∧
      SourceCurrentHereditaryNativeControl.Stored annotation source after ∧
      EdgeResident after.native.machine.heap value ∧ SourceCurrentHereditaryConstructors.Edge annotation value := by
  dsimp only
  have receipt := SourceCurrentHereditaryNativeCache.edge_observed_ready annotation source request before.native chosen returned handle value
    physical stored.native ready safe selected demanded
  have chosenMachine : chosen.machine = before.native.machine := by
    simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_machine request before.native
  have constructors : SourceCurrentHereditaryConstruction.MuStored annotation returned.machine.heap := by
    rw [receipt.2.2.1, chosenMachine]
    exact stored.constructors
  exact ⟨by simp only [SourceEqualityNativeDemand.step, selected, demanded],
    ⟨constructors, receipt.2.1⟩, receipt.2.2.2, receipt.1 bindings left right⟩

/-- A supplied literal node trace constructs its own local certificates from initial inputs. -/
theorem actual_node_trace {bits fuel : Nat} {source : InternedConstructorTemplates.State Symbol Guard}
    {inventory : List IntersectionFlatMemoKeyDomain.DomainKey} {initial : Cache.State IntersectionFlatMemoKeyDomain.DomainKey}
    (resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources bits source inventory initial)
    (request : NodeRequest Symbol Guard) (before after : Checked (bits + 2)) (value : Value Symbol Guard)
    (known : SourceCurrentAllocatedRecursivePrefixState.Current source inventory initial before)
    (ready : NodeReady before.native.machine request) (scope : SourceRecursiveIntersectionCode.NodeScope source request)
    (member : request.domain.key ∈ inventory)
    (stored : SourceCurrentHereditaryNativeControl.Stored (fun guard => SourceMemoGate.plain guard = true) source before)
    (bindings : Bindings (fun guard => SourceMemoGate.plain guard = true) source request.domain.key)
    (left : Annotated (fun guard => SourceMemoGate.plain guard = true) request.left)
    (right : Annotated (fun guard => SourceMemoGate.plain guard = true) request.right)
    (actual : SourceEqualityNativeDemand.Steps fuel
      (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after) :
    SourceCurrentHereditaryNativeControl.Stored (fun guard => SourceMemoGate.plain guard = true) source after ∧
      Available after.native.machine.heap value ∧ Annotated (fun guard => SourceMemoGate.plain guard = true) value := by
  have physical := SourceCurrentAllocatedRecursivePrefixCode.request_node source inventory request before.native.machine ready scope member
  have localCertificate := SourceCurrentHereditaryNativeEffects.request_node
    (fun guard => SourceMemoGate.plain guard = true) source request before.native.machine bindings left right
  exact SourceCurrentHereditaryNativeTrace.completed resources fuel
    (.code (requestNode request.domain request.left request.right)) before after value
    (fun state result => Available state.heap result)
    (fun state result => Available state.heap result ∧ Annotated (fun guard => SourceMemoGate.plain guard = true) result)
    known physical (by intro _; trivial) localCertificate stored actual

#print axioms warm_node
#check @warm_node
#print axioms warm_edge
#check @warm_edge
#print axioms actual_node_trace
#check @actual_node_trace
end MicroCFTA.NativeExecutionReview

#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.Certified
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.Certified
#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.Stored
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.Stored
#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.pure_result
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.pure_result
#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.certified_bind
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.certified_bind
#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.node_law
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.node_law
#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.edge_law
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.edge_law
#print axioms MicroCFTA.SourceCurrentHereditaryNativeTransition.node_yielded
#check @MicroCFTA.SourceCurrentHereditaryNativeTransition.node_yielded
#print axioms MicroCFTA.SourceCurrentHereditaryNativeTransition.edge_yielded
#check @MicroCFTA.SourceCurrentHereditaryNativeTransition.edge_yielded

#print axioms MicroCFTA.SourceCurrentHereditaryNativeTrace.completed
#check @MicroCFTA.SourceCurrentHereditaryNativeTrace.completed
```
