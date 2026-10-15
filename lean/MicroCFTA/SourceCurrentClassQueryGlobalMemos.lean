import MicroCFTA.SourceDecisionGlobalMemos
import MicroCFTA.SourceClassQueryGlobalMemos
import MicroCFTA.SourceCurrentSecondaryMemos
import MicroCFTA.SourceCurrentSecondaryEffects

/-!
# Current secondary class queries with all four completed memo families

The current secondary gate returns its three tables before the seeded fold
starts. The fold returns its tables before the separate emptiness memo call.
Proper original paths supply anchored projection support. No acceptance or
final-validity premise is needed. The receipts retain completed scoped
execution. They do not transfer GHC demand or pending memo publication.
-/
namespace MicroCFTA.SourceCurrentClassQueryGlobalMemos
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEmptinessClassFold SourceClassQueryGlobalMemos SourceCurrentSecondaryProjectionScoped
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained

/-- The actual secondary, seeded, and fourth-memo calls pass the same three tables in order. -/
inductive QueryReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {paths : Class} {values : List (Value Symbol Guard)}
    {before middle after : Native width Symbol Guard} {anchor : State Symbol Guard}
    {query : Value Symbol Guard} {answer : Bool} {memo saved : SourceCurrentEmptinessMemo.Memo}
    (gate : SourceCurrentSecondaryTrace.ClassTrace source values paths before.machine.heap false anchor)
    (seeded : Seeded top conjoin values (paths.map (List.map Int.ofNat)) (advanceHeap before anchor) query middle)
    (call : SourceCurrentEmptinessMemo.Call memo query middle answer after saved) : Memos → Memos → Prop where
  | run {memos first second final : Memos}
      (gateRead : SourceCurrentSecondaryMemos.ClassReads gate memos first)
      (seededRead : SeededReads seeded first second)
      (callRead : SourceDecisionGlobalMemos.CallReads call second final) : QueryReads gate seeded call memos final

/-- Proper original paths derive all returned heap and memo invariants through the actual query. -/
theorem query_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (paths : Class) (values : List (Value Symbol Guard)) (proper : ∀ path ∈ paths, path ≠ [])
    {before middle after : Native width Symbol Guard} {anchor : State Symbol Guard}
    {query : Value Symbol Guard} {answer : Bool} {memo saved : SourceCurrentEmptinessMemo.Memo}
    (gate : SourceCurrentSecondaryTrace.ClassTrace source values paths before.machine.heap false anchor)
    (seeded : Seeded top conjoin values (paths.map (List.map Int.ofNat)) (advanceHeap before anchor) query middle)
    (call : SourceCurrentEmptinessMemo.Call memo query middle answer after saved)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ final, QueryReads gate seeded call memos final ∧ Valid after.machine.heap final ∧
      IdleReady top conjoin after ∧ CostHeap after.machine.heap ∧ FieldHeap after.machine.heap ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap values ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  have gateReady := SourceEqualityExposureCosts.gate_ready ready.semantic costs
  obtain ⟨anchorSemantic, anchorReady, kept, anchorValues, supported⟩ :=
    class_support source gate ready.semantic gateReady available proper
  obtain ⟨gateMemos, gateRead, gateKept⟩ := SourceCurrentSecondaryMemos.lift_class _ _ _ _ _
    gate gateReady available memos valid
  have signedSupport : ∀ path ∈ paths.map (List.map Int.ofNat), PathSupport source anchor path values := by
    intro path member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact supported original present
  have advancedReady := ready.advance anchor kept anchorSemantic
  have anchorFields : FieldHeap anchor := SourceCurrentSecondaryEffects.class_effects
    (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities)
    source gate ready.semantic costs available fields |>.2.2.2
  have folded := SourceCurrentSecondaryClassFold.seeded_effects source anchor anchorSemantic anchorReady
    seeded advancedReady anchorValues (grows_refl anchor) signedSupport
  have foldedCosts := SourceCurrentSecondaryQueryCosts.seeded_costs source anchor anchorSemantic anchorReady
    seeded advancedReady anchorValues (grows_refl anchor) signedSupport anchorReady.2.2.2
  obtain ⟨seedMemos, seedRead, seedValid, _, _⟩ := seeded_memos source anchor anchorSemantic anchorReady
    seeded advancedReady anchorValues (grows_refl anchor) signedSupport anchorReady.2.2.2 gateMemos gateKept.valid
  obtain ⟨final, callRead, finalValid, _, _⟩ := SourceDecisionGlobalMemos.call_memos call folded.1 foldedCosts seedMemos seedValid
  have effects := SourceCurrentSecondaryQueryCosts.seeded_memo_ready source anchor anchorSemantic anchorReady
    seeded call advancedReady anchorValues (grows_refl anchor) signedSupport anchorReady.2.2.2 anchorFields
    formulas solver (SourceCurrentEmptinessMemo.grows formulas solver kept memo correct)
  have retained := kept.trans effects.2.2.2.1
  exact ⟨final, .run gateRead seedRead callRead, finalValid, effects.1, effects.2.1, effects.2.2.2.2.1,
    retained, (fun value member => retained.available value (available value member)), effects.2.2.2.2.2⟩

end MicroCFTA.SourceCurrentClassQueryGlobalMemos
