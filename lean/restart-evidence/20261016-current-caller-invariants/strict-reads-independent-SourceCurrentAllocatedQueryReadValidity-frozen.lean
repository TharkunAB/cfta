import MicroCFTA.SourceCurrentAllocatedGateReadValidity
import MicroCFTA.SourceCurrentAllocatedSeededReadValidity
import MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity

/-!
# Validity of supplied current class-query reads

The secondary gate, seeded fold, and conjunction call retain the exact
returned bundle supplied to each next phase. Physical effects come from
the actual source graphs and reached word checks.
-/
namespace MicroCFTA.SourceCurrentAllocatedQueryReadValidity
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
open SourceCurrentConjunctionQueryGlobalMemos (QueryReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "unconstrained" => SourceMemoGate.unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- A supplied query receipt derives validity of its actual final tables and its physical receipt. -/
theorem query
    {paths : Class} {values : List (Value Symbol Guard)}
    {before middle : Checked width} {after : Physical} {anchor : State Symbol Guard}
    {value : Value Symbol Guard} {answer : Bool} {budget : Nat} {memo saved : Memo}
    {gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.native.machine.heap false anchor}
    {seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
      (advanceHeap before anchor) value middle}
    {call : SourceCurrentConjunctionMemo.Call budget memo value (physical middle) answer after saved}
    {memos final : Memos} (reads : QueryReads gate seeded call memos final)
    (proper : ∀ path ∈ paths, path ≠ [])
    (ranges : SourceCurrentAllocatedSeededQuery.SeededRanges values (paths.map (List.map Int.ofNat))
      (advanceHeap before anchor))
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (valid : Valid before.native.machine.heap memos) :
    Valid after.heap final ∧ Ready (advancePhysical middle after) ∧ Effects (physical before) after ∧
      Values after.heap values ∧ SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  cases reads with
  | run gateRead seedRead callRead =>
      have initialReady := SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs
      obtain ⟨anchorSemantic, anchorReady, _, anchorValues, supported⟩ :=
        SourceCurrentSecondaryProjectionScoped.class_support unconstrained gate ready.semantic
          (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available proper
      have first := SourceCurrentAllocatedGateFields.secondary_class unconstrained gate initialReady available
      have advancedReady := SourceCurrentConjunctionClassScan.advance_ready before ⟨anchor, before.operations⟩ ready first.1
      have gateKept := SourceCurrentAllocatedGateReadValidity.secondary_class gateRead
        (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available valid
      obtain ⟨chosen, reached, completed, queryGood, queryEffects, _, queryScopes, queryIdle, queryAvailable, _⟩ :=
        SourceCurrentAllocatedSeededQuery.false_class_complete unconstrained paths values gate ready.good initialReady
          ready.scopedCache ready.idle available proper ranges
      obtain ⟨rfl, rfl⟩ := seeded.unique completed
      have seedValid := SourceCurrentAllocatedSeededReadValidity.seeded unconstrained anchor anchorSemantic anchorReady
        seedRead ranges advancedReady.good first.1.ready advancedReady.scopedCache advancedReady.idle anchorValues
        (grows_refl anchor) (by
          intro path member
          obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
          exact supported original present) gateKept.valid
      have queryReady : Ready middle :=
        ⟨queryGood, queryEffects.ready.semantic, queryEffects.ready.costs, queryScopes, queryIdle⟩
      have queryCorrect := SourceCurrentEmptinessMemo.grows formulas solver queryEffects.keeps memo correct
      have finalValid := SourceCurrentAllocatedConjunctionReadValidity.call callRead queryEffects.ready queryAvailable seedValid.1
      obtain ⟨finalReady, callEffects, finalCorrect, _, retained⟩ :=
        SourceCurrentConjunctionClassScan.memo_effects formulas solver call queryReady queryAvailable queryCorrect
      exact ⟨finalValid.1, finalReady, queryEffects.trans callEffects,
        (fun value member => callEffects.keeps.available value (queryEffects.keeps.available value (available value member))),
        finalCorrect, retained⟩

end MicroCFTA.SourceCurrentAllocatedQueryReadValidity
