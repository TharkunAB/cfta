import MicroCFTA.SourceCurrentAllocatedSeededMemos
import MicroCFTA.SourceCurrentConjunctionGlobalMemos
import MicroCFTA.SourceCurrentConjunctionClassScan
import MicroCFTA.SourceCurrentSecondaryMemos

/-!
# Three global gate tables through current checked class queries

The actual secondary gate returns its tables before projection starts.
The checked seeded fold returns its tables before the current conjunction
memo call. Proper selected paths derive each reached physical invariant.
No historical emptiness body or final table validity is supplied.
Completed receipts retain the stated GHC forcing and publication boundary.
-/
namespace MicroCFTA.SourceCurrentConjunctionQueryGlobalMemos
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "unconstrained" => SourceMemoGate.unconstrained
variable {width : Nat}

/-- The reached secondary gate, checked fold, and current call retain their exact returned tables. -/
inductive QueryReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    {paths : Class} {values : List (Value Symbol Guard)}
    {before middle : Checked width} {after : Physical} {anchor : State Symbol Guard}
    {query : Value Symbol Guard} {answer : Bool} {budget : Nat} {memo saved : Memo}
    (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.native.machine.heap false anchor)
    (seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
      (advanceHeap before anchor) query middle)
    (call : SourceCurrentConjunctionMemo.Call budget memo query (physical middle) answer after saved) :
    Memos → Memos → Prop where
  | run {memos first second final : Memos}
      (gateRead : SourceCurrentSecondaryMemos.ClassReads gate memos first)
      (seededRead : SourceCurrentAllocatedSeededMemos.SeededReads seeded first second)
      (callRead : SourceCurrentConjunctionGlobalMemos.CallReads call second final) :
      QueryReads gate seeded call memos final

/-- Actual current query execution derives coherent tables and physical and fourth-memo invariants. -/
theorem query_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (paths : Class) (values : List (Value Symbol Guard)) (proper : ∀ path ∈ paths, path ≠ [])
    {before middle : Checked width} {after : Physical} {anchor : State Symbol Guard}
    {query : Value Symbol Guard} {answer : Bool} {budget : Nat} {memo saved : Memo}
    (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.native.machine.heap false anchor)
    (seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
      (advanceHeap before anchor) query middle)
    (call : SourceCurrentConjunctionMemo.Call budget memo query (physical middle) answer after saved)
    (ranges : SourceCurrentAllocatedSeededQuery.SeededRanges values (paths.map (List.map Int.ofNat))
      (advanceHeap before anchor))
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ final, QueryReads gate seeded call memos final ∧ Valid after.heap final ∧
      Ready (advancePhysical middle after) ∧ Effects (physical before) after ∧
      Values after.heap values ∧ SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  have initialReady := SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs
  obtain ⟨anchorSemantic, anchorReady, _, anchorValues, supported⟩ :=
    SourceCurrentSecondaryProjectionScoped.class_support unconstrained gate ready.semantic
      (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available proper
  have first := SourceCurrentAllocatedGateFields.secondary_class unconstrained gate initialReady available
  have advancedReady := SourceCurrentConjunctionClassScan.advance_ready before ⟨anchor, before.operations⟩ ready first.1
  obtain ⟨gateMemos, gateRead, gateKept⟩ := SourceCurrentSecondaryMemos.lift_class _ _ _ _ _ gate
    (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available memos valid
  obtain ⟨chosen, reached, completed, queryGood, queryEffects, _, queryScopes, queryIdle, queryAvailable, _⟩ :=
    SourceCurrentAllocatedSeededQuery.false_class_complete unconstrained paths values gate ready.good initialReady
      ready.scopedCache ready.idle available proper ranges
  obtain ⟨rfl, rfl⟩ := seeded.unique completed
  obtain ⟨seedMemos, seedRead, seedValid, _, _⟩ := SourceCurrentAllocatedSeededMemos.seeded_memos
    unconstrained anchor anchorSemantic anchorReady seeded ranges advancedReady.good first.1.ready
      advancedReady.scopedCache advancedReady.idle anchorValues (grows_refl anchor)
      (by
        intro path member
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        exact supported original present) gateMemos gateKept.valid
  have queryReady : Ready middle :=
    ⟨queryGood, queryEffects.ready.semantic, queryEffects.ready.costs, queryScopes, queryIdle⟩
  have queryCorrect := SourceCurrentEmptinessMemo.grows formulas solver queryEffects.keeps memo correct
  obtain ⟨final, callRead, finalValid, _, _⟩ := SourceCurrentConjunctionGlobalMemos.call_memos
    call queryEffects.ready queryAvailable seedMemos seedValid
  obtain ⟨finalReady, callEffects, finalCorrect, _, retained⟩ :=
    SourceCurrentConjunctionClassScan.memo_effects formulas solver call queryReady queryAvailable queryCorrect
  exact ⟨final, .run gateRead seedRead callRead, finalValid, finalReady,
    queryEffects.trans callEffects,
    (fun value member => callEffects.keeps.available value (queryEffects.keeps.available value (available value member))),
    finalCorrect, retained⟩

end MicroCFTA.SourceCurrentConjunctionQueryGlobalMemos
