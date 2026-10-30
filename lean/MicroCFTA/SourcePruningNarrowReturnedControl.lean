import MicroCFTA.SourcePruningNarrowControl
import MicroCFTA.MergedFreshOrdinaryColdReplay

/-!
# Control of actual returned narrowing results

Every successful narrowing has a stable result at larger fuel.
Its observed result receives the normal form and retained-row properties
from the existing closed-input completion proof at a common bound.
No future completion or supplied normalization observation is required.

-/
namespace MicroCFTA.SourcePruningNativeView
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
local notation "Symbol" => SourcePruningTemplates.Symbol
attribute [local instance] FormulaExecutable.formulaDecidableEq
variable {Guard Key : Type}

/-- Every actual successful filter keeps its exact result and heap at larger fuel. -/
theorem narrowAt_returned_stable [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel extra : Nat) (key : Key) (value result : Value Symbol Guard) (before after : State Symbol Guard)
    (returned : narrowAt fits admits fuel key value before = .done result after) :
    narrowAt fits admits (fuel + extra) key value before = .done result after := by
  cases exposed : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | done rows middle =>
      have extended := (MergedFreshOrdinaryColdReplay.nodeEdges_stable fuel extra value before
        (by simp only [exposed, MergedSourceExposure.Finished])).trans exposed
      simp only [narrowAt, exposed] at returned
      simpa only [narrowAt, extended] using returned
  | unresolved | pending | exhausted =>
      simp only [narrowAt, exposed] at returned
      cases returned

/-- Actual closed-input success supplies its own normal result, cache lineage and replay. -/
theorem narrowAt_returned_control [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel : Nat) (key : Key) (value result : Value Symbol Guard) (before after : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = [])
    (returned : narrowAt fits admits fuel key value before = .done result after) :
    SourceEqualityRequiredCache.Keeps before after ∧
      Available after result ∧ result.free = [] ∧ SourceEqualityRequiredCache.Ordinary result ∧
      EqualityOrdinaryReadback.Normal after result ∧
      (∀ edge ∈ nodeEdges result, keeps fits admits key edge = true) ∧
      (∀ repeatFuel, narrowAt fits admits repeatFuel key result after = .done result after) := by
  obtain ⟨chosenFuel, rows, middle, expected, expectedAfter, exposed, built, completed,
      kept, resultAvailable, resultClosed, ordinary, normal, resultRows, stable, replay⟩ :=
    narrowAt_complete_control fits admits key value before ready available closed
  have actualCommon := narrowAt_returned_stable fits admits fuel chosenFuel key value result before after returned
  have chosenCommon := stable fuel
  rw [Nat.add_comm chosenFuel fuel] at chosenCommon
  have same := MergedSourceComparison.Result.done.inj (actualCommon.symm.trans chosenCommon)
  rcases same with ⟨rfl, rfl⟩
  exact ⟨kept, resultAvailable, resultClosed, ordinary, normal,
    fun edge member => (resultRows edge member).2, replay⟩

end MicroCFTA.SourcePruningNativeView

namespace MicroCFTA.SourcePruningEnumerationAction
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourcePruningNativeView SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
attribute [local instance] FormulaExecutable.formulaDecidableEq
variable {Guard EnumGuard Typing Key : Type}

/-- An actual changed preparation result supplies its filtered normal form internally. -/
theorem prepare_changed_returned_control [DecidableEq (EdgeKey Symbol Guard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (nativeFuel representativeFuel uv oldHandle newHandle : Nat) (scs : List EnumerationState.Suspended)
    (value result : Value Symbol Guard) (before after : State Symbol Guard)
    (action : Option (EnumerationState.EnumerateM Symbol EnumGuard Unit))
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = [])
    (returned : prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs value before =
      .done (result, action) after)
    (oldEncoded : encodeNode value = some oldHandle)
    (newEncoded : encodeNode result = some newHandle) (changed : newHandle ≠ oldHandle) :
    narrowAt fits admits nativeFuel (holeKey metadata.typing uv) value before = .done result after ∧
      SourceEqualityRequiredCache.Keeps before after ∧
      Available after result ∧ result.free = [] ∧ SourceEqualityRequiredCache.Ordinary result ∧
      EqualityOrdinaryReadback.Normal after result ∧
      (∀ edge ∈ nodeEdges result, keeps fits admits (holeKey metadata.typing uv) edge = true) ∧
      (∀ repeatFuel, narrowAt fits admits repeatFuel (holeKey metadata.typing uv) result after = .done result after) := by
  have outerReturned : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv value before =
      .done result after := by
    cases query : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv value before with
    | failed =>
        simp only [prepare, query] at returned
        cases returned
    | done nextValue nextHeap =>
        simp only [prepare, query] at returned
        have same := MergedSourceComparison.Result.done.inj returned
        have sameValue : nextValue = result := congrArg Prod.fst same.1
        have sameHeap : nextHeap = after := same.2
        simp only [sameValue, sameHeap]
  have changedValue : result ≠ value := by
    intro same
    rw [same] at newEncoded
    exact changed (Option.some.inj (newEncoded.symm.trans oldEncoded))
  have filtered : narrowAt fits admits nativeFuel (holeKey metadata.typing uv) value before = .done result after := by
    cases value with
    | mu entry body depth ordinary =>
        simp only [SourcePruningOuterNarrow.narrow] at outerReturned
        exact (changedValue (MergedSourceComparison.Result.done.inj outerReturned).1.symm).elim
    | empty | reference | node | union =>
        simp only [SourcePruningOuterNarrow.narrow] at outerReturned
        split at outerReturned
        · exact (changedValue (MergedSourceComparison.Result.done.inj outerReturned).1.symm).elim
        · exact outerReturned
  exact ⟨filtered, narrowAt_returned_control fits admits nativeFuel (holeKey metadata.typing uv)
    value result before after ready available closed filtered⟩

end MicroCFTA.SourcePruningEnumerationAction
