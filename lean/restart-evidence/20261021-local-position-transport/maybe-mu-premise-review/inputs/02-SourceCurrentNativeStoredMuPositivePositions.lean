import MicroCFTA.SourceCurrentNativePublicationTrace
import MicroCFTA.SourceCurrentRequiredPositivePosition

/-!
# Positive positions after source-derived stored Mu readback

An actual checked prefix derives the selected record's causal history.
Smart readback exposes positive positions exactly when the stored probe
has no deep local. The ordinary probe retains the same child path.
-/
namespace MicroCFTA.SourceCurrentNativeStoredMuPositivePositions
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentRequiredPositivePosition (PositiveAt)
open SourceCurrentNativeMuPublication (History)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Trace" => SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace
variable {A : Type} {width fuel : Nat}

private theorem erase_positions (name : InternedBinderProtocol.Reference)
    (value : Value Symbol Guard) (path : List Nat) :
    PositiveAt (SourceCurrentNativeCallbackErasure.eraseSelf name value) path ↔ PositiveAt value path := by
  unfold SourceCurrentNativeCallbackErasure.eraseSelf
  split
  · rename_i erased
    constructor
    · intro impossible; cases impossible
    · intro positive
      cases positive <;> simp [Value.referenceOf] at erased
  · rfl

private theorem heap_positions [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (history : History empty state)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : state.nodeRecords key = some (.mu entry body depth ordinary))
    (smart : Bool) (path : List Nat) :
    PositiveAt (InternedNestedConstruction.finish smart (.mu entry body depth ordinary)) path ↔
      smart = true ∧ InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false ∧
        PositiveAt ordinary path := by
  cases smart with
  | false =>
      simp only [InternedNestedConstruction.finish, Bool.false_eq_true, ↓reduceIte, false_and]
      constructor
      · intro impossible; cases impossible
      · intro impossible; cases impossible
  | true =>
      cases used : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary with
      | false =>
          have returned := SourceCurrentNativeNormalizedComparisonExecution.history_unused
            state history key entry body depth ordinary present used
          rw [returned,erase_positions]
          simp only [true_and]
      | true =>
          have returned := SourceCurrentNativeNormalizedComparison.retained_of_used entry body depth ordinary
            (semantic.2 key entry body depth ordinary present) used
          rw [returned]
          simp only [Bool.true_eq_false, false_and, and_false]
          constructor
          · intro impossible; cases impossible
          · intro impossible; cases impossible

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A warm checked prefix derives exact positive positions from its actual prior source history. -/
theorem reached {control rest : Control A} {before after : Checked width}
    (actual : Trace fuel control before rest after) (semantic : SemanticHeap before.native.machine.heap)
    (earlier : History empty before.native.machine.heap)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : after.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary))
    (smart : Bool) (path : List Nat) :
    PositiveAt (InternedNestedConstruction.finish smart (.mu entry body depth ordinary)) path ↔
      smart = true ∧ InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false ∧
        PositiveAt ordinary path := by
  obtain ⟨current,⟨history⟩⟩ := SourceCurrentNativePublicationTrace.from_history actual semantic earlier
  exact heap_positions _ current history key entry body depth ordinary present smart path

/-- Actual initial source construction supplies the stored readback law at the same reached cell. -/
theorem source (source : InternedNestedConstruction.Syntax Symbol Guard)
    {control rest : Control A} {before after : Checked width}
    (actual : Trace fuel control before rest after)
    (initial : before.native.machine.heap =
      (InternedFreshOrdinaryConstruction.build source [] empty).state)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : after.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary))
    (smart : Bool) (path : List Nat) :
    PositiveAt (InternedNestedConstruction.finish smart (.mu entry body depth ordinary)) path ↔
      smart = true ∧ InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false ∧
        PositiveAt ordinary path := by
  obtain ⟨current,⟨history⟩⟩ := SourceCurrentNativePublicationTrace.source_trace source actual initial
  exact heap_positions _ current history key entry body depth ordinary present smart path

end MicroCFTA.SourceCurrentNativeStoredMuPositivePositions
