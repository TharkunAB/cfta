import MicroCFTA.SourceCurrentAllocatedMergePhysical

#print axioms MicroCFTA.SourceCurrentAllocatedMergePhysical.SafeCode.grows
#print axioms MicroCFTA.SourceCurrentAllocatedMergePhysical.body_safe
#print axioms MicroCFTA.SourceCurrentAllocatedMergePhysical.Run.verified
#print axioms MicroCFTA.SourceCurrentAllocatedMergeGraph.Call.verified
#print axioms MicroCFTA.SourceCurrentAllocatedMergeGraph.Run.extends
#print axioms MicroCFTA.SourceCurrentAllocatedMergeGraph.Call.extends
#print axioms MicroCFTA.SourceCurrentAllocatedMergePhysical.call_complete

set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedMergePhysical.SafeCode.grows
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedMergePhysical.body_safe
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedMergePhysical.Run.verified
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedMergeGraph.Call.verified
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedMergeGraph.Run.extends
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedMergeGraph.Call.extends
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedMergePhysical.call_complete

namespace MicroCFTA.AllocatedMergePhysicalProbes
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedMergeGraph
open SourceCurrentAllocatedMergePhysical
local notation "S" => SourceObservations.Label FullSyntax.Formula
local notation "G" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "P" => SourceCurrentAllocatedMergeGraph.State
local notation "Ops" => SourceEqualityConstraintMemoAllocation.State

-- The Top instruction needs no prior field-load premise.
example (operations : Ops) (symbol : S) (children : List (Value S G)) :
    SafeCode operations (.topRow symbol children) := trivial

-- Actual empty-field allocation supplies the exact Top load.
example (operations : Ops) (valid : SourceEqualityConstraintMemoAllocation.Valid operations) :
    SourceCurrentConjunctionEquality.FieldAvailable
      (SourceEqualityMkEdgeAllocation.emptyField operations) top :=
  (SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula) operations valid).2.2

-- The same actual allocation preserves every original field.
example (operations : Ops) (valid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (field : G) (available : SourceCurrentConjunctionEquality.FieldAvailable operations field) :
    SourceCurrentConjunctionEquality.FieldAvailable
      (SourceEqualityMkEdgeAllocation.emptyField operations) field :=
  available.grows (SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula) operations valid).2.1

section
variable [DecidableEq S] [DecidableEq (EdgeKey S G)]

-- The actual Top-row receipt keeps the returned operation state.
example (clear : G → Bool) (symbol : S) (children : List (Value S G)) (before : P) (memo : Memo) :
    Run clear (.topRow symbol children) before memo
      (run (makeEdge symbol top children) before.heap).1
      ⟨(run (makeEdge symbol top children) before.heap).2,
        SourceEqualityMkEdgeAllocation.emptyField before.equality⟩ memo :=
  .topRow symbol children before memo

-- A completed hit returns its winner at the identical physical state and memo.
example (clear : G → Bool) (before : P) (memo : Memo) (input : Value S G)
    (entry : SourceCurrentMemoMergeGraph.Entry S G)
    (found : memo input.referenceOf = some entry) :
    Call clear input before memo entry.result before memo := .hit found

-- A present hit derives readiness without a body receipt.
example (clear : G → Bool) (before : P) (memo : Memo) (input : Value S G)
    (entry : SourceCurrentMemoMergeGraph.Entry S G)
    (found : memo input.referenceOf = some entry)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (stored : SourceCurrentMemoMergeEffects.Stored before.heap memo)
    (available : Available before.heap input) :
    SourceCurrentConjunctionRowsAllocation.Ready before :=
  ((Call.hit found : Call clear input before memo entry.result before memo).verified ready stored available).1.ready

-- The completed-call theorem retains the literal completed memo table.
example {clear : G → Bool} {input output : Value S G} {before after : P} {memo saved : Memo}
    (actual : Call clear input before memo output after saved) : Cache.Extends memo saved := actual.extends

-- Empty input completion needs no closed-forest or Top availability premise.
example (clear : G → Bool) (before : P)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (available : Available before.heap (.empty : Value S G)) :
    ∃ output after saved, Call clear .empty before SourceCurrentMemoMergeGraph.empty output after saved ∧
      SourceCurrentConjunctionRowsAllocation.Effects before after ∧
      SourceCurrentMemoMergeEffects.Stored after.heap saved ∧ Available after.heap output ∧
      ((Value.empty : Value S G).free = [] → output.free = []) :=
  call_complete clear .empty before SourceCurrentMemoMergeGraph.empty ready
    (SourceCurrentMemoMergeEffects.stored_empty before.heap) available

-- An open ordinary input follows the literal unchanged-body branch.
example (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue S G))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (openInput : free ≠ []) :
    body (.node entry edges depth free) = .pure (.node entry edges depth free) := by
  simp only [body, openInput, ite_false]
end
end MicroCFTA.AllocatedMergePhysicalProbes
