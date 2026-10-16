import MicroCFTA.SourceCurrentAllocatedMergeGraph
import MicroCFTA.SourceCurrentConjunctionFieldAllocation
namespace MicroCFTA.AllocatedMergeGraphKernels
open InternedConstructorTemplates
open SourceCurrentAllocatedMergeGraph
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentAllocatedMergeGraph.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- Top construction retains the actual edge request and the literal equality allocation state.
example (clear : Guard → Bool) (symbol : Symbol) (children : List (Value Symbol Guard))
 (before : Physical) (memo : Memo) :
 Run clear (.topRow symbol children) before memo (run (makeEdge symbol top children) before.heap).1
  ⟨(run (makeEdge symbol top children) before.heap).2, SourceEqualityMkEdgeAllocation.emptyField before.equality⟩ memo :=
 .topRow symbol children before memo

-- Raw small-row work retains its original guard and does not change equality operations.
example (clear : Guard → Bool) (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard))
 (before : Physical) (memo : Memo) :
 Run clear (.work (makeEdge symbol guard children)) before memo (run (makeEdge symbol guard children) before.heap).1
  ⟨(run (makeEdge symbol guard children) before.heap).2, before.equality⟩ memo := .work _ _ _

-- A completed hit is available with the whole physical state unchanged and no Top coverage premise.
example (clear : Guard → Bool) (input : Value Symbol Guard) (before : Physical) (memo : Memo)
 (entry : SourceCurrentMemoMergeGraph.Entry Symbol Guard) (found : memo input.referenceOf = some entry) :
 Call clear input before memo entry.result before memo := .hit found

-- A miss on EmptyNode has no constructor or equality allocation work.
example (clear : Guard → Bool) (before : Physical) (memo : Memo)
 (absent : memo .empty = none) :
 Call clear .empty before memo (SourceCurrentMemoMergeGraph.winner memo .empty .empty).result before
  (SourceCurrentMemoMergeGraph.remember memo .empty .empty) := by
 apply Call.miss absent
 change Run clear (.pure (.empty : Value Symbol Guard)) before memo .empty before memo
 exact .pure _ _ _

-- Every actual old call constructs a new call and erases to the same literal old result/state/memo.
example {clear : Guard → Bool} {input output : Value Symbol Guard} {before after : Heap} {memo saved : Memo}
 (actual : SourceCurrentMemoMergeGraph.Call clear top input before memo output after saved)
 (operations : SourceEqualityConstraintMemoAllocation.State) :
 ∃ final, Call clear input ⟨before, operations⟩ memo output ⟨after, final⟩ saved ∧
  SourceCurrentMemoMergeGraph.Call clear top input before memo output after saved := by
 obtain ⟨final, next⟩ := call_lift actual operations
 exact ⟨final, next, next.graph⟩

-- Two actual Top instructions thread the first allocation into the second.
example (clear : Guard → Bool) (one two : Symbol) (before : Physical) (memo : Memo) :
 let first := run (makeEdge one top []) before.heap
 let second := run (makeEdge two top [.empty]) first.2
 Run clear (.bind (.topRow one []) (fun _ => .topRow two [.empty])) before memo second.1
  ⟨second.2, SourceEqualityMkEdgeAllocation.emptyField (SourceEqualityMkEdgeAllocation.emptyField before.equality)⟩ memo := by
 exact .bind (.topRow _ _ _ _) (.topRow _ _ _ _)

-- Empty-field allocation derives a real successful field load while retaining both operation tables.
example (before : SourceEqualityConstraintMemoAllocation.State) (valid : SourceEqualityConstraintMemoAllocation.Valid before) :
 SourceCurrentConjunctionEquality.FieldAvailable (SourceEqualityMkEdgeAllocation.emptyField before) top ∧
 (SourceEqualityMkEdgeAllocation.emptyField before).combinations = before.combinations ∧
 (SourceEqualityMkEdgeAllocation.emptyField before).descents = before.descents :=
 ⟨(SourceCurrentConjunctionFieldAllocation.empty_field before valid).2.2, rfl, rfl⟩

-- Literal Top agrees with the older plain predicate.
example : SourceMemoGate.plain (top : Guard) = true ∧ (top : Guard) = SourceEqualityConstraintConstructors.top := by
 constructor
 · simp [SourceMemoGate.plain, SourceCompactGuards.sourceEqualities, SourceCompactGuards.positiveNormalized,
    SourceEqualityConstraintConstructors.top]
 · rfl

-- An empty conjunction is plain but differs from the literal noConstraint guard.
example : let other : Guard := ⟨some [], .and []⟩
 SourceMemoGate.plain other = true ∧ other ≠ (top : Guard) := by
 constructor
 · simp [SourceMemoGate.plain, SourceCompactGuards.sourceEqualities, SourceCompactGuards.positiveNormalized,
    SourceCompactGuards.positiveNormalizedList]
 · intro same
   have guards := congrArg SourceSymbolicIndex.Constraint.guard same
   cases guards
end MicroCFTA.AllocatedMergeGraphKernels
