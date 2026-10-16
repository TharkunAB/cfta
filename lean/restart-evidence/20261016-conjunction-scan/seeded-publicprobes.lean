import MicroCFTA.SourceCurrentAllocatedSeededQuery

#print axioms MicroCFTA.SourceCurrentAllocatedSeededQuery.Operand.unique
#print axioms MicroCFTA.SourceCurrentAllocatedSeededQuery.Fold.unique
#print axioms MicroCFTA.SourceCurrentAllocatedSeededQuery.Seeded.unique
#print axioms MicroCFTA.SourceCurrentAllocatedSeededQuery.operand_complete
#print axioms MicroCFTA.SourceCurrentAllocatedSeededQuery.fold_complete
#print axioms MicroCFTA.SourceCurrentAllocatedSeededQuery.seeded_complete
#print axioms MicroCFTA.SourceCurrentAllocatedSeededQuery.Seeded.effects
#print axioms MicroCFTA.SourceCurrentAllocatedSeededQuery.false_class_complete
#check MicroCFTA.SourceCurrentAllocatedSeededQuery.Operand.unique
#check MicroCFTA.SourceCurrentAllocatedSeededQuery.Fold.unique
#check MicroCFTA.SourceCurrentAllocatedSeededQuery.Seeded.unique
#check MicroCFTA.SourceCurrentAllocatedSeededQuery.operand_complete
#check MicroCFTA.SourceCurrentAllocatedSeededQuery.fold_complete
#check MicroCFTA.SourceCurrentAllocatedSeededQuery.seeded_complete
#check MicroCFTA.SourceCurrentAllocatedSeededQuery.Seeded.effects
#check MicroCFTA.SourceCurrentAllocatedSeededQuery.false_class_complete

namespace MicroCFTA.SourceCurrentAllocatedSeededQueryProbes
open InternedConstructorTemplates
open SourceCurrentAllocatedSeededQuery
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceRecursiveIntersectionCode SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width fuel : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {values : List (Value Symbol Guard)} {path first second third : List Int}
variable {before middle later after : Checked width} {value tail result : Value Symbol Guard}

-- Empty input retains the literal empty result and complete checked state.
example : Seeded values [] before .empty before := .nil before

-- Empty input needs no reached native word check.
example : SeededRanges values [] before := trivial

-- A singleton performs its actual projection without a native request.
example (operand : Operand path values before value after) : Seeded values [path] before value after :=
  .nonempty (.one operand)

-- A singleton range plan contains no native request premise.
example : SeededRanges values [path] before := FoldRanges.one

-- The second source operand is projected before the first seed.
example (head : Operand second values before value middle)
    (seed : Operand first values middle tail later)
    (native : Trace fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain value tail)) later
      (.code (.pure result)) after) : Seeded values [first, second] before result after :=
  .nonempty (.cons head (.one seed) native)

-- Three source operands rotate to second, third, then first.
example (fold : Fold values [second, third, first] before result after) :
    Seeded values [first, second, third] before result after := .nonempty fold

-- Every actual projection retains both native tables and the domain cache.
example (heap : State Symbol Guard)
    (projection : SourceEqualityProjectionGraph.Forest path values before.native.machine.heap result heap) :
    Operand path values before result (advancePhysical before ⟨heap, before.operations⟩) ∧
      (advancePhysical before ⟨heap, before.operations⟩).native.nodes = before.native.nodes ∧
      (advancePhysical before ⟨heap, before.operations⟩).native.edges = before.native.edges ∧
      (advancePhysical before ⟨heap, before.operations⟩).native.machine.domains = before.native.machine.domains :=
  ⟨.force result heap projection, SourceCurrentAllocatedQueryMemo.advance_tables before _⟩

-- Projection keeps the actual equality-operation state.
example (heap : State Symbol Guard) :
    (advancePhysical before ⟨heap, before.operations⟩).operations = before.operations := rfl

-- Successful projection bounds identify the complete returned state.
example (left : Operand path values before value middle) (right : Operand path values before tail after) :
    value = tail ∧ middle = after := left.unique right

-- Successful seeded bounds identify the complete returned state.
example {paths : List (List Int)} (left : Seeded values paths before value middle)
    (right : Seeded values paths before tail after) : value = tail ∧ middle = after := left.unique right
end MicroCFTA.SourceCurrentAllocatedSeededQueryProbes
