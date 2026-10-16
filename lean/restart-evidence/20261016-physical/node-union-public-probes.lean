import MicroCFTA.SourceCurrentAllocatedNativeNodeBranches
import MicroCFTA.SourceCurrentAllocatedNativeUnionMeaning

namespace MicroCFTA.CurrentPhysicalMeaningProbes
open Language InternedConstructorTemplates SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativeContextCache SourceRecursiveIntersectionCode SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

#print axioms SourceCurrentAllocatedNativeNodeBranches.original_closed_language
#check SourceCurrentAllocatedNativeNodeBranches.original_closed_language
#print axioms SourceCurrentAllocatedNativeNodeBranches.original_closed_rank
#check SourceCurrentAllocatedNativeNodeBranches.original_closed_rank
#print axioms SourceCurrentAllocatedNativeNodeBranches.empty_law
#check SourceCurrentAllocatedNativeNodeBranches.empty_law
#print axioms SourceCurrentAllocatedNativeNodeBranches.swap_law
#check SourceCurrentAllocatedNativeNodeBranches.swap_law
#print axioms SourceCurrentAllocatedNativeNodeBranches.reset_law
#check SourceCurrentAllocatedNativeNodeBranches.reset_law
#print axioms SourceCurrentAllocatedNativeNodeBranches.repeated_law
#check SourceCurrentAllocatedNativeNodeBranches.repeated_law
#print axioms SourceCurrentAllocatedNativeNodeBranches.union_members
#check SourceCurrentAllocatedNativeNodeBranches.union_members
#print axioms SourceCurrentAllocatedNativeNodeBranches.left_union_law
#check SourceCurrentAllocatedNativeNodeBranches.left_union_law
#print axioms SourceCurrentAllocatedNativeNodeBranches.right_union_law
#check SourceCurrentAllocatedNativeNodeBranches.right_union_law
#print axioms SourceCurrentAllocatedNativeNodeBranches.self_law
#check SourceCurrentAllocatedNativeNodeBranches.self_law
#print axioms SourceCurrentAllocatedNativeUnionMeaning.union_body
#check SourceCurrentAllocatedNativeUnionMeaning.union_body

example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey) (right : Value Symbol Guard) :
    NodeLaw view model ranked holds ⟨domain, .empty, right⟩ .empty :=
  SourceCurrentAllocatedNativeNodeBranches.empty_law view model ranked holds _ (Or.inl rfl)

example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey) (left : Value Symbol Guard) :
    NodeLaw view model ranked holds ⟨domain, left, .empty⟩ .empty :=
  SourceCurrentAllocatedNativeNodeBranches.empty_law view model ranked holds _ (Or.inr rfl)

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey) (right : Value Symbol Guard)
    (before : SourceEqualityNativeDemand.State width) :
    execute 1 (.code (compileNode ⟨domain, .empty, right⟩)) before = .done .empty before := by
  simp [execute, step, compileNode, SourceRecursiveIntersectionControl.decision,
    SourceRecursiveIntersectionControl.hasEmpty, Value.referenceOf,
    SourceRecursiveIntersectionNative.step, lift]

example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (law : NodeLaw view model ranked holds request value) :
    NodeLaw view model ranked holds request value := by
  have reversed := SourceCurrentAllocatedNativeNodeBranches.swap_law view model ranked holds
    ⟨request.domain, request.right, request.left⟩ value law
  exact SourceCurrentAllocatedNativeNodeBranches.swap_law view model ranked holds request value reversed

end MicroCFTA.CurrentPhysicalMeaningProbes
