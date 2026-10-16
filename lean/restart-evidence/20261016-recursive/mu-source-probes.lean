import MicroCFTA.SourceCurrentAllocatedNativeMuSource

#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuSource.enter_prefix
#check @MicroCFTA.SourceCurrentAllocatedNativeMuSource.enter_prefix
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuSource.original_body
#check @MicroCFTA.SourceCurrentAllocatedNativeMuSource.original_body
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuSource.unfolded_valid
#check @MicroCFTA.SourceCurrentAllocatedNativeMuSource.unfolded_valid
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuSource.mu_source_law
#check @MicroCFTA.SourceCurrentAllocatedNativeMuSource.mu_source_law

namespace MicroCFTA.SourceCurrentAllocatedNativeMuSource.Probes
noncomputable section
open InternedConstructorTemplates SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local instance : DecidableEq (EdgeKey Symbol Guard) := Classical.typeDecidableEq _

def request : NodeRequest Symbol Guard :=
  ⟨IntersectionEmptyDomain.emptyDomain, .reference (.interned 4), .reference (.interned 2)⟩

example (before : SourceEqualityNativeDemand.State width) :
    let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
      request.left request.right 4 2
    SourceEqualityNativeDemand.step
      (.code (SourceRecursiveIntersectionCode.compileMu request.domain request.left request.right)) before =
      .yielded (.code (.node ⟨entered.1, request.left, request.right⟩
        (fun value => .optionalBinder (2, 4) value .pure)))
        {before with native := advance before.native {before.native.machine with domains := entered.2}} := by
  exact enter_prefix request before 4 2 rfl rfl

example : SourceRecursiveIntersectionInputView.Original
    (SourceRecursiveIntersectionKernel.body (.reference (.interned 4) : Value Symbol Guard)) :=
  original_body _ (.reference 4)

example : SourceRecursiveIntersectionInputView.Original
    (SourceRecursiveIntersectionKernel.body (.empty : Value Symbol Guard)) := original_body _ .empty

example : SourceRecursiveIntersectionControl.pair 4 2 = IntersectSchedule.pair (.ref 4) (.ref 2) := rfl

end
end MicroCFTA.SourceCurrentAllocatedNativeMuSource.Probes
