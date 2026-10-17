import MicroCFTA.SourceCurrentStoredNodeExpansion
import MicroCFTA.SourceCurrentStoredCallsReplay
set_option linter.all true
namespace MicroCFTA.RowCallsDeterminismCheck
open InternedConstructorTemplates InternedStoredSubstitution SourceCurrentStoredNodeExpansion
example [DecidableEq (EdgeKey Symbol Guard)] (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (original firstOutput secondOutput : EdgeValue Symbol Guard)
    (valid : Valid common) (first : RowCalls environment common original firstOutput)
    (second : RowCalls environment common original secondOutput) : firstOutput = secondOutput := by
  have children := SourceCurrentStoredCallsReplay.same first.1 second.1 common valid valid (grows_refl _) (grows_refl _)
  have madeFirst := first.2.1
  rw [children] at madeFirst
  exact congrArg Prod.fst (madeFirst.symm.trans second.2.1)
end MicroCFTA.RowCallsDeterminismCheck
