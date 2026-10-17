import MicroCFTA.SourceCurrentRowPlanReplay
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
namespace MicroCFTA.RowPlanReplayKernels
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryGrowth
open InternedFreshOrdinaryPlanEquivalence
open SourceCurrentRowPlanReplay
open Language
private def firstInputs : List (Value Nat Bool) := [.reference .depth]
private def secondInputs : List (Value Nat Bool) := [.reference (.uninterned 0),.reference .depth]
private def firstChildren : List (Syntax Nat Bool) :=
  [.var 0,.binder false (.node [.mk 9 false [.var 1,.var 0]])]
private def secondChildren : List (Syntax Nat Bool) :=
  [.var 1,.binder false (.node [.mk 9 false [.var 2,.var 0]])]
private def firstRow : EdgeSyntax Nat Bool := .mk 7 false firstChildren
private def secondRow : EdgeSyntax Nat Bool := .mk 7 false secondChildren
private def originals : List (EdgeSyntax Nat Bool) := [firstRow,.mk 8 true [.node [.mk 10 true []]]]
private def built := buildEdges originals firstInputs (empty : State Nat Bool)
private def outputs : List (EdgeValue Nat Bool) := match built with | .done values _ => values | .pending .. => []
private def after := built.state
private def extra := run (makeEdge 99 true []) after
private def common := extra.2
private theorem actual : built = .done outputs after := by cbv
private theorem children_equivalent : ManyEquivalent firstChildren firstInputs secondChildren secondInputs := by
  simp [firstChildren,secondChildren,firstInputs,secondInputs,ManyEquivalent,Equivalent,EdgesEquivalent]
private theorem first_pair {relation : EdgeSyntax Nat Bool → EdgeValue Nat Bool → Prop}
    {row : EdgeSyntax Nat Bool} {rest : List (EdgeSyntax Nat Bool)} {values : List (EdgeValue Nat Bool)}
    (actual : All₂ relation (row::rest) values) : ∃ output later, values=output::later ∧ relation row output := by
  cases actual with
  | cons first rest => exact ⟨_,_,rfl,first⟩
private theorem captured_proof :
    buildEdges originals firstInputs empty = .done outputs after ∧ after.edges.next < common.edges.next ∧
      All₂ (fun plan output => rowRun plan firstInputs common = .done output common) originals outputs ∧
      ∃ output later, outputs = output::later ∧ rowRun secondRow secondInputs common = .done output common := by
  have retained := buildEdges_correct originals firstInputs empty (empty_valid (Symbol:=Nat) (Guard:=Bool))
  have validAfter : Valid after := retained.1
  have increase : Grows after common := (run_correct (makeEdge 99 true []) after validAfter).2
  have replay := SourceCurrentRowPlanReplay.rows originals firstInputs empty outputs after common empty_valid actual increase
  obtain ⟨output,later,shape,first⟩ := first_pair replay
  have changed : rowRun firstRow firstInputs common = rowRun secondRow secondInputs common :=
    SourceCurrentRowPlanReplay.equivalent 7 7 false false firstChildren secondChildren firstInputs secondInputs common
      rfl rfl children_equivalent
  exact ⟨actual,by cbv,replay,output,later,shape,changed.symm.trans first⟩
/-- Actual nested captured rows replay after allocation and agree with recoded lexical slots. -/
theorem captured :
    buildEdges originals firstInputs empty = .done outputs after ∧ after.edges.next < common.edges.next ∧
      All₂ (fun plan output => rowRun plan firstInputs common = .done output common) originals outputs ∧
      ∃ output later, outputs = output::later ∧ rowRun secondRow secondInputs common = .done output common := captured_proof
end MicroCFTA.RowPlanReplayKernels
#check @MicroCFTA.RowPlanReplayKernels.captured
#print MicroCFTA.RowPlanReplayKernels.captured
#print axioms MicroCFTA.RowPlanReplayKernels.captured
