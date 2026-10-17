import MicroCFTA.SourceCurrentRowPlanReplay
import MicroCFTA.InternedNodeSetCongruence
import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.InternedNestedSpecialization

/-!
# Node plans with reordered or repeated rows

Equivalent row plans can occur in different orders and multiplicities.
Actual completed rows replay at one common heap. Their complete row sets
then agree, including rows removed by physical empty-child normalization.
-/
namespace MicroCFTA.SourceCurrentNodePlanCongruence
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedFacts InternedNestedProvenance InternedNestedSpecialization
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryGrowth InternedFreshOrdinaryFacts
open InternedFreshOrdinaryPlanEquivalence
open SourceCurrentRowPlanReplay
open Language

/-- Row plans retain exact symbols, complete guards, and equivalent ordered child plans. -/
def RowEquivalent (first : EdgeSyntax Symbol Guard) (firstInputs : List (Value Symbol Guard))
    (second : EdgeSyntax Symbol Guard) (secondInputs : List (Value Symbol Guard)) : Prop :=
  match first, second with
  | .mk leftSymbol leftGuard left, .mk rightSymbol rightGuard right =>
      leftSymbol = rightSymbol ∧ leftGuard = rightGuard ∧ ManyEquivalent left firstInputs right secondInputs

/-- Every row occurrence has an equivalent row on the other side, without an ordering requirement. -/
def RowsEquivalent (first : List (EdgeSyntax Symbol Guard)) (firstInputs : List (Value Symbol Guard))
    (second : List (EdgeSyntax Symbol Guard)) (secondInputs : List (Value Symbol Guard)) : Prop :=
  (∀ row ∈ first, ∃ other ∈ second, RowEquivalent row firstInputs other secondInputs) ∧
    (∀ row ∈ second, ∃ other ∈ first, RowEquivalent other firstInputs row secondInputs)

private theorem left_member {A B : Type} {relation : A → B → Prop} {first : List A} {second : List B}
    (paired : All₂ relation first second) (value : A) (member : value ∈ first) :
    ∃ other ∈ second, relation value other := by
  induction paired with
  | nil => cases member
  | cons pair _ ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, pair⟩
      · obtain ⟨other, present, related⟩ := ih later
        exact ⟨other, List.mem_cons_of_mem _ present, related⟩

private theorem right_member {A B : Type} {relation : A → B → Prop} {first : List A} {second : List B}
    (paired : All₂ relation first second) (value : B) (member : value ∈ second) :
    ∃ other ∈ first, relation other value := by
  induction paired with
  | nil => cases member
  | cons pair _ ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, pair⟩
      · obtain ⟨other, present, related⟩ := ih later
        exact ⟨other, List.mem_cons_of_mem _ present, related⟩

/-- Equivalent rows execute identically at any common heap, including pending outcomes. -/
theorem row_exact [DecidableEq (EdgeKey Symbol Guard)] (first : EdgeSyntax Symbol Guard)
    (firstInputs : List (Value Symbol Guard)) (second : EdgeSyntax Symbol Guard)
    (secondInputs : List (Value Symbol Guard)) (common : State Symbol Guard)
    (same : RowEquivalent first firstInputs second secondInputs) :
    rowRun first firstInputs common = rowRun second secondInputs common := by
  cases first with
  | mk symbol guard children =>
      cases second with
      | mk otherSymbol otherGuard otherChildren =>
          obtain ⟨rfl, rfl, paired⟩ := same
          simp only [rowRun, buildMany_exact children firstInputs otherChildren secondInputs common paired]

/-- Actual row executions derive equal complete output sets after both histories reach a common heap. -/
theorem rows [DecidableEq (EdgeKey Symbol Guard)]
    (first second : List (EdgeSyntax Symbol Guard)) (firstInputs secondInputs : List (Value Symbol Guard))
    (before later after final common : State Symbol Guard) (left right : List (EdgeValue Symbol Guard))
    (same : RowsEquivalent first firstInputs second secondInputs)
    (leftValid : Valid before) (rightValid : Valid later)
    (leftDone : buildEdges first firstInputs before = .done left after)
    (rightDone : buildEdges second secondInputs later = .done right final)
    (leftGrowth : Grows after common) (rightGrowth : Grows final common) :
    ∀ row, row ∈ left ↔ row ∈ right := by
  have firstRows := SourceCurrentRowPlanReplay.rows first firstInputs before left after common leftValid leftDone leftGrowth
  have secondRows := SourceCurrentRowPlanReplay.rows second secondInputs later right final common rightValid rightDone rightGrowth
  intro row
  constructor
  · intro member
    obtain ⟨original, present, called⟩ := right_member firstRows row member
    obtain ⟨other, included, equivalent⟩ := same.1 original present
    obtain ⟨output, returned, actual⟩ := left_member secondRows other included
    have equal := called.symm.trans ((row_exact original firstInputs other secondInputs common equivalent).trans actual)
    have identity : row = output := by simpa only [Outcome.done.injEq, and_true] using equal
    simpa only [identity] using returned
  · intro member
    obtain ⟨original, present, called⟩ := right_member secondRows row member
    obtain ⟨other, included, equivalent⟩ := same.2 original present
    obtain ⟨output, returned, actual⟩ := left_member firstRows other included
    have equal := actual.symm.trans ((row_exact other firstInputs original secondInputs common equivalent).trans called)
    have identity : output = row := by simpa only [Outcome.done.injEq, and_true] using equal
    exact identity ▸ returned

/-- Reordering or repeating equivalent row plans preserves the exact completed canonical node value. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)]
    (first second : List (EdgeSyntax Symbol Guard)) (firstInputs secondInputs : List (Value Symbol Guard))
    (before later after final common : State Symbol Guard) (left right : Value Symbol Guard)
    (same : RowsEquivalent first firstInputs second secondInputs)
    (leftFacts : Facts before) (rightFacts : Facts later)
    (leftInputs : Values before firstInputs) (rightInputs : Values later secondInputs)
    (leftDone : build (.node first) firstInputs before = .done left after)
    (rightDone : build (.node second) secondInputs later = .done right final)
    (leftGrowth : Grows after common) (rightGrowth : Grows final common) (coherent : Coherent common) :
    left = right := by
  rw [build] at leftDone rightDone
  obtain ⟨leftRows, leftMiddle, leftRowsDone, leftMade⟩ := bind_done _ _ _ _ leftDone
  obtain ⟨rightRows, rightMiddle, rightRowsDone, rightMade⟩ := bind_done _ _ _ _ rightDone
  have leftChecked := InternedFreshOrdinaryFacts.buildEdges_verified first firstInputs before leftFacts leftInputs
  have rightChecked := InternedFreshOrdinaryFacts.buildEdges_verified second secondInputs later rightFacts rightInputs
  have leftMiddleFacts : Facts leftMiddle := by simpa only [leftRowsDone, Outcome.state] using leftChecked.facts
  have rightMiddleFacts : Facts rightMiddle := by simpa only [rightRowsDone, Outcome.state] using rightChecked.facts
  have leftResident := leftChecked.result leftRows leftMiddle leftRowsDone
  have rightResident := rightChecked.result rightRows rightMiddle rightRowsDone
  have leftRun : run (makeNode leftRows) leftMiddle = (left, after) := by
    cases result : run (makeNode leftRows) leftMiddle with
    | mk value state => simpa only [work, result, Outcome.done.injEq, Prod.mk.injEq] using leftMade
  have rightRun : run (makeNode rightRows) rightMiddle = (right, final) := by
    cases result : run (makeNode rightRows) rightMiddle with
    | mk value state => simpa only [work, result, Outcome.done.injEq, Prod.mk.injEq] using rightMade
  have leftPrefix : Grows leftMiddle after := by
    simpa only [leftRun] using (run_correct (makeNode leftRows) leftMiddle leftMiddleFacts.coherent.valid).2
  have rightPrefix : Grows rightMiddle final := by
    simpa only [rightRun] using (run_correct (makeNode rightRows) rightMiddle rightMiddleFacts.coherent.valid).2
  have leftCommon := grows_trans leftPrefix leftGrowth
  have rightCommon := grows_trans rightPrefix rightGrowth
  have members := rows first second firstInputs secondInputs before later leftMiddle rightMiddle common leftRows rightRows
    same leftFacts.coherent.valid rightFacts.coherent.valid leftRowsDone rightRowsDone leftCommon rightCommon
  have requestSame := InternedNodeSetCongruence.makeNode_same_members common coherent leftRows rightRows
    (fun edge member => edge_grows leftMiddle common leftCommon edge (leftResident edge member))
    (fun edge member => edge_grows rightMiddle common rightCommon edge (rightResident edge member))
    (by intro edge; simp only [surviving, List.mem_filter, members edge])
  have firstWarm := InternedConstructorTemplates.replay (makeNode leftRows) leftMiddle common
    leftMiddleFacts.coherent.valid (by simpa only [leftRun] using leftGrowth)
  have secondWarm := InternedConstructorTemplates.replay (makeNode rightRows) rightMiddle common
    rightMiddleFacts.coherent.valid (by simpa only [rightRun] using rightGrowth)
  rw [leftRun] at firstWarm
  rw [rightRun] at secondWarm
  exact congrArg Prod.fst (firstWarm.symm.trans ((congrArg (fun computation => run computation common) requestSame).trans secondWarm))

end MicroCFTA.SourceCurrentNodePlanCongruence
