import MicroCFTA.SourceCurrentGeneratedRowSchedules
import MicroCFTA.SourceCurrentCausalGeneratedEmpty

/-!
# Causal alignment of actual source row fragments

Historical source rows retain their original shared index. Ordered actual
stored child calls supply both generated directions. Causal Empty agreement
then retains the exact child-empty test and row survival on both sides.
Neither whole ordinary source group needs a warm stored execution.
-/
namespace MicroCFTA.SourceCurrentCausalRowFragmentAlignment
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build buildEdges buildMany)
open InternedFreshOrdinaryLiveInputs (input)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference)
open InternedEdgeResidency (nodeEdges)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentRetainedMuDirectedCase (Generated Inputs)
open SourceCurrentUsedBinderAliasTransport (Aliases)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceCurrentStoredNodeExpansion (RowCalls)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentOpenObservations (RowMatch)
open SourceCurrentOpenPreorderSimulation (Mutual)
open SourceEqualityRequiredCache (Ready)

private theorem any_empty {first second : List (Value Symbol Guard)}
    (paired : All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second) :
    first.any (fun value => value.referenceOf == .empty) = second.any (fun value => value.referenceOf == .empty) := by
  induction paired with
  | nil => rfl
  | cons head tail ih => simp only [List.any_cons,head,ih]

/-- Actual indexed row calls match in full and have the same physical survival test at the original reader. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard) (reader before after later final : State Symbol Guard)
    (ready : Ready reader) (history : History empty reader)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (aliases : Aliases (.node expressions) inputs firstNames secondNames)
    (paired : Inputs reader first second (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader first) (secondReplacements : Replacements reader second)
    (rawFirst rawSecond : Value Symbol Guard)
    (firstBuild : build (.node expressions) (inputs.map (input firstNames)) before = .done rawFirst after)
    (secondBuild : build (.node expressions) (inputs.map (input secondNames)) later = .done rawSecond final)
    (firstGrowth : Grows after reader) (secondGrowth : Grows final reader)
    (firstAvailable : Available reader rawFirst) (secondAvailable : Available reader rawSecond)
    (row firstOutput : EdgeValue Symbol Guard) (selected : row ∈ nodeEdges rawFirst)
    (firstCalls : RowCalls first reader row firstOutput)
    (oppositeCalls : ∀ original ∈ nodeEdges rawSecond, ∃ output, RowCalls second reader original output) :
    ∃ firstRows firstAfter secondRows secondAfter index symbol guard children,
      ∃ (firstRow : RowCall expressions (inputs.map (input firstNames)) before firstRows firstAfter reader index symbol guard children)
        (secondRow : RowCall expressions (inputs.map (input secondNames)) later secondRows secondAfter reader index symbol guard children),
      buildEdges expressions (inputs.map (input firstNames)) before = .done firstRows firstAfter ∧
      run (makeNode firstRows) firstAfter = (rawFirst,after) ∧
      buildEdges expressions (inputs.map (input secondNames)) later = .done secondRows secondAfter ∧
      run (makeNode secondRows) secondAfter = (rawSecond,final) ∧
      firstRow.output = row ∧ secondRow.output ∈ nodeEdges rawSecond ∧
      buildMany children (inputs.map (input firstNames)) reader = .done firstRow.values reader ∧
      buildMany children (inputs.map (input secondNames)) reader = .done secondRow.values reader ∧
      ∃ secondOutput,
        RowCalls second reader secondRow.output secondOutput ∧
        RowMatch (Mutual (Generated reader)) firstOutput secondOutput ∧
        firstOutput.children.any (fun child => child.referenceOf == .empty) =
          secondOutput.children.any (fun child => child.referenceOf == .empty) ∧
        ((!(firstOutput.children.any (fun child => child.referenceOf == .empty))) = true ↔
          (!(secondOutput.children.any (fun child => child.referenceOf == .empty))) = true) := by
  obtain ⟨firstRows,firstAfter,secondRows,secondAfter,index,symbol,guard,children,firstRow,secondRow,
    firstRowsDone,firstMade,secondRowsDone,secondMade,selectedRow,secondMember,firstChildrenWarm,secondChildrenWarm,
    secondOutput,secondCalls,symbolSame,guardSame,generated⟩ :=
    SourceCurrentGeneratedRowSchedules.node expressions inputs firstNames secondNames first second
      reader before after later final ready firstContext secondContext aliases paired firstReplacements secondReplacements
      rawFirst rawSecond firstBuild secondBuild firstGrowth secondGrowth firstAvailable secondAvailable
      row firstOutput selected firstCalls oppositeCalls
  have childrenEmpty := All₂.imp
    (fun _ _ pair => SourceCurrentCausalGeneratedEmpty.generated reader history pair.1) generated
  have same := any_empty childrenEmpty
  exact ⟨firstRows,firstAfter,secondRows,secondAfter,index,symbol,guard,children,firstRow,secondRow,
    firstRowsDone,firstMade,secondRowsDone,secondMade,selectedRow,secondMember,firstChildrenWarm,secondChildrenWarm,
    secondOutput,secondCalls,⟨symbolSame,guardSame,generated⟩,same,by rw [same]⟩

end MicroCFTA.SourceCurrentCausalRowFragmentAlignment
