import MicroCFTA.SourceCurrentStoredMuActiveChildLineage

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.MuActiveChildKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentStoredMuActiveChildLineage
open SourceCurrentOpenObservationSurvival (Related)

private def captureSource : Syntax Nat Bool := .binder true (.union [.node [.mk 3 true []],.node [.mk 4 false [.var 0]]])
private def captureBuilt := build captureSource [] empty
private def capture := match captureBuilt with | .done value _ => value | .pending .. => .empty
private def base := captureBuilt.state
private def inner : Syntax Nat Bool := .node [.mk 8 false [.var 0]]
private def rows : List (EdgeSyntax Nat Bool) :=
  [.mk 7 true [inner,.var 0,.var 1],.mk 7 true [inner,.var 0,.var 1],.mk 11 false [.var 2]]
private def captures : List (Value Nat Bool) := [capture,.empty]
private def first := build (.node rows) (.reference (.uninterned 0) :: captures) base
private def rawFirst := match first with | .done value _ => value | .pending .. => .empty
private def firstHeap := first.state
private def second := build (.node rows) (.reference (.uninterned 9) :: captures) firstHeap
private def rawSecond := match second with | .done value _ => value | .pending .. => .empty
private def common := second.state
private def firstEnvironment : Environment Nat Bool := fun name => if name = .uninterned 0 then some capture else none
private def secondEnvironment : Environment Nat Bool := fun name => if name = .uninterned 9 then some capture else none
private def isNode : Value Nat Bool → Bool | .node .. => true | _ => false
private def isMu : Value Nat Bool → Bool | .mu .. => true | _ => false

private theorem captureActual : captureBuilt = .done capture base := by cbv
private theorem firstActual : first = .done rawFirst firstHeap := by cbv
private theorem secondActual : second = .done rawSecond common := by cbv
private theorem baseReady : Ready base := SourceEqualityRequiredCache.constructed captureSource capture base captureActual

private theorem sourceReady (source : Syntax Nat Bool) (environment : List (Value Nat Bool))
    (before : State Nat Bool) (ready : Ready before)
    (available : InternedNestedProvenance.Values before environment)
    (value : Value Nat Bool) (after : State Nat Bool)
    (actual : build source environment before = .done value after) : Ready after := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic environment available
  refine ⟨?_,
    InternedFreshOrdinaryCoverage.build_covered source environment before
      ready.semantic.1.normal.facts.coherent.valid ready.covered value after actual,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source source environment before ready.semantic available
  · simpa only [actual,Outcome.state] using (InternedOpenDepthExecution.build_depth source environment before context ready.semantic.2 ready.depth).heap


private theorem captureAvailable : Available base capture :=
  (InternedFreshOrdinaryFacts.build_verified captureSource [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).result capture base captureActual

private theorem firstInputs : InternedNestedProvenance.Values base (.reference (.uninterned 0) :: captures) := by
  intro value member
  simp only [captures,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact InternedNestedProvenance.ordinary_available _ _
  · exact captureAvailable
  · exact InternedProbeProvenance.empty_available _
private theorem firstReady : Ready firstHeap := sourceReady (.node rows) _ base baseReady firstInputs rawFirst firstHeap firstActual
private theorem secondInputs : InternedNestedProvenance.Values firstHeap (.reference (.uninterned 9) :: captures) := by
  intro value member
  simp only [captures,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact InternedNestedProvenance.ordinary_available _ _
  · exact (InternedFreshOrdinaryFacts.build_verified (.node rows) _ base baseReady.semantic.1.normal.facts firstInputs).available
      capture captureAvailable
  · exact InternedProbeProvenance.empty_available _
private theorem commonReady : Ready common := sourceReady (.node rows) _ firstHeap firstReady secondInputs rawSecond common secondActual

private theorem innerAligned : Aligned inner := by
  apply ordinary [.mk 8 false [.var 0]]
  intro child selected
  obtain ⟨symbol,guard,originals,present,member,_⟩ := selected
  simp only [List.mem_singleton,EdgeSyntax.mk.injEq] at present
  obtain ⟨rfl,rfl,rfl⟩ := present
  have same := List.mem_singleton.mp member
  subst child
  exact reference 0

private theorem childrenAligned : ∀ child, StrictChild rows child → Aligned child := by
  intro child selected
  obtain ⟨symbol,guard,originals,present,member,_⟩ := selected
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false,EdgeSyntax.mk.injEq] at present
  rcases present with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact innerAligned
    · exact reference 0
    · exact reference 1
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact innerAligned
    · exact reference 0
    · exact reference 1
  · have same := List.mem_singleton.mp member
    subst child
    exact reference 2

/-- Actual active ordinary callbacks reconstruct related nonempty parents with a retained productive Mu capture. -/
theorem active_nested_ordinary :
    first = .done rawFirst firstHeap ∧ second = .done rawSecond common ∧
    rawFirst.referenceOf ≠ rawSecond.referenceOf ∧ isMu capture = true ∧
    ∃ left middle right reader,
      execute rawFirst firstEnvironment common = .done left middle ∧
      execute rawSecond secondEnvironment middle = .done right reader ∧
      execute rawFirst firstEnvironment reader = .done left reader ∧
      execute rawSecond secondEnvironment reader = .done right reader ∧
      Keeps common middle ∧ Keeps middle reader ∧ Available reader left ∧ Available reader right ∧
      Nonempty (SourceCurrentNativeMuPublication.History common middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle reader) ∧ Related left right ∧ isNode left = true := by
  have firstChecked := InternedFreshOrdinaryFacts.build_verified (.node rows) _ base baseReady.semantic.1.normal.facts firstInputs
  have secondChecked := InternedFreshOrdinaryFacts.build_verified (.node rows) _ firstHeap firstReady.semantic.1.normal.facts secondInputs
  have captured : Available common capture := secondChecked.available capture (firstChecked.available capture captureAvailable)
  have firstCommon : InternedNestedProvenance.Values common (.reference (.uninterned 0) :: captures) := by
    intro value member
    simp only [captures,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact InternedNestedProvenance.ordinary_available _ _
    · exact captured
    · exact InternedProbeProvenance.empty_available _
  have secondCommon : InternedNestedProvenance.Values common (.reference (.uninterned 9) :: captures) := by
    intro value member
    simp only [captures,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact InternedNestedProvenance.ordinary_available _ _
    · exact captured
    · exact InternedProbeProvenance.empty_available _
  have replacementFirst : Replacements common firstEnvironment := by
    intro name value found
    dsimp only [firstEnvironment] at found
    split at found
    · cases found; exact captured
    · cases found
  have replacementSecond : Replacements common secondEnvironment := by
    intro name value found
    dsimp only [secondEnvironment] at found
    split at found
    · cases found; exact captured
    · cases found
  have compatible : Compatible captures (.uninterned 0) (.uninterned 9) firstEnvironment secondEnvironment := by
    constructor
    · rfl
    · intro value member name present
      simp only [captures,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · have closed : capture.free = [] := by cbv
        rw [closed] at present
        cases present
      · cases present
  obtain ⟨left,middle,right,reader,done,other,replay,replayOther,firstKept,secondKept,leftAvailable,rightAvailable,
    firstHistory,secondHistory,related⟩ := node_complete rows childrenAligned captures (.uninterned 0) (.uninterned 9)
      firstEnvironment secondEnvironment compatible base firstHeap firstHeap common common
      (SourceRecursiveIntersectionSemanticHeap.context base baseReady.semantic _ firstInputs)
      (SourceRecursiveIntersectionSemanticHeap.context firstHeap firstReady.semantic _ secondInputs)
      rawFirst rawSecond firstActual secondActual secondChecked.growth (grows_refl _) commonReady firstCommon secondCommon
      replacementFirst replacementSecond
  have positive : isNode left = true := by
    have known : (match execute rawFirst firstEnvironment common with | .done value _ => isNode value | _ => false) = true := by cbv
    simpa only [done] using known
  exact ⟨firstActual,secondActual,by cbv; decide,by cbv,left,middle,right,reader,done,other,replay,replayOther,
    firstKept,secondKept,leftAvailable,rightAvailable,firstHistory,secondHistory,related,positive⟩

end MicroCFTA.MuActiveChildKernels

#check @MicroCFTA.MuActiveChildKernels.active_nested_ordinary
#print axioms MicroCFTA.MuActiveChildKernels.active_nested_ordinary
