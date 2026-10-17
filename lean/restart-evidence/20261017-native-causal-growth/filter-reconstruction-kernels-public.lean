import MicroCFTA.SourceCurrentStoredFilterReconstruction

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.FilterReconstructionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence InternedEdgeResidency
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentLiteralRootParts (SameParts Literal)
open SourceCurrentStoredFilterReconstruction (retained)

private def captures : List (Value Nat Bool) := [.reference (.uninterned 0)]
private def expression : Syntax Nat Bool :=
  .node [.mk 9 true [.var 0, .union [.var 0, .node [.mk 1 false []]]]]
private def built := build expression captures empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def bare : Value Nat Bool := .reference (.uninterned 0)
private def raw := ((children root)[1]?).getD .empty
private def leaf : Value Nat Bool :=
  match build (.node [.mk 1 false []]) [] empty with | .done value _ => value | .pending .. => .empty
private def environment : Environment Nat Bool :=
  fun name => if name = .uninterned 0 then some (.reference .depth) else none

private theorem actual : built = .done root heap := by cbv
private theorem inputs : Values (empty : State Nat Bool) captures := by
  intro value member
  cases List.mem_singleton.mp member
  exact InternedNestedProvenance.ordinary_available empty 0

private theorem ready : Ready heap := by
  have context := SourceRecursiveIntersectionSemanticHeap.context empty
    SourceRecursiveIntersectionSemanticHeap.empty_heap captures inputs
  refine ⟨SourceRecursiveIntersectionSemanticHeap.source expression captures empty
    SourceRecursiveIntersectionSemanticHeap.empty_heap inputs,
    InternedFreshOrdinaryCoverage.build_covered expression captures empty empty_valid
      InternedRecordCoherence.empty_correct.2 root heap actual, ?_⟩
  exact (InternedOpenDepthExecution.build_depth expression captures empty context
    InternedFreshOrdinaryDepthHeap.empty_heap InternedOpenDepthReadback.empty_heap).heap

private theorem available : Available heap bare ∧ Available heap raw := by
  have parent := (InternedFreshOrdinaryFacts.build_verified expression captures empty
    InternedNestedFacts.empty_facts inputs).result root heap actual
  exact ⟨parent.children bare (by cbv; exact .head _),
    parent.children raw (by cbv; exact .tail _ (.head _))⟩

private theorem replacements : Replacements heap environment := by
  intro name value found
  dsimp only [environment] at found
  split at found
  · cases found
    exact InternedNestedProvenance.depth_available heap
  · cases found

/-- One initial source supplies bare self and union self; both complete schedules retain their distinct root behavior. -/
theorem bare_and_union_self :
    build expression captures empty = .done root heap ∧ Ready heap ∧
    retained (.uninterned 0) bare = [bare] ∧ retained (.uninterned 0) raw = [leaf] ∧
    ∃ first middle outputs memberHeap folded final second after secondOutputs secondMember secondFold secondFinal,
      run (withoutSelfReference (.uninterned 0) bare) heap = (bare, heap) ∧
      execute bare environment heap = .done first middle ∧
      Calls environment [bare] middle outputs memberHeap ∧
      run (makeUnion outputs) memberHeap = (folded, final) ∧ Keeps heap final ∧
      SameParts first folded ∧ first = .reference .depth ∧
      run (withoutSelfReference (.uninterned 0) raw) final = (leaf, final) ∧
      execute leaf environment final = .done second after ∧
      Calls environment [leaf] after secondOutputs secondMember ∧
      run (makeUnion secondOutputs) secondMember = (secondFold, secondFinal) ∧
      Keeps final secondFinal ∧ SameParts second secondFold ∧ second = leaf ∧
      (nodeEdges second).length = 1 ∧ Literal first (.reference .depth) ∧
      ¬ Literal second (.reference .depth) := by
  have bareRetained : retained (.uninterned 0) bare = [bare] := rfl
  have unionRetained : retained (.uninterned 0) raw = [leaf] := by cbv
  obtain ⟨filtered,filterHeap,first,middle,outputs,memberHeap,folded,final,
    filteredActual,called,calls,joined,one,two,three,four,_,_,parts⟩ :=
    SourceCurrentStoredFilterReconstruction.complete (.uninterned 0) bare environment heap ready available.1 replacements
  have bareFilter : run (withoutSelfReference (.uninterned 0) bare) heap = (bare,heap) := rfl
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (bareFilter.symm.trans filteredActual)
  have firstSame : first = .reference .depth :=
    (Outcome.done.inj (called.symm.trans (show execute bare environment heap =
      .done (.reference .depth) heap by cbv))).1
  rw [bareRetained] at calls
  have firstKept := one.trans (two.trans (three.trans four))
  obtain ⟨filtered,filterHeap,second,after,secondOutputs,secondMember,secondFold,secondFinal,
    filteredActual,secondCalled,secondCalls,secondJoined,five,six,seven,eight,_,_,secondParts⟩ :=
    SourceCurrentStoredFilterReconstruction.complete (.uninterned 0) raw environment final firstKept.ready
      (firstKept.available raw available.2)
      (fun name value found => firstKept.available value (replacements name value found))
  have unionFilter : run (withoutSelfReference (.uninterned 0) raw) final = (leaf,final) := by cbv
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (unionFilter.symm.trans filteredActual)
  have secondSame : second = leaf :=
    (Outcome.done.inj (secondCalled.symm.trans
      (SourceCurrentStoredUnionObservations.closed leaf environment final (by cbv)))).1
  rw [unionRetained] at secondCalls
  refine ⟨actual,ready,bareRetained,unionRetained,first,middle,outputs,memberHeap,folded,final,
    second,after,secondOutputs,secondMember,secondFold,secondFinal,
    bareFilter,called,calls,joined,firstKept,parts,firstSame,unionFilter,secondCalled,secondCalls,secondJoined,
    five.trans (six.trans (seven.trans eight)),secondParts,secondSame,?_,?_,?_⟩
  · rw [secondSame]
    cbv
  · rw [firstSame]
    constructor
  · rw [secondSame]
    unfold leaf
    cbv
    intro impossible
    cases impossible

end MicroCFTA.FilterReconstructionKernels

#check @MicroCFTA.FilterReconstructionKernels.bare_and_union_self
#print axioms MicroCFTA.FilterReconstructionKernels.bare_and_union_self
