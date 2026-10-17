import MicroCFTA.SourceCurrentStoredLiteralCongruence
import MicroCFTA.SourceCurrentLiteralPartsObservations

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

namespace MicroCFTA.StoredLiteralKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference NodeKey)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Ready Keeps)

private def captures : List (Value Nat Bool) := [.reference (.uninterned 0)]
private def nodeA : Syntax Nat Bool := .node [.mk 1 false [.var 0,.var 0]]
private def nodeB : Syntax Nat Bool := .node [.mk 2 true [.var 0]]
private def recursive : Syntax Nat Bool := .binder false (.union [.node [.mk 3 true []],.node [.mk 4 false [.var 0]]])
private def expression : Syntax Nat Bool := .node [.mk 9 true [
  .union [.var 0,nodeA,nodeB], .union [.union [nodeA,nodeB],.var 0], recursive]]
private def built := build expression captures empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def first : Value Nat Bool := ((children root)[0]?).getD .empty
private def second : Value Nat Bool := ((children root)[1]?).getD .empty
private def fields : Value Nat Bool → Interned NodeKey × List (Value Nat Bool) × Nat × List Reference
  | .union entry rows level free => (entry,rows,level,free)
  | _ => (⟨0,.union []⟩,[],0,[])
private theorem actual : built = .done root heap := by cbv
private theorem inputs : Values (empty : State Nat Bool) captures := by
  intro value member
  have same : value = .reference (.uninterned 0) := List.mem_singleton.mp member
  cases same
  exact InternedNestedProvenance.ordinary_available empty 0
private theorem ready : Ready heap := by
  have context := SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap captures inputs
  refine ⟨SourceRecursiveIntersectionSemanticHeap.source expression captures empty
    SourceRecursiveIntersectionSemanticHeap.empty_heap inputs,
    InternedFreshOrdinaryCoverage.build_covered expression captures empty empty_valid
      InternedRecordCoherence.empty_correct.2 root heap actual,?_⟩
  exact (InternedOpenDepthExecution.build_depth expression captures empty context
    InternedFreshOrdinaryDepthHeap.empty_heap InternedOpenDepthReadback.empty_heap).heap
private theorem available : Available heap first ∧ Available heap second := by
  have result := (InternedFreshOrdinaryFacts.build_verified expression captures empty InternedNestedFacts.empty_facts inputs).result root heap actual
  exact ⟨result.children first (by cbv; exact .head _), result.children second (by cbv; exact .tail _ (.head _))⟩
private def bare : Value Nat Bool := .reference (.uninterned 0)
private def a : Value Nat Bool := ((fields first).2.1)[1]?.getD .empty
private def b : Value Nat Bool := ((fields first).2.1)[2]?.getD .empty
private def ab : Value Nat Bool := ((fields second).2.1)[0]?.getD .empty
private theorem aAvailable : Available heap a :=
  available.1.children a (List.mem_of_getElem? (show (children first)[1]? = some a by cbv))
private theorem bAvailable : Available heap b :=
  available.1.children b (List.mem_of_getElem? (show (children first)[2]? = some b by cbv))
private theorem abAvailable : Available heap ab :=
  available.2.children ab (List.mem_of_getElem? (show (children second)[0]? = some ab by cbv))
private theorem bareAvailable : Available heap bare := InternedNestedProvenance.ordinary_available heap 0
private theorem firstInputs : Values heap [bare,a,b] := by
  intro value member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact bareAvailable
  · exact aAvailable
  · exact bAvailable
private theorem secondInputs : Values heap [ab,bare] := by
  intro value member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact abAvailable
  · exact bareAvailable
private theorem groupedInputs : Values heap [a,b] := by
  intro value member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact aAvailable
  · exact bAvailable
private theorem firstWarm : run (makeUnion [bare,a,b]) heap = (first,heap) := by cbv
private theorem secondWarm : run (makeUnion [ab,bare]) heap = (second,heap) := by cbv
private theorem groupedWarm : run (makeUnion [a,b]) heap = (ab,heap) := by cbv
private theorem parts : SourceCurrentLiteralRootParts.SameParts first second := by
  constructor
  · intro atom
    have firstParts := SourceCurrentLiteralUnionParts.literal heap ready.semantic.1.normal.facts [bare,a,b] firstInputs atom
    have secondParts := SourceCurrentLiteralUnionParts.literal heap ready.semantic.1.normal.facts [ab,bare] secondInputs atom
    have grouped := SourceCurrentLiteralUnionParts.literal heap ready.semantic.1.normal.facts [a,b] groupedInputs atom
    rw [firstWarm] at firstParts
    rw [secondWarm] at secondParts
    rw [groupedWarm] at grouped
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_and_right,exists_or,exists_eq_left] at firstParts secondParts grouped
    exact firstParts.trans (or_comm.trans ((or_congr grouped Iff.rfl).symm.trans secondParts.symm))
  · intro row
    have firstParts := SourceCurrentLiteralUnionParts.row heap ready.semantic.1.normal.facts ready.semantic.1.normal.live [bare,a,b] firstInputs row
    have secondParts := SourceCurrentLiteralUnionParts.row heap ready.semantic.1.normal.facts ready.semantic.1.normal.live [ab,bare] secondInputs row
    have grouped := SourceCurrentLiteralUnionParts.row heap ready.semantic.1.normal.facts ready.semantic.1.normal.live [a,b] groupedInputs row
    rw [firstWarm] at firstParts
    rw [secondWarm] at secondParts
    rw [groupedWarm] at grouped
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_and_right,exists_or,exists_eq_left] at firstParts secondParts grouped
    exact firstParts.trans (or_comm.trans ((or_congr grouped Iff.rfl).symm.trans secondParts.symm))

private def replacement : Value Nat Bool := (children root)[2]?.getD .empty
private def environment : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = .uninterned 0 then some replacement else none
private def value : Outcome Nat Bool (Value Nat Bool) → Value Nat Bool
  | .done result _ => result
  | .pending .. => .empty
private def isMu : Value Nat Bool → Bool | .mu .. => true | _ => false
private def isUnion : Value Nat Bool → Bool | .union .. => true | _ => false
private theorem replacementAvailable : Available heap replacement := by
  have result := (InternedFreshOrdinaryFacts.build_verified expression captures empty InternedNestedFacts.empty_facts inputs).result root heap actual
  exact result.children replacement (List.mem_of_getElem? (show (children root)[2]? = some replacement by cbv))
private theorem replacements : InternedStoredSubstitution.Replacements heap environment := by
  intro name output found
  dsimp only [environment] at found
  split at found
  · cases found; exact replacementAvailable
  · cases found

/-- Source-built unequal roots reconstruct with a recursive replacement and preserve exact parts. -/
private theorem initial_receipt :
    build expression captures empty = .done root heap ∧ Ready heap ∧ first ≠ second ∧
    SourceCurrentLiteralRootParts.SameParts first second ∧ isMu replacement = true ∧
    (∀ depth view, SourceCurrentOpenObservations.Same depth view [first] [second]) ∧
    ∃ left middle right after,
      execute first environment heap = .done left middle ∧ execute second environment middle = .done right after ∧
      execute first environment after = .done left after ∧ execute second environment after = .done right after ∧
      Keeps heap middle ∧ Keeps middle after ∧ Available after left ∧ Available after right ∧
      Nonempty (SourceCurrentNativeMuPublication.History heap middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle after) ∧
      SourceCurrentLiteralRootParts.SameParts left right ∧ SourceCurrentOpenObservationSurvival.Related left right ∧
      isUnion left = true ∧ isUnion right = true ∧ left ≠ right := by
  have unequal : first ≠ second := by
    intro same
    have identity := congrArg Value.referenceOf same
    cbv at identity
    cases identity
  have observed := SourceCurrentLiteralPartsObservations.same heap heap ready.semantic.1.normal ready.semantic.1.normal
    first second available.1 available.2 parts
  obtain ⟨left,middle,right,after,firstDone,secondDone,firstWarm,secondWarm,firstKept,secondKept,
    leftAvailable,rightAvailable,firstHistory,secondHistory,resultParts,related⟩ :=
    SourceCurrentStoredLiteralCongruence.initial first second environment heap ready available.1 available.2 replacements parts
  have knownFirst : execute first environment heap =
      .done (value (execute first environment heap)) (execute first environment heap).state := by cbv
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (firstDone.symm.trans knownFirst)
  have knownSecond : execute second environment (execute first environment heap).state =
      .done (value (execute second environment (execute first environment heap).state))
        (execute second environment (execute first environment heap).state).state := by cbv
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (secondDone.symm.trans knownSecond)
  refine ⟨actual,ready,unequal,parts,by cbv,observed,_,_,_,_,firstDone,secondDone,firstWarm,secondWarm,
    firstKept,secondKept,leftAvailable,rightAvailable,firstHistory,secondHistory,resultParts,related,by cbv,by cbv,?_⟩
  intro same
  have identity := congrArg Value.referenceOf same
  cbv at identity
  cases identity

/-- The public integration retains the exact checked initial receipt. -/
theorem unequal_recursive_reconstruction :
    build expression captures empty = .done root heap ∧ Ready heap ∧ first ≠ second ∧
    SourceCurrentLiteralRootParts.SameParts first second ∧ isMu replacement = true ∧
    (∀ depth view, SourceCurrentOpenObservations.Same depth view [first] [second]) ∧
    ∃ left middle right after,
      execute first environment heap = .done left middle ∧ execute second environment middle = .done right after ∧
      execute first environment after = .done left after ∧ execute second environment after = .done right after ∧
      Keeps heap middle ∧ Keeps middle after ∧ Available after left ∧ Available after right ∧
      Nonempty (SourceCurrentNativeMuPublication.History heap middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle after) ∧
      SourceCurrentLiteralRootParts.SameParts left right ∧ SourceCurrentOpenObservationSurvival.Related left right ∧
      isUnion left = true ∧ isUnion right = true ∧ left ≠ right := initial_receipt

end MicroCFTA.StoredLiteralKernels

#check @MicroCFTA.StoredLiteralKernels.unequal_recursive_reconstruction
#print MicroCFTA.StoredLiteralKernels.unequal_recursive_reconstruction
#print axioms MicroCFTA.StoredLiteralKernels.unequal_recursive_reconstruction
