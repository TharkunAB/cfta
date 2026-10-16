import MicroCFTA.SourceCurrentAllocatedNativePairAdmission
import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

open MicroCFTA Cache Language IntersectSchedule InternedConstructorTemplates
open InternedProbeProvenance InternedNestedProvenance SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativePairAdmission SourceCurrentAllocatedNativeContextRebase

#print axioms name_covered
#print axioms identity_input
#print axioms physical_name_covered
#print axioms pair_covered
#print axioms empty_seen
#print axioms restrict_seen
#print axioms extend_seen
#print axioms bindings_covered
#print axioms entered_seen
#print axioms entered_names
#print axioms request_entered_seen
#print axioms request_entered_names
#check @name_covered
#check @identity_input
#check @physical_name_covered
#check @pair_covered
#check @empty_seen
#check @restrict_seen
#check @extend_seen
#check @bindings_covered
#check @entered_seen
#check @entered_names
#check @request_entered_seen
#check @request_entered_names

private def leaf (symbol : Nat) : InternedNestedConstruction.Syntax Nat Bool := .node [⟨symbol, true, []⟩]
private def first := InternedFreshOrdinaryConstruction.build (.binder false (leaf 0)) [] empty
private def middle : State Nat Bool := first.state
private def left : Value Nat Bool := match first with
  | .done value _ => value
  | .pending _ _ => .empty
private theorem first_done : first = .done left middle := by cbv
private theorem first_verified : InternedNestedFacts.Verified empty first Available :=
  InternedFreshOrdinaryFacts.closed_verified (.binder false (leaf 0))
private theorem middleFacts : InternedNestedFacts.Facts middle := first_verified.facts
private theorem leftAvailable : Available middle left := first_verified.result _ _ first_done
private theorem leftClosed : left.free = [] := by cbv
private def second := InternedFreshOrdinaryConstruction.build (leaf 1) [] middle
private def source : State Nat Bool := second.state
private def right : Value Nat Bool := match second with
  | .done value _ => value
  | .pending _ _ => .empty
private theorem second_done : second = .done right source := by cbv
private theorem second_verified : InternedNestedFacts.Verified middle second Available :=
  InternedFreshOrdinaryFacts.build_verified (leaf 1) [] middle middleFacts (by intro value member; cases member)
private theorem sourceFacts : InternedNestedFacts.Facts source := second_verified.facts
private theorem rightAvailable : Available source right := second_verified.result _ _ second_done
private theorem rightClosed : right.free = [] := by cbv
private def roots := [left, right]
private def holds (_ : Bool) (_ : Term Nat) := true
private theorem available : Values source roots := by
  intro root member
  simp only [roots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact leftAvailable.grows middle source second_verified.growth second_verified.history
  · exact rightAvailable
private theorem closed : ∀ root ∈ roots, root.free = [] := by
  intro root member
  simp only [roots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact leftClosed
  · exact rightClosed
private theorem originals : ∀ root ∈ roots, Original root := fun root member =>
  SourceRecursiveIntersectionOriginalOutput.closed_original root source sourceFacts.coherent
    (available root member) (closed root member)
private def inputs := SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
  source sourceFacts holds roots originals available closed
private theorem leftValid : inputs.valid (inputOf left) :=
  SourceCurrentAllocatedNativeInputInventoryModels.root_valid source sourceFacts holds roots originals available closed
    left List.mem_cons_self
private theorem rightValid : inputs.valid (inputOf right) :=
  SourceCurrentAllocatedNativeInputInventoryModels.root_valid source sourceFacts holds roots originals available closed
    right (List.mem_cons_of_mem _ List.mem_cons_self)
private def firstId := (SourceRecursiveIntersectionControl.identity left).getD 0
private def secondId := (SourceRecursiveIntersectionControl.identity right).getD 0
private theorem leftIdentity : SourceRecursiveIntersectionControl.identity left = some firstId := by cbv
private theorem rightIdentity : SourceRecursiveIntersectionControl.identity right = some secondId := by cbv
private def earlier := SourceRecursiveIntersectionEnvironment.enter Cache.emptyState IntersectionEmptyDomain.emptyKey
  left left firstId firstId
private theorem earlierValid : Cache.Valid earlier.2 :=
  (IntersectionEmptyDomain.make_correct Cache.emptyState Cache.empty_valid _).1
private theorem earlierSeen : SeenCovered inputs earlier.1.key :=
  entered_seen inputs Cache.emptyState Cache.empty_valid IntersectionEmptyDomain.emptyKey left left
    (empty_seen inputs) leftValid leftValid firstId firstId leftIdentity leftIdentity
private def later := SourceRecursiveIntersectionEnvironment.enter earlier.2 earlier.1.key left right firstId secondId
private theorem laterSeen : SeenCovered inputs later.1.key :=
  entered_seen inputs earlier.2 earlierValid earlier.1.key left right earlierSeen
    leftValid rightValid firstId secondId leftIdentity rightIdentity

example : SeenCovered inputs IntersectionEmptyDomain.emptyDomain.key := empty_seen inputs
example : inputOf left = .mu 1 ∧ firstId = 1 ∧ secondId = 2 := by refine ⟨?_, ?_, ?_⟩ <;> cbv
example : NameCovered inputs firstId := physical_name_covered inputs left leftValid firstId leftIdentity
example : NameCovered inputs secondId := physical_name_covered inputs right rightValid secondId rightIdentity
example : NameCovered inputs (SourceRecursiveIntersectionControl.pair secondId firstId).1 ∧
    NameCovered inputs (SourceRecursiveIntersectionControl.pair secondId firstId).2 :=
  pair_covered inputs secondId firstId
    (physical_name_covered inputs right rightValid secondId rightIdentity)
    (physical_name_covered inputs left leftValid firstId leftIdentity)
example : SeenCovered inputs earlier.1.key := earlierSeen
example : SeenCovered inputs later.1.key := laterSeen
example : SourceRecursiveIntersectionControl.pair firstId firstId ∈ later.1.key.seen := by
  change SourceRecursiveIntersectionControl.pair firstId firstId ∈
    (SourceRecursiveIntersectionEnvironment.enter earlier.2 earlier.1.key left right firstId secondId).1.key.seen
  rw [SourceRecursiveIntersectionSchedule.entered_key earlier.2 earlierValid earlier.1.key left right firstId secondId]
  apply (SourceRecursiveIntersectionDomain.extend_seen _ _ _ _).mpr
  right
  change SourceRecursiveIntersectionControl.pair firstId firstId ∈
    (SourceRecursiveIntersectionEnvironment.enter Cache.emptyState IntersectionEmptyDomain.emptyKey left left firstId firstId).1.key.seen
  rw [SourceRecursiveIntersectionSchedule.entered_key Cache.emptyState Cache.empty_valid
    IntersectionEmptyDomain.emptyKey left left firstId firstId]
  exact SourceRecursiveIntersectionEnvironment.enter_seen _ left left firstId firstId
example : ∀ name ∈ (SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst,
    NameCovered inputs name := bindings_covered inputs left right leftValid rightValid
example : ∀ name ∈ SourceRecursiveIntersectionDomain.names earlier.1.key, NameCovered inputs name :=
  entered_names inputs Cache.emptyState Cache.empty_valid IntersectionEmptyDomain.emptyKey left left
    (by intro name member; cases member) leftValid leftValid firstId firstId
example : earlier.2.next = 1 ∧ later.2.next = 2 := by constructor <;> cbv
example : SourceRecursiveIntersectionEnvironment.enter later.2 earlier.1.key left right firstId secondId = later := by cbv
