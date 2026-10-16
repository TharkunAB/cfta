import MicroCFTA.SourceCurrentAllocatedNativeGrownInventory
import MicroCFTA.InternedFreshOrdinaryFacts

open MicroCFTA Cache Language IntersectSchedule InternedConstructorTemplates
open InternedProbeProvenance InternedNestedProvenance
open SourceRecursiveIntersectionInputView SourceCurrentAllocatedNativeGrownInventory

#print axioms closed_originals
#print axioms reachable_grows
#print axioms valid_grows
#print axioms rank_exact
#print axioms language_exact
#print axioms name_rank_exact
#print axioms name_language_exact
#print axioms target_root_valid
#check @closed_originals
#check @reachable_grows
#check @valid_grows
#check @rank_exact
#check @language_exact
#check @name_rank_exact
#check @name_language_exact
#check @target_root_valid

private def leafSyntax (symbol : Nat) : InternedNestedConstruction.Syntax Nat Bool :=
  .node [⟨symbol, true, []⟩]
private def first := InternedFreshOrdinaryConstruction.build (leafSyntax 0) [] empty
private def source : State Nat Bool := first.state
private def left : Value Nat Bool := match first with
  | .done value _ => value
  | .pending _ _ => .empty
private theorem first_done : first = .done left source := by cbv
private theorem first_verified : InternedNestedFacts.Verified empty first Available :=
  InternedFreshOrdinaryFacts.closed_verified (leafSyntax 0)
private theorem sourceFacts : InternedNestedFacts.Facts source := first_verified.facts
private theorem leftAvailable : Available source left := first_verified.result _ _ first_done
private theorem leftClosed : left.free = [] := by cbv
private theorem leftOriginal : Original left :=
  SourceRecursiveIntersectionOriginalOutput.closed_original _ source sourceFacts.coherent leftAvailable leftClosed

private def second := InternedFreshOrdinaryConstruction.build (leafSyntax 1) [] source
private def target : State Nat Bool := second.state
private def right : Value Nat Bool := match second with
  | .done value _ => value
  | .pending _ _ => .empty
private theorem second_done : second = .done right target := by cbv
private theorem second_verified : InternedNestedFacts.Verified source second Available :=
  InternedFreshOrdinaryFacts.build_verified (leafSyntax 1) [] source sourceFacts
    (by intro value member; cases member)
private theorem targetFacts : InternedNestedFacts.Facts target := second_verified.facts
private theorem rightAvailable : Available target right := second_verified.result _ _ second_done
private theorem rightClosed : right.free = [] := by cbv
private theorem growth : Grows source target := second_verified.growth
private theorem history : Extends source.nodes.issued target.nodes.issued := second_verified.history
private def holds (_ : Bool) (_ : Term Nat) := true
private def roots := [left]
private def targetRoots := [right, left, right]
private theorem originals : ∀ root ∈ roots, Original root := by
  intro root member
  have same : root = left := List.mem_singleton.mp member
  exact same ▸ leftOriginal
private theorem available : Values source roots := by
  intro root member
  have same : root = left := List.mem_singleton.mp member
  exact same ▸ leftAvailable
private theorem closed : ∀ root ∈ roots, root.free = [] := by
  intro root member
  have same : root = left := List.mem_singleton.mp member
  exact same ▸ leftClosed
private theorem targetAvailable : Values target targetRoots := by
  intro root member
  simp only [targetRoots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact rightAvailable
  · exact leftAvailable.grows source target growth history
  · exact rightAvailable
private theorem targetClosed : ∀ root ∈ targetRoots, root.free = [] := by
  intro root member
  simp only [targetRoots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact rightClosed
  · exact leftClosed
  · exact rightClosed
private theorem included : ∀ root ∈ roots, root ∈ targetRoots := by
  intro root member
  have same : root = left := List.mem_singleton.mp member
  subst root
  exact List.mem_cons_of_mem _ List.mem_cons_self
private def oldInputs := SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
  source sourceFacts holds roots originals available closed
private def newInputs := SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
  target targetFacts holds targetRoots (closed_originals target targetFacts targetRoots targetAvailable targetClosed)
    targetAvailable targetClosed
private theorem leftValid : oldInputs.valid (inputOf left) :=
  SourceCurrentAllocatedNativeInputInventoryModels.root_valid
    source sourceFacts holds roots originals available closed left List.mem_cons_self
private theorem left_input : inputOf left = .node 0 := by cbv
private theorem right_input : inputOf right = .node 1 := by cbv
private theorem left_nonempty : inputOf left ≠ .empty := by rw [left_input]; intro same; cases same
private theorem source_rows : (view source holds).rows 0 = [⟨0, [], fun _ => true⟩] := by cbv

example : source.nodes.next = 1 ∧ target.nodes.next = 2 := by constructor <;> cbv
example : inputOf left ≠ .empty := left_nonempty
example : inputOf right ≠ inputOf left := by rw [left_input, right_input]; decide
example : newInputs.valid (inputOf left) :=
  valid_grows source target sourceFacts targetFacts growth history holds roots originals available closed
    targetRoots targetAvailable targetClosed included _ leftValid
example : newInputs.valid (inputOf right) :=
  target_root_valid target targetFacts holds targetRoots targetAvailable targetClosed right List.mem_cons_self
example (rank : Nat) (term : Term Nat) :
    inputAt (finiteRanks (view target holds) newInputs) (inputOf left) rank term ↔
      inputAt (finiteRanks (view source holds) oldInputs) (inputOf left) rank term :=
  rank_exact source target sourceFacts targetFacts growth history holds roots originals available closed
    targetRoots targetAvailable targetClosed included _ leftValid rank term
example (rank : Nat) (term : Term Nat) :
    finiteRanks (view target holds) newInputs (identity (inputOf left)) rank term ↔
      finiteRanks (view source holds) oldInputs (identity (inputOf left)) rank term :=
  name_rank_exact source target sourceFacts targetFacts growth history holds roots originals available closed
    targetRoots targetAvailable targetClosed included _ leftValid left_nonempty rank term
example (term : Term Nat) :
    finiteLanguages (view target holds) newInputs (identity (inputOf left)) term ↔
      finiteLanguages (view source holds) oldInputs (identity (inputOf left)) term :=
  name_language_exact source target sourceFacts targetFacts growth history holds roots originals available closed
    targetRoots targetAvailable targetClosed included _ leftValid left_nonempty term
example : InputDerivation (view source holds) (inputOf left) 0 (.node 0 []) := by
  rw [left_input]
  refine .node ⟨0, [], fun _ => true⟩ ?_ [] .nil rfl
  rw [source_rows]
  exact List.mem_cons_self
example : InputDerivation (view target holds) (inputOf left) 0 (.node 0 []) := by
  apply (SourceCurrentAllocatedNativeInputGrowthModels.derivation_exact oldInputs
    (SourceCurrentAllocatedNativeInputGrowthModels.inventory_agreement source target sourceFacts targetFacts
      growth history holds roots originals available closed) _ leftValid 0 (.node 0 [])).mpr
  rw [left_input]
  refine .node ⟨0, [], fun _ => true⟩ ?_ [] .nil rfl
  rw [source_rows]
  exact List.mem_cons_self

-- Empty inventories do not admit arbitrary resident values.
example : ¬ SourceCurrentAllocatedNativeInputInventoryModels.Reachable source holds [] (inputOf left) := by
  rintro ⟨root, member, _⟩
  cases member
