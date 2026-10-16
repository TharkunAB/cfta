import MicroCFTA.SourceCurrentAllocatedNativeContextRebase
import MicroCFTA.SourceCurrentAllocatedNativeGrownInventory

#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.NameCovered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.SeenCovered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.SeenAdmitted
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.language
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.name_rank
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.name_language
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.name_covered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.seen_covered
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.sound_pairs
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.complete_pairs
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.initial_seen
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.advance_seen
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.seen_admitted
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.node_inputs
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.edge_inputs
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.admitted
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.row_language
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.row_rank
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.node_law
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.edge_law
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.contextual
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextRebase.rebase

#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.NameCovered
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.SeenCovered
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.SeenAdmitted
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.language
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.name_rank
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.name_language
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.name_covered
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.seen_covered
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.sound_pairs
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.complete_pairs
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.initial_seen
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.advance_seen
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.seen_admitted
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.node_inputs
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.edge_inputs
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.admitted
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.row_language
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.Agreement.row_rank
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.node_law
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.edge_law
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.contextual
#check @MicroCFTA.SourceCurrentAllocatedNativeContextRebase.rebase

namespace MicroCFTA.ContextRebaseProbe
open Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativeContextCache SourceCurrentAllocatedNativePairContexts
open SourceCurrentAllocatedNativeInputModelTransport (Admitted)
open SourceCurrentAllocatedNativeContextRebase
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {oldView newView : View Symbol} {width : Nat}

-- Both contextual environment directions preserve the exact shared rank bound.
example (before : FiniteInput oldView) (after : FiniteInput newView) (agreement : Agreement before after)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (seen : SeenCovered before domain)
    (bound : Nat) (output : InternedGuardedLanguage.Env Symbol)
    (sound : SoundPairs (finiteLanguages newView after) domain output)
    (complete : CompletePairs (finiteRanks newView after) bound domain output) :
    SoundPairs (finiteLanguages oldView before) domain output ∧
      CompletePairs (finiteRanks oldView before) bound domain output ∧ SeenCovered after domain :=
  ⟨agreement.sound_pairs seen sound, agreement.complete_pairs seen complete, agreement.seen_covered seen⟩

-- A machine advance and cross-view rebase retain the same returned request records.
example (before : FiniteInput oldView) (after : FiniteInput newView) (agreement : Agreement before after)
    (holds : Guard → Term Symbol → Bool) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (machine : Machine Symbol Guard) (admitted : Admitted oldView (finiteInputMeaning oldView before) state)
    (seen : SeenAdmitted before state)
    (valid : Contextual oldView (finiteInputMeaning oldView before) (finiteRankedInput oldView before) holds state) :
    Contextual newView (finiteInputMeaning newView after) (finiteRankedInput newView after) holds (advance state machine) ∧
      Admitted newView (finiteInputMeaning newView after) (advance state machine) ∧
      SeenAdmitted after (advance state machine) :=
  rebase agreement holds (advance state machine)
    (SourceCurrentAllocatedNativeInputModelTransport.advance_admitted oldView (finiteInputMeaning oldView before) state machine admitted)
    (advance_seen before state machine seen)
    (advance_contextual oldView (finiteInputMeaning oldView before) (finiteRankedInput oldView before) holds state machine valid)

-- The empty native cache derives both coverage premises before cross-view transport.
example (before : FiniteInput oldView) (after : FiniteInput newView) (agreement : Agreement before after)
    (holds : Guard → Term Symbol → Bool) (machine : Machine Symbol Guard) :
    Contextual newView (finiteInputMeaning newView after) (finiteRankedInput newView after) holds (initial width machine) ∧
      Admitted newView (finiteInputMeaning newView after) (initial width machine) ∧
      SeenAdmitted after (initial width machine) :=
  rebase agreement holds (initial width machine)
    (SourceCurrentAllocatedNativeInputModelTransport.initial_admitted oldView (finiteInputMeaning oldView before) width machine)
    (initial_seen before width machine)
    (initial_contextual oldView (finiteInputMeaning oldView before) (finiteRankedInput oldView before) holds width machine)

-- A common finite input term is retained by the exact old result under the new view.
example (before : FiniteInput oldView) (after : FiniteInput newView) (agreement : Agreement before after)
    (holds : Guard → Term Symbol → Bool) (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (admitted : NodeInputs oldView (finiteInputMeaning oldView before) request)
    (seen : SeenCovered before request.domain.key)
    (law : NodeLaw oldView (finiteInputMeaning oldView before) (finiteRankedInput oldView before) holds request result)
    (output : InternedGuardedLanguage.Env Symbol) (first second : Nat) (term : Term Symbol)
    (complete : CompletePairs (finiteRanks newView after) (first + second) request.domain.key output)
    (left : inputAt (finiteRanks newView after) (inputOf request.left) first term)
    (right : inputAt (finiteRanks newView after) (inputOf request.right) second term) :
    InternedGuardedLanguage.meaning holds output result term :=
  (node_law agreement holds request result admitted seen law).complete (agreement.node_inputs admitted)
    (first + second) output complete first second (Nat.le_refl _) term left right

section ActualGrowth
variable (source target : InternedConstructorTemplates.State Symbol Guard)
  (sourceFacts : InternedNestedFacts.Facts source) (targetFacts : InternedNestedFacts.Facts target)
  (growth : Grows source target) (history : Cache.Extends source.nodes.issued target.nodes.issued)
  (holds : Guard → Term Symbol → Bool) (roots : List (Value Symbol Guard))
  (originals : ∀ root ∈ roots, Original root) (available : Values source roots)
  (closed : ∀ root ∈ roots, root.free = [])
  (targetRoots : List (Value Symbol Guard)) (targetAvailable : Values target targetRoots)
  (targetClosed : ∀ root ∈ targetRoots, root.free = []) (included : ∀ root ∈ roots, root ∈ targetRoots)
local notation "oldInputs" => SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
  source sourceFacts holds roots originals available closed
local notation "newInputs" => SourceCurrentAllocatedNativeInputInventoryModels.finiteInput
  target targetFacts holds targetRoots
    (SourceCurrentAllocatedNativeGrownInventory.closed_originals target targetFacts targetRoots targetAvailable targetClosed)
    targetAvailable targetClosed

-- Actual retained records construct Agreement; a newly listed target value needs no old-domain membership.
example (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (admitted : Admitted (view source holds) (finiteInputMeaning (view source holds) oldInputs) state)
    (seen : SeenAdmitted oldInputs state)
    (valid : Contextual (view source holds) (finiteInputMeaning (view source holds) oldInputs)
      (finiteRankedInput (view source holds) oldInputs) holds state)
    (newValue : Value Symbol Guard) (member : newValue ∈ targetRoots) :
    Contextual (view target holds) (finiteInputMeaning (view target holds) newInputs)
      (finiteRankedInput (view target holds) newInputs) holds state ∧
      Admitted (view target holds) (finiteInputMeaning (view target holds) newInputs) state ∧
      SeenAdmitted newInputs state ∧ (newInputs).valid (inputOf newValue) := by
  have agreement : Agreement oldInputs newInputs :=
    ⟨SourceCurrentAllocatedNativeGrownInventory.valid_grows source target sourceFacts targetFacts growth history
        holds roots originals available closed targetRoots targetAvailable targetClosed included,
      SourceCurrentAllocatedNativeGrownInventory.rank_exact source target sourceFacts targetFacts growth history
        holds roots originals available closed targetRoots targetAvailable targetClosed included⟩
  obtain ⟨contextual, newAdmitted, newSeen⟩ := rebase agreement holds state admitted seen valid
  exact ⟨contextual, newAdmitted, newSeen, SourceCurrentAllocatedNativeGrownInventory.target_root_valid
    target targetFacts holds targetRoots targetAvailable targetClosed newValue member⟩
end ActualGrowth
end MicroCFTA.ContextRebaseProbe

