import MicroCFTA.SourceCurrentCausalSourceComparison

/-!
# Assigned payload profiles from actual empty-table histories

Each publication proves its payload after the earlier callback histories.
An effect that adds no Mu retains the state-independent payload contract.
Thus an actual reader history supplies the contract needed by source
comparison. Callers need no separate assumed payload heap.
-/
namespace MicroCFTA.SourceCurrentCausalHistoryProfiles
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedFreshOrdinaryLiveInputs (input)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile Equivalent)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentPublicationHeapInduction (Heap)
open SourceCurrentStoredMuProfileContract (Correct)

/-- Actual forward history extends the already proved state-independent payload contract. -/
theorem history_heap [DecidableEq (EdgeKey Symbol Guard)]
    {before after : State Symbol Guard} (path : History before after)
    (earlier : History empty before) (initial : Heap Correct before) : Heap Correct after := by
  revert earlier initial
  induction path with
  | refl state => intro _ initial; exact initial
  | retain before after old =>
      intro _ initial
      exact SourceCurrentPublicationHeapInduction.retain Correct initial old
  | trans first next firstIH nextIH =>
      intro earlier initial
      exact nextIH (.trans earlier first) (firstIH earlier initial)
  | publication event depthPath ordinaryPath bodyPath depthIH ordinaryIH bodyIH =>
      intro earlier initial
      have depthHistory : History empty event.afterDepth := .trans earlier depthPath
      have afterDepth := depthIH earlier initial
      have cutHistory : History empty event.cut := .trans depthHistory ordinaryPath
      have cut := ordinaryIH depthHistory afterDepth
      have allocated : Heap Correct event.allocated := cut
      have reservation : History event.cut event.allocated :=
        .retain event.cut event.allocated (fun _ _ _ _ _ present => present)
      have allocatedHistory : History empty event.allocated := .trans cutHistory reservation
      have bodyHistory : History empty event.afterBody := .trans allocatedHistory bodyPath
      have afterBody := bodyIH allocatedHistory allocated
      exact SourceCurrentPublicationHeapInduction.complete Correct event.smart event.entry event.body
        event.depth event.ordinary event.afterBody afterBody
        (SourceCurrentCausalSourceComparison.publication event afterBody bodyHistory)

/-- An actual reader history from empty tables derives every stored payload's assigned profile law. -/
theorem heap [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard) (history : History empty reader) :
    Heap Correct reader :=
  history_heap history (.refl empty) (SourceCurrentPublicationHeapInduction.empty Correct)

/-- Actual causal readers compare full source results without a supplied semantic payload heap. -/
theorem compare [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (reader : State Symbol Guard) (history : History empty reader)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (firstAssignment secondAssignment : Reference → Profile) (firstCuts secondCuts : Reference → Bool)
    (firstBefore firstAfter secondBefore secondAfter : State Symbol Guard)
    (first second : Value Symbol Guard)
    (firstContext : Context firstBefore (inputs.map (input firstNames)))
    (secondContext : Context secondBefore (inputs.map (input secondNames)))
    (aliases : SourceCurrentUsedBinderAliasTransport.Aliases expression inputs firstNames secondNames)
    (profiles : SourceCurrentScopedProfileInputs.Compatible expression inputs firstNames secondNames firstAssignment secondAssignment)
    (cuts : SourceCurrentScopedDeletionInputs.Compatible expression inputs firstNames secondNames firstCuts secondCuts)
    (firstDone : InternedFreshOrdinaryConstruction.build expression (inputs.map (input firstNames)) firstBefore = .done first firstAfter)
    (secondDone : InternedFreshOrdinaryConstruction.build expression (inputs.map (input secondNames)) secondBefore = .done second secondAfter)
    (firstGrowth : Grows firstAfter reader) (secondGrowth : Grows secondAfter reader) :
    Equivalent (SourceCurrentStoredRootDeletion.deleted firstCuts first firstAssignment)
      (SourceCurrentStoredRootDeletion.deleted secondCuts second secondAssignment) :=
  SourceCurrentCausalSourceComparison.source expression reader inputs firstNames secondNames
    firstAssignment secondAssignment firstCuts secondCuts firstBefore firstAfter secondBefore secondAfter first second
    firstContext secondContext aliases profiles cuts firstDone secondDone firstGrowth secondGrowth (heap reader history) history

/-- Any supported source call after an actual history retains the derived payload contract. -/
theorem build_heap [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (history : History empty state) :
    Heap Correct (InternedFreshOrdinaryConstruction.build expression environment state).state :=
  SourceCurrentCausalSourceComparison.build_heap expression environment state context history (heap state history)

end MicroCFTA.SourceCurrentCausalHistoryProfiles
