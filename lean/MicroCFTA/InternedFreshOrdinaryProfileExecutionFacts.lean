import MicroCFTA.InternedFreshOrdinaryNormal
import MicroCFTA.InternedProfileExecutionFacts
import MicroCFTA.InternedProfileComposition
import MicroCFTA.InternedFreshOrdinaryProfileCandidate
import MicroCFTA.InternedRootProfileFilter
import MicroCFTA.InternedProfileFree
import MicroCFTA.InternedNestedMuOrigins

/-!
# Local profile facts for the repaired source schedule

Each checked execution preserves decoded profiles in the cache and proves
its output profile when it completes. A pending outcome retains the cache
invariant. Source sequencing and the actual callback filter compose these
facts without assuming that every callback completes.
-/
namespace MicroCFTA.InternedFreshOrdinaryProfileExecutionFacts
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish IsPending)
open InternedNestedFacts InternedNestedRequestFacts
open InternedNestedProvenance (Values Edges depth_available ordinary_available)
open InternedNestedMissReadback (missing_record)
open InternedStoredMuOrigins (Normal empty_normal reserve_normal filter_noNewMu)
open InternedFreshOrdinaryProfileHeap
open InternedRootProfile InternedProfileEquivalence InternedProfileSemantics
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryNormal
open InternedBinderProtocol (Reference NodeKey)

/-- A source outcome preserves the complete recursive profile table and verifies any returned result. -/
structure Checked (outcome : Outcome Symbol Guard Result) (property : Result → Prop) : Prop where
  heap : InternedFreshOrdinaryProfileHeap.Heap outcome.state
  result : ∀ value after, outcome = .done value after → property value

/-- A returned source value preserves the current table. -/
theorem done_checked (value : Result) (state : State Symbol Guard) (property : Result → Prop)
    (heap : InternedFreshOrdinaryProfileHeap.Heap state) (holds : property value) : Checked (.done value state) property := by
  refine ⟨heap, ?_⟩
  intro result after returned
  cases returned
  exact holds

/-- A pending source lookup returns no unchecked result. -/
theorem pending_checked (key : NodeKey) (state : State Symbol Guard) (property : Result → Prop)
    (heap : InternedFreshOrdinaryProfileHeap.Heap state) : Checked (.pending key state) property := by
  refine ⟨heap, ?_⟩
  intro value after impossible
  cases impossible

/-- Ordered source sequencing uses only facts obtained from actual earlier completion. -/
theorem bind_checked (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (firstProperty : First → Prop) (property : Result → Prop)
    (checked : Checked outcome firstProperty)
    (later : ∀ value after, outcome = .done value after → InternedFreshOrdinaryProfileHeap.Heap after → firstProperty value →
      Checked (next value after) property) : Checked (outcome.bind next) property := by
  cases outcome with
  | pending key state => exact pending_checked key state property checked.heap
  | done value state => exact later value state rfl checked.heap (checked.result value state rfl)

/-- The source self filter turns a checked body profile into its normalized callback profile. -/
theorem callback_checked [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state (.reference name :: environment))
    (checked : Checked (build expression (.reference name :: environment) state)
      (fun value => Equivalent (profile value) (evaluate expression (some [name] :: environment.map profile)))) :
    Checked (callback expression environment name state)
      (fun value => Equivalent (profile value) (normalize name (evaluate expression (some [name] :: environment.map profile)))) := by
  have verified := build_verified expression _ state normal.facts inputs
  have sourceNormal := build_normal expression _ state normal inputs
  unfold callback
  apply bind_checked _ _ _ _ checked
  intro value after returned afterHeap same
  have afterNormal : Normal after := by simpa only [returned, Outcome.state] using sourceNormal
  have available := verified.result value after returned
  apply done_checked
  · exact InternedFreshOrdinaryProfileHeap.preserve after _ afterHeap (filter_noNewMu name value after)
  · exact trans (InternedRootProfileFilter.filter_profile name value after afterNormal available)
      (normalize_same name same)

end MicroCFTA.InternedFreshOrdinaryProfileExecutionFacts
