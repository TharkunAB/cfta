import MicroCFTA.InternedProfileComposition
import MicroCFTA.InternedProfileCandidate
import MicroCFTA.InternedRootProfileFilter
import MicroCFTA.InternedProfileFree
import MicroCFTA.InternedNestedMuOrigins

/-!
# Local profile facts for the complete source schedule

Each checked execution preserves decoded profiles in the cache and proves
its output profile when it completes. A pending outcome retains the cache
invariant. Source sequencing and the actual callback filter compose these
facts without assuming that every callback completes.
-/
namespace MicroCFTA.InternedProfileExecutionFacts
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedNestedRequestFacts
open InternedNestedMissReadback InternedStoredMuOrigins InternedProfileHeap
open InternedRootProfile InternedProfileEquivalence InternedProfileSemantics
open InternedBinderProtocol (Reference NodeKey)

/-- A source outcome preserves the complete recursive profile table and verifies any returned result. -/
structure Checked (outcome : Outcome Symbol Guard Result) (property : Result → Prop) : Prop where
  heap : InternedProfileHeap.Heap outcome.state
  result : ∀ value after, outcome = .done value after → property value

/-- A returned source value preserves the current table. -/
theorem done_checked (value : Result) (state : State Symbol Guard) (property : Result → Prop)
    (heap : InternedProfileHeap.Heap state) (holds : property value) : Checked (.done value state) property := by
  refine ⟨heap, ?_⟩
  intro result after returned
  cases returned
  exact holds

/-- A pending source lookup returns no unchecked result. -/
theorem pending_checked (key : NodeKey) (state : State Symbol Guard) (property : Result → Prop)
    (heap : InternedProfileHeap.Heap state) : Checked (.pending key state) property := by
  refine ⟨heap, ?_⟩
  intro value after impossible
  cases impossible

/-- Ordered source sequencing uses only facts obtained from actual earlier completion. -/
theorem bind_checked (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (firstProperty : First → Prop) (property : Result → Prop)
    (checked : Checked outcome firstProperty)
    (later : ∀ value after, outcome = .done value after → InternedProfileHeap.Heap after → firstProperty value →
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
  · exact InternedProfileHeap.preserve after _ afterHeap (filter_noNewMu name value after)
  · exact trans (InternedRootProfileFilter.filter_profile name value after afterNormal available)
      (normalize_same name same)

/-- A source cache miss chooses a name absent from all captured root profiles. -/
theorem fresh_profiles (depth ordinary : Value Symbol Guard) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (inputs : Values state environment)
    (missing : state.nodes.table (muKey depth ordinary) = none) :
    ∀ value ∈ environment.map profile,
      .interned (Cache.intern state.nodes (muKey depth ordinary)).1.identity ∉ value.getD [] := by
  intro value member present
  obtain ⟨actual, included, rfl⟩ := List.mem_map.mp member
  have actualFree := InternedProfileFree.member_free actual _ state facts.coherent (inputs actual included) present
  rw [InternedFreshProbeKeys.intern_miss_identity state.nodes _ missing] at actualFree
  exact InternedFreshProbeKeys.next_absent state.nodes facts.coherent.valid.2 actual (inputs actual included).issued actualFree

end MicroCFTA.InternedProfileExecutionFacts
