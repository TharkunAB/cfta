import MicroCFTA.InternedFreshOrdinaryFreeNames
import MicroCFTA.InternedFreeNameBoundary

/-!
# Free-name origins and repaired source callback observations

Full source execution introduces no free name outside its environment.
Each normalized callback has the same captured free names away from its
supplied argument. These statements include nested recursive requests.
-/
namespace MicroCFTA.InternedFreshOrdinarySourceFreeNames
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish IsPending)
open InternedNestedFacts
open InternedNestedProvenance (Values Edges depth_available ordinary_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryNormal
open InternedStoredMuOrigins (Normal empty_normal reserve_normal filter_noNewMu)
open InternedFreshOrdinaryFreeNames
open InternedFreeNameComposition InternedFreshOrdinaryFreeRequest InternedRootProfile
open InternedFreshProbeKeys InternedConstructionProvenance InternedBoundaryAtoms
open InternedBinderProtocol (Reference)

/-- Every returned free name came from one actual lexical environment value. -/
theorem build_free_origins [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment)
    (heap : InternedFreshOrdinaryFreeHeap.Heap state) (profiles : InternedFreshOrdinaryProfileHeap.Heap state)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : build expression environment state = .done value after) (name : Reference) (member : name ∈ value.free) :
    ∃ original ∈ environment, name ∈ original.free := by
  have same := (build_free expression environment state normal inputs heap profiles).result value after done
  obtain ⟨names, source, present⟩ := InternedFreeNameSemantics.evaluate_origins expression
    (environment.map profile) (environment.map Value.free) name ((same name).mp member)
  obtain ⟨original, included, rfl⟩ := List.mem_map.mp source
  exact ⟨original, included, present⟩

/-- A completed closed source expression has no free names. -/
theorem closed_free_empty [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (done : build expression [] empty = .done value state) : value.free = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  obtain ⟨original, impossible, _⟩ := build_free_origins expression [] empty empty_normal (by simp [Values])
    InternedFreshOrdinaryFreeHeap.empty_heap InternedFreshOrdinaryProfileHeap.empty_heap value state done name member
  cases impossible

/-- A completed source result preserves every age bound on the captured free names. -/
theorem build_free_below [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment)
    (heap : InternedFreshOrdinaryFreeHeap.Heap state) (profiles : InternedFreshOrdinaryProfileHeap.Heap state)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : build expression environment state = .done value after) (cutoff : Nat)
    (old : ∀ original ∈ environment, ∀ identity, .interned identity ∈ original.free → identity < cutoff) :
    ∀ identity, .interned identity ∈ value.free → identity < cutoff := by
  intro identity member
  obtain ⟨original, included, present⟩ :=
    build_free_origins expression environment state normal inputs heap profiles value after done (.interned identity) member
  exact old original included identity present

/-- The full actual callback preserves decoded free names and observes its syntax-derived capture set. -/
theorem callback_checked [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state (.reference name :: environment))
    (heap : InternedFreshOrdinaryFreeHeap.Heap state) (profiles : InternedFreshOrdinaryProfileHeap.Heap state) :
    Checked (callback expression environment name state)
      (fun value => ∀ other, other ≠ name →
        (other ∈ value.free ↔ other ∈ InternedProfileCallbackForm.captures
          (InternedFreeNameForm.symbolic expression (environment.map profile) (environment.map Value.free)))) := by
  apply InternedFreshOrdinaryFreeRequest.callback_checked expression environment name _ state normal inputs
  have raw := build_free expression (.reference name :: environment) state normal inputs heap profiles
  refine ⟨raw.heap, ?_⟩
  intro value after done other different
  have same := raw.result value after done other
  simp only [List.map_cons, profile, Value.free] at same
  exact same.trans (InternedFreeNameForm.supplied_other expression (environment.map profile)
    (environment.map Value.free) name other different)

/-- Every completed callback agrees on each name other than its supplied argument. -/
theorem callback_other [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state (.reference name :: environment))
    (heap : InternedFreshOrdinaryFreeHeap.Heap state) (profiles : InternedFreshOrdinaryProfileHeap.Heap state)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : callback expression environment name state = .done value after) (other : Reference) (different : other ≠ name) :
    other ∈ value.free ↔ other ∈ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic expression (environment.map profile) (environment.map Value.free)) :=
  (callback_checked expression environment name state normal inputs heap profiles).result value after done other different

/-- Actual callback execution also preserves the already proved root-profile heap. -/
theorem callback_profile_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state (.reference name :: environment))
    (profiles : InternedFreshOrdinaryProfileHeap.Heap state) :
    InternedFreshOrdinaryProfileHeap.Heap (callback expression environment name state).state := by
  exact (InternedFreshOrdinaryProfileExecutionFacts.callback_checked expression environment name state normal inputs
    (by simpa only [List.map_cons, profile] using
      InternedFreshOrdinaryProfiles.build_profile expression (.reference name :: environment) state normal inputs profiles)).heap

/-- The chosen ordinary level exceeds every ordinary name in the actual callback's capture set. -/
theorem ordinary_above_captures [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state (.reference .depth :: environment))
    (heap : InternedFreshOrdinaryFreeHeap.Heap state) (profiles : InternedFreshOrdinaryProfileHeap.Heap state)
    (depth : Value Symbol Guard) (after : State Symbol Guard)
    (done : callback expression environment .depth state = .done depth after) (level : Nat)
    (member : .uninterned level ∈ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic expression (environment.map profile) (environment.map Value.free))) :
    level < ordinaryLevel depth := by
  apply ordinary_free_bound depth level
  exact (callback_other expression environment .depth state normal inputs heap profiles depth after done
    (.uninterned level) (by intro impossible; cases impossible)).mpr member

/-- Ordinary-name membership alone determines the chosen free-name bound. -/
theorem freeBound_congr (first second : List Reference)
    (same : ∀ level, .uninterned level ∈ first ↔ .uninterned level ∈ second) :
    freeBound first = freeBound second := by
  apply Nat.le_antisymm
  · exact freeBound_le first (freeBound second)
      (fun level member => freeBound_lt second level ((same level).mp member))
  · exact freeBound_le second (freeBound first)
      (fun level member => freeBound_lt first level ((same level).mpr member))

/-- The source chooser uses the syntax-derived ordinary captures of its actual callback. -/
theorem ordinary_from_captures [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state (.reference .depth :: environment))
    (heap : InternedFreshOrdinaryFreeHeap.Heap state) (profiles : InternedFreshOrdinaryProfileHeap.Heap state)
    (depth : Value Symbol Guard) (after : State Symbol Guard)
    (done : callback expression environment .depth state = .done depth after) :
    ordinaryLevel depth = max depth.depth (freeBound (InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic expression (environment.map profile) (environment.map Value.free)))) := by
  unfold ordinaryLevel
  congr 1
  apply freeBound_congr
  intro level
  exact callback_other expression environment .depth state normal inputs heap profiles depth after done
    (.uninterned level) (by intro impossible; cases impossible)

end MicroCFTA.InternedFreshOrdinarySourceFreeNames
