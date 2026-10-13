import MicroCFTA.InternedNestedFreeNames
import MicroCFTA.InternedFreeNameBoundary

/-!
# Free-name origins and actual source callback observations

Full source execution introduces no free name outside its environment.
Each normalized callback has the same captured free names away from its
supplied argument. These statements include nested recursive requests.
-/
namespace MicroCFTA.InternedSourceFreeNames
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedMissReadback InternedStoredMuOrigins InternedNestedFreeNames
open InternedFreeNameComposition InternedFreeNameRequest InternedRootProfile
open InternedFreshProbeKeys InternedConstructionProvenance InternedBoundaryAtoms
open InternedBinderProtocol (Reference)

/-- Every returned free name came from one actual lexical environment value. -/
theorem build_free_origins [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment)
    (heap : InternedFreeNameHeap.Heap state) (profiles : InternedProfileHeap.Heap state)
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
    InternedFreeNameHeap.empty_heap InternedProfileHeap.empty_heap value state done name member
  cases impossible

/-- A completed source result preserves every age bound on the captured free names. -/
theorem build_free_below [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment)
    (heap : InternedFreeNameHeap.Heap state) (profiles : InternedProfileHeap.Heap state)
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
    (heap : InternedFreeNameHeap.Heap state) (profiles : InternedProfileHeap.Heap state) :
    Checked (callback expression environment name state)
      (fun value => ∀ other, other ≠ name →
        (other ∈ value.free ↔ other ∈ InternedProfileCallbackForm.captures
          (InternedFreeNameForm.symbolic expression (environment.map profile) (environment.map Value.free)))) := by
  apply InternedFreeNameRequest.callback_checked expression environment name _ state normal inputs
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
    (heap : InternedFreeNameHeap.Heap state) (profiles : InternedProfileHeap.Heap state)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : callback expression environment name state = .done value after) (other : Reference) (different : other ≠ name) :
    other ∈ value.free ↔ other ∈ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic expression (environment.map profile) (environment.map Value.free)) :=
  (callback_checked expression environment name state normal inputs heap profiles).result value after done other different

/-- Actual callback execution also preserves the already proved root-profile heap. -/
theorem callback_profile_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state (.reference name :: environment))
    (profiles : InternedProfileHeap.Heap state) :
    InternedProfileHeap.Heap (callback expression environment name state).state := by
  exact (InternedProfileExecutionFacts.callback_checked expression environment name state normal inputs
    (by simpa only [List.map_cons, profile] using
      InternedNestedProfiles.build_profile expression (.reference name :: environment) state normal inputs profiles)).heap

/-- The actual three-call miss schedule transfers an old free-name bound to both probe boundaries. -/
theorem probes_reference_absent [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before afterDepth beforeReserve afterBody : State Symbol Guard)
    (normal : Normal before) (inputs : Values before environment)
    (heap : InternedFreeNameHeap.Heap before) (profiles : InternedProfileHeap.Heap before)
    (depth ordinary body : Value Symbol Guard)
    (depthDone : callback expression environment .depth before = .done depth afterDepth)
    (ordinaryDone : callback expression environment (.uninterned depth.depth) afterDepth = .done ordinary beforeReserve)
    (missing : beforeReserve.nodes.table (muKey depth ordinary) = none)
    (bodyDone : callback expression environment
      (.interned (Cache.intern beforeReserve.nodes (muKey depth ordinary)).1.identity)
      {beforeReserve with nodes := (Cache.intern beforeReserve.nodes (muKey depth ordinary)).2} = .done body afterBody)
    (cutoff : Nat) (old : ∀ identity, .interned identity ∈ body.free → identity < cutoff) :
    ∀ identity, cutoff ≤ identity →
      .ref (.interned identity) ∉ atoms depth ∧ .ref (.interned identity) ∉ atoms ordinary := by
  have depthInputs : Values before (.reference .depth :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact depth_available before
    · exact inputs value member
  have depthChecked := callback_checked expression environment .depth before normal depthInputs heap profiles
  have depthVerified := callback_verified expression environment .depth before normal.facts depthInputs
  have depthSame := depthChecked.result depth afterDepth depthDone
  have depthNormal : Normal afterDepth := by
    simpa only [depthDone, Outcome.state] using callback_normal expression environment .depth before normal depthInputs
  have depthHeap : InternedFreeNameHeap.Heap afterDepth := by
    simpa only [depthDone, Outcome.state] using depthChecked.heap
  have depthProfiles : InternedProfileHeap.Heap afterDepth := by
    simpa only [depthDone, Outcome.state] using callback_profile_heap expression environment .depth before normal depthInputs profiles
  have afterInputs : Values afterDepth environment := by
    intro value member
    simpa only [depthDone, Outcome.state] using depthVerified.available value (inputs value member)
  have ordinaryInputs : Values afterDepth (.reference (.uninterned depth.depth) :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact ordinary_available afterDepth depth.depth
    · exact afterInputs value member
  have ordinaryChecked := callback_checked expression environment (.uninterned depth.depth)
    afterDepth depthNormal ordinaryInputs depthHeap depthProfiles
  have ordinaryVerified := callback_verified expression environment (.uninterned depth.depth) afterDepth depthNormal.facts ordinaryInputs
  have ordinarySame := ordinaryChecked.result ordinary beforeReserve ordinaryDone
  have reserveNormal : Normal beforeReserve := by
    simpa only [ordinaryDone, Outcome.state] using
      callback_normal expression environment (.uninterned depth.depth) afterDepth depthNormal ordinaryInputs
  have reserveHeap : InternedFreeNameHeap.Heap beforeReserve := by
    simpa only [ordinaryDone, Outcome.state] using ordinaryChecked.heap
  have reserveProfiles : InternedProfileHeap.Heap beforeReserve := by
    simpa only [ordinaryDone, Outcome.state] using
      callback_profile_heap expression environment (.uninterned depth.depth) afterDepth depthNormal ordinaryInputs depthProfiles
  have reserveInputs : Values beforeReserve environment := by
    intro value member
    simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available value (afterInputs value member)
  have depthAvailable : Available beforeReserve depth := by
    simpa only [ordinaryDone, Outcome.state] using
      ordinaryVerified.available depth (depthVerified.result depth afterDepth depthDone)
  have ordinaryAvailable := ordinaryVerified.result ordinary beforeReserve ordinaryDone
  let entry := Cache.intern beforeReserve.nodes (muKey depth ordinary)
  let allocated := {beforeReserve with nodes := entry.2}
  have allocatedNormal : Normal allocated := reserve_normal (muKey depth ordinary) beforeReserve reserveNormal
  have growth : Grows beforeReserve allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have history := intern_issued_extends beforeReserve.nodes (muKey depth ordinary) reserveNormal.facts.coherent.valid.2
  have allocatedInputs : Values allocated (.reference (.interned entry.1.identity) :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact (reserve_available (muKey depth ordinary) beforeReserve reserveNormal.facts.coherent reserveNormal.facts.cached).2
    · exact (reserveInputs value member).grows beforeReserve allocated growth history
  have bodySame := (callback_checked expression environment (.interned entry.1.identity) allocated
    allocatedNormal allocatedInputs reserveHeap reserveProfiles).result body afterBody bodyDone
  have fresh := InternedFreeNameBoundary.next_not_captured depth _ beforeReserve reserveNormal.facts.coherent depthAvailable depthSame
  have identity : entry.1.identity = beforeReserve.nodes.next := intern_miss_identity beforeReserve.nodes _ missing
  apply InternedFreeNameBoundary.probes_reference_absent depth ordinary body entry.1.identity cutoff _
    (by simpa only [identity] using fresh) depthSame ordinarySame bodySame old beforeReserve
    reserveNormal.facts.coherent depthAvailable ordinaryAvailable

end MicroCFTA.InternedSourceFreeNames
