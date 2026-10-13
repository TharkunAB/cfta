import MicroCFTA.InternedProbeFreeSupport
import MicroCFTA.InternedBoundaryAge

/-!
# Strict age descent through complete recursive probe records

Both original probes finish before a Mu reserves its identity. Every Mu
boundary in those probes therefore has a smaller identity. This gives
well-founded induction on the complete probe dependency graph, including
the graph left by a pending source run. It is not a body-unfolding rank.
-/
namespace MicroCFTA.InternedProbeDependencyAge
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedMissReadback InternedStoredMuOrigins InternedFreshProbeKeys
open InternedNodeIdentityFootprint InternedBoundaryAge InternedBoundaryAtoms
open InternedProbeFreeSupport
open InternedBinderProtocol (NodeKey)

/-- Each original probe contains only identities reserved before its parent Mu. -/
theorem origin_probes_older [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (origin : Origin entry body depth ordinary)
    (identity : Nat) (occurrence : Occurs identity depth ∨ Occurs identity ordinary) : identity < entry.identity := by
  obtain ⟨expression, environment, before, afterDepth, afterOrdinary, afterBody, normal, inputs,
    depthDone, ordinaryDone, missing, entrySame, bodyDone⟩ := origin
  have firstInputs : Values before (.reference .depth :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact depth_available before
    · exact inputs value member
  have first := callback_verified expression environment .depth before normal.facts firstInputs
  have afterFacts : Facts afterDepth := by simpa only [depthDone, Outcome.state] using first.facts
  have afterInputs : Values afterDepth environment := by
    intro value member
    simpa only [depthDone, Outcome.state] using first.available value (inputs value member)
  have secondInputs : Values afterDepth (.reference (.uninterned depth.depth) :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact ordinary_available afterDepth depth.depth
    · exact afterInputs value member
  have second := callback_verified expression environment (.uninterned depth.depth) afterDepth afterFacts secondInputs
  have finalFacts : Facts afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using second.facts
  have depthAvailable : Available afterOrdinary depth := by
    simpa only [ordinaryDone, Outcome.state] using second.available depth (first.result depth afterDepth depthDone)
  have ordinaryAvailable := second.result ordinary afterOrdinary ordinaryDone
  rw [entrySame, intern_miss_identity afterOrdinary.nodes _ missing]
  rcases occurrence with inDepth | inOrdinary
  · exact available_below afterOrdinary finalFacts.coherent depth depthAvailable identity inDepth
  · exact available_below afterOrdinary finalFacts.coherent ordinary ordinaryAvailable identity inOrdinary

/-- Each recursive boundary in an original probe has a strictly older identity. -/
theorem origin_boundary_older [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (origin : Origin entry body depth ordinary)
    (identity : Nat) (boundary : .mu identity ∈ atoms depth ∨ .mu identity ∈ atoms ordinary) :
    identity < entry.identity := by
  apply origin_probes_older entry body depth ordinary origin identity
  rcases boundary with inDepth | inOrdinary
  · exact Or.inl (atom_occurs depth _ identity (Or.inr rfl) inDepth)
  · exact Or.inr (atom_occurs ordinary _ identity (Or.inr rfl) inOrdinary)

/-- Read a complete record's identity for the probe dependency measure. -/
def recordIdentity (state : State Symbol Guard) (key : NodeKey) : Nat :=
  (((state.nodeRecords key).bind entryOf).map (fun entry => entry.identity)).getD 0

/-- Every actual recursive probe dependency strictly decreases the complete-record identity. -/
theorem step_decreases [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (origins : InternedStoredMuOrigins.Heap state) (first second : NodeKey) (step : ProbeStep state first second) :
    recordIdentity state second < recordIdentity state first := by
  obtain ⟨entry, body, depth, ordinary, nextEntry, nextBody, nextDepth, nextOrdinary,
    firstStored, secondStored, boundary⟩ := step
  have smaller := origin_boundary_older entry body depth ordinary (origins _ _ _ _ _ firstStored)
    nextEntry.identity boundary
  simpa only [recordIdentity, firstStored, secondStored, Option.bind_some, entryOf,
    Option.map_some, Option.getD_some] using smaller

/-- A finite probe chain never increases its complete-record identity. -/
theorem chain_le [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (origins : InternedStoredMuOrigins.Heap state) (first last : NodeKey) (chain : ProbeChain state first last) :
    recordIdentity state last ≤ recordIdentity state first := by
  induction chain with
  | refl => exact Nat.le_refl _
  | step head tail ih => exact Nat.le_trans ih (Nat.le_of_lt (step_decreases state origins _ _ head))

/-- No nonempty chain of actual stored probe dependencies returns to its starting record. -/
theorem no_cycle [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (origins : InternedStoredMuOrigins.Heap state) (first second : NodeKey)
    (step : ProbeStep state first second) (back : ProbeChain state second first) : False := by
  exact Nat.not_lt_of_ge (chain_le state origins second first back) (step_decreases state origins first second step)

/-- Reversing each probe edge gives a well-founded relation on complete record keys. -/
theorem wellFounded [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (origins : InternedStoredMuOrigins.Heap state) :
    WellFounded (fun child parent => ProbeStep state parent child) := by
  apply Subrelation.wf (r := (measure (recordIdentity state)).rel) ?_ (measure (recordIdentity state)).wf
  intro child parent edge
  exact step_decreases state origins parent child edge

/-- Complete probe dependencies supply an induction principle with strictly older recursive premises. -/
theorem induction [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (origins : InternedStoredMuOrigins.Heap state) (property : NodeKey → Prop)
    (step : ∀ parent, (∀ child, ProbeStep state parent child → property child) → property parent)
    (key : NodeKey) : property key :=
  (wellFounded state origins).induction key step

/-- Every first closed source run has a well-founded complete probe graph, even if it stops pending. -/
theorem closed_wellFounded [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    WellFounded (fun child parent => ProbeStep (build expression [] empty).state parent child) :=
  wellFounded _ (InternedNestedMuOrigins.closed_origins expression)

end MicroCFTA.InternedProbeDependencyAge
