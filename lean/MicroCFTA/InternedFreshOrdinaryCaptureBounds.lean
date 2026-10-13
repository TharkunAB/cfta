import MicroCFTA.InternedFreshOrdinarySemanticOrigins

/-!
# Ordinary capture bounds for complete repaired Mu records

Actual source origins show that the Depth observation retains exactly the
stored Mu's ordinary captures. Every such capture lies below the selected
ordinary probe. This statement covers records from discarded computations.
-/
namespace MicroCFTA.InternedFreshOrdinaryCaptureBounds
open Cache InternedConstructorTemplates InternedProbeProvenance InternedConstructionProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (depth_available ordinary_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinarySemanticOrigins
open InternedFreshOrdinarySourceFreeNames
open InternedBinderProtocol (Reference NodeKey)

/-- The original Depth observation has exactly the complete Mu's free ordinary references. -/
theorem origin_ordinary_free [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (origin : Origin entry body depth ordinary) (level : Nat) :
    .uninterned level ∈ (Value.mu entry body depth ordinary).free ↔ .uninterned level ∈ depth.free := by
  obtain ⟨expression, environment, before, afterDepth, afterOrdinary, afterBody,
    context, depthDone, ordinaryDone, missing, entrySame, bodyDone⟩ := origin
  subst entry
  have afterContext : Context afterDepth environment := by
    simpa only [depthDone, Outcome.state] using context.callback expression .depth (depth_available before)
  have finalContext : Context afterOrdinary environment := by
    simpa only [ordinaryDone, Outcome.state] using
      afterContext.callback expression (.uninterned (ordinaryLevel depth)) (ordinary_available afterDepth (ordinaryLevel depth))
  let key := muKey depth ordinary
  let entry := Cache.intern afterOrdinary.nodes key
  let allocated := {afterOrdinary with nodes := entry.2}
  have reserved : Context allocated environment := finalContext.reserve key
  have argument : Available allocated (.reference (.interned entry.1.identity)) :=
    (reserve_available key afterOrdinary finalContext.normal.facts.coherent finalContext.normal.facts.cached).2
  have bodyNames := callback_other expression environment (.interned entry.1.identity) allocated reserved.normal
    (reserved.local _ argument).inputs reserved.freeNames reserved.profiles body afterBody bodyDone
    (.uninterned level) (by intro impossible; cases impossible)
  have depthNames := callback_other expression environment .depth before context.normal
    (context.local .depth (depth_available before)).inputs context.freeNames context.profiles depth afterDepth depthDone
    (.uninterned level) (by intro impossible; cases impossible)
  simpa [Value.free] using bodyNames.trans depthNames.symm

/-- Every ordinary capture of a complete repaired record lies below its chosen probe. -/
theorem origin_capture_bound [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (origin : Origin entry body depth ordinary) (level : Nat)
    (member : .uninterned level ∈ (Value.mu entry body depth ordinary).free) : level < ordinaryLevel depth :=
  ordinary_free_bound depth level ((origin_ordinary_free entry body depth ordinary origin level).mp member)

/-- Every stored repaired record after any closed run has the strict ordinary capture bound. -/
theorem closed_capture_bound [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary))
    (level : Nat) (member : .uninterned level ∈ (Value.mu entry body depth ordinary).free) : level < ordinaryLevel depth :=
  origin_capture_bound entry body depth ordinary (closed_origins expression key entry body depth ordinary present) level member

end MicroCFTA.InternedFreshOrdinaryCaptureBounds
