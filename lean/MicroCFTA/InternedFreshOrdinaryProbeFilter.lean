import MicroCFTA.InternedFreshOrdinarySemanticOrigins
import MicroCFTA.InternedStoredSelfFilter

/-!
# Fixed filters on the actual stored Mu probes

The original source callbacks filter both probes. Their retained semantic
contexts justify that filter. Reapplying the filter returns the same complete
probe and the same cache. No binder language law supplies this fact.
-/
namespace MicroCFTA.InternedFreshOrdinaryProbeFilter
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedStoredSelfFilter (NoSelf)
open InternedBinderProtocol (Reference NodeKey)

/-- A filtered root has no matching bare union member, so filtering has no effects. -/
theorem filter_fixed [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (clean : NoSelf name value) :
    run (withoutSelfReference name value) state = (value, state) := by
  cases value <;> simp only [withoutSelfReference, run] <;> try rfl
  case union entry members depth free =>
    have absent : members.any (fun member => member.referenceOf == .ref name) = false := by
      apply Bool.eq_false_iff.mpr
      intro present
      obtain ⟨member, included, equal⟩ := List.any_eq_true.mp present
      have same := (referenceOf_self_iff name member).mp (beq_iff_eq.mp equal)
      exact clean (same ▸ included)
    simp only [absent, Bool.false_eq_true, ↓reduceIte, run]

/-- A completed repaired callback derives its filtered-root property from its actual source context. -/
theorem callback_clean [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (before after : State Symbol Guard)
    (context : Context before environment) (argument : Available before (.reference name))
    (value : Value Symbol Guard) (done : callback expression environment name before = .done value after) :
    NoSelf name value := by
  unfold callback at done
  cases returned : build expression (.reference name :: environment) before with
  | pending key current => simp only [returned, Outcome.bind] at done; cases done
  | done body current =>
      have currentContext : Context current (.reference name :: environment) := by
        simpa only [returned, Outcome.state] using (context.local name argument).build expression
      have available := (build_verified expression (.reference name :: environment) before context.normal.facts
        (context.local name argument).inputs).result body current returned
      have filtered := InternedStoredSelfFilter.filter_noSelf name body current currentContext.normal.facts.coherent
        currentContext.normal.facts.cached currentContext.normal.flat available
      simp only [returned, Outcome.bind, work, Outcome.done.injEq] at done
      exact done.1 ▸ filtered

/-- Both stored probes satisfy the exact filter used by source reconstruction. -/
def Clean (depth ordinary : Value Symbol Guard) : Prop :=
  NoSelf .depth depth ∧ NoSelf (.uninterned (ordinaryLevel depth)) ordinary

/-- Actual original probe calls derive both fixed-filter obligations. -/
theorem origin_clean [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (origin : InternedFreshOrdinarySemanticOrigins.Origin entry body depth ordinary) : Clean depth ordinary := by
  obtain ⟨expression, environment, before, afterDepth, afterOrdinary, afterBody, context,
    depthDone, ordinaryDone, _missing, _entry, _bodyDone⟩ := origin
  have depthClean := callback_clean expression environment .depth before afterDepth context
    (InternedNestedProvenance.depth_available before) depth depthDone
  have depthContext : Context afterDepth environment := by
    simpa only [depthDone, Outcome.state] using
      context.callback expression .depth (InternedNestedProvenance.depth_available before)
  exact ⟨depthClean, callback_clean expression environment (.uninterned (ordinaryLevel depth)) afterDepth afterOrdinary
    depthContext (InternedNestedProvenance.ordinary_available afterDepth (ordinaryLevel depth)) ordinary ordinaryDone⟩

/-- Every resident Mu in the source-origin heap retains both filtered probes. -/
theorem resident_clean [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (heap : InternedFreshOrdinarySemanticOrigins.Heap state) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (available : Available state (.mu entry body depth ordinary)) :
    Clean depth ordinary :=
  origin_clean entry body depth ordinary (heap entry.key entry body depth ordinary (available.resident entry rfl))

/-- Closed source execution derives filtered probes for every complete resident Mu. -/
theorem constructed [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (done : build expression [] empty = .done value state) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (available : Available state (.mu entry body depth ordinary)) :
    Clean depth ordinary := by
  have heap : InternedFreshOrdinarySemanticOrigins.Heap state := by
    simpa only [done, Outcome.state] using InternedFreshOrdinarySemanticOrigins.closed_origins expression
  exact resident_clean state heap entry body depth ordinary available

end MicroCFTA.InternedFreshOrdinaryProbeFilter
