import MicroCFTA.SourcePhysicalRecursiveRowsShared
import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.InternedFreshOrdinaryReplay

/-!
# Source construction of a productive recursive knot

The actual repaired constructor builds mu x. (base | step x) from empty
caches. The proof retains both probes, the reserved Mu identity, the stored
body, and both final counters. The symbols can be equal because the rows
have different arities. No completed knot or cache invariant is assumed.
-/
namespace MicroCFTA.SourcePhysicalRecursiveConstruction
open InternedConstructorTemplates InternedNestedConstruction InternedBinderProtocol
open InternedNestedFacts InternedProbeProvenance InternedEdgeResidency SourcePhysicalRecursiveRows

variable {Symbol : Type}

/-- The source body has one nullary row and one unary recursive row. -/
def expression (base step : Symbol) : Syntax Symbol Unit :=
  .binder true (.node [.mk base () [], .mk step () [.var 0]])

/-- The base row is the first physical edge issued by the source constructor. -/
def baseEntry (base : Symbol) : Cache.Interned (EdgeKey Symbol Unit) := ⟨0, ⟨base, [], ()⟩⟩

/-- Each probe and the actual body retain their own recursive child reference. -/
def stepEntry (step : Symbol) (name : Reference) (identity : Nat) : Cache.Interned (EdgeKey Symbol Unit) :=
  ⟨identity, ⟨step, [.ref name], ()⟩⟩

/-- A completed probe retains its physical rows and cached metadata. -/
def probe (base step : Symbol) (name : Reference) (nodeIdentity edgeIdentity : Nat) : Value Symbol Unit :=
  .node ⟨nodeIdentity, .node [0, edgeIdentity]⟩
    [.mk (baseEntry base) [], .mk (stepEntry step name edgeIdentity) [.reference name]] 0 [name]

/-- The source reserves its Mu identity after completing the two probe nodes. -/
def muEntry : Cache.Interned NodeKey := ⟨2, .mu ⟨.node 0, .node 1⟩⟩

/-- The actual stored body has its own canonical ordinary node identity. -/
def bodyEntry : Cache.Interned NodeKey := ⟨3, .node [0, 3]⟩

/-- The exact completed source record supplies the earlier knot interface. -/
def record (base step : Symbol) : Value Symbol Unit :=
  knot muEntry bodyEntry (baseEntry base) (stepEntry step (.interned 2) 3)
    (probe base step .depth 0 1) (probe base step (.uninterned 0) 1 2)

/-- Read the returned record and both counters without equating function-valued caches. -/
def observation : Outcome Symbol Unit (Value Symbol Unit) → Option (Value Symbol Unit × Nat × Nat)
  | .pending .. => none
  | .done value state => some (value, state.nodes.next, state.edges.next)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Kernel evaluation follows both actual probes, reservation, body construction, and cleanup. -/
theorem source_observed [DecidableEq Symbol] (base step : Symbol) :
    observation (InternedFreshOrdinaryConstruction.build (expression base step) [] empty) =
      some (record base step, 4, 4) := by
  by_cases same : base = step
  · subst step
    cbv
  · cbv
    simp (config := { maxSteps := 1000000 }) [EdgeKey.mk.injEq, same, Ne.symm same, Cache.put,
      Cache.keepFirst, Cache.install, Cache.reserve, BEq.beq, Value.referenceOf, EdgeValue.entry,
      EdgeValue.children, Value.free, Value.depth, maximumDepth, childFree, canonicalFree, canonicalEdges,
      surviving, identifyNode, List.eraseDupsBy.loop, List.find?,
      List.filterMap, List.flatMap, InternedConstructorTemplates.run, nodeStep, edgeStep, Cache.intern,
      withoutSelfReference, InternedFreshOrdinaryConstruction.build,
      InternedFreshOrdinaryConstruction.buildMany, InternedFreshOrdinaryConstruction.buildEdges,
      finish, muKey, cleanup, Outcome.bind, work, makeEdge, makeNode]
    cbv

/-- Retain the exact final cache produced by source execution. -/
def final [DecidableEq Symbol] (base step : Symbol) : State Symbol Unit :=
  (InternedFreshOrdinaryConstruction.build (expression base step) [] empty).state

/-- Actual construction completes with the exact knot and its actual final cache. -/
theorem source_return [DecidableEq Symbol] (base step : Symbol) :
    InternedFreshOrdinaryConstruction.build (expression base step) [] empty =
      .done (record base step) (final base step) := by
  have observed := source_observed base step
  cases done : InternedFreshOrdinaryConstruction.build (expression base step) [] empty with
  | pending key state => simp [done, observation] at observed
  | done value state =>
      have fields : (value, state.nodes.next, state.edges.next) = (record base step, 4, 4) := by
        simpa only [done, observation, Option.some.injEq] using observed
      simp only [Prod.mk.injEq] at fields
      simp only [final, done, Outcome.state, fields.1]

/-- Later cache growth retains exact source constructor replay without allocation. -/
theorem source_replay [DecidableEq Symbol] (base step : Symbol) (after : State Symbol Unit)
    (growth : Grows (final base step) after) :
    InternedFreshOrdinaryConstruction.build (expression base step) [] after = .done (record base step) after :=
  InternedFreshOrdinaryReplay.empty_replay (expression base step) (record base step) (final base step) after
    (source_return base step) growth

/-- The constructor derives coherence and complete-knot availability from empty caches. -/
theorem constructed [DecidableEq Symbol] (base step : Symbol) :
    Facts (final base step) ∧ Available (final base step) (record base step) ∧
      (final base step).nodes.next = 4 ∧ (final base step).edges.next = 4 := by
  have checked := InternedFreshOrdinaryFacts.closed_verified (expression base step)
  have facts : Facts (final base step) := by
    simpa only [source_return, Outcome.state] using checked.facts
  have observed := source_observed base step
  have counters : (final base step).nodes.next = 4 ∧ (final base step).edges.next = 4 := by
    simpa only [source_return, observation, Option.some.injEq, Prod.mk.injEq, true_and] using observed
  exact ⟨facts, checked.result _ _ (source_return base step), counters⟩

/-- Source-derived coherence supplies exact unfolding, stable replay, and independent language. -/
theorem source_unfold [DecidableEq Symbol] (base step : Symbol) :
    ∃ result after,
      InternedFreshOrdinaryStoredSubstitution.unfold (record base step) (final base step) = .done result after ∧
      Facts after ∧ Available after result ∧
      InternedFreshOrdinaryStoredSubstitution.unfold (record base step) after = .done result after ∧
      (∀ term, Physical (final base step) (record base step) term ↔ Chain base step term) ∧
      (∀ term, Physical after (record base step) term ↔ Chain base step term) ∧
      (∀ term, Physical (final base step) (record base step) term ↔ Physical after result term) := by
  obtain ⟨facts, available, _⟩ := constructed base step
  exact unfold_language muEntry bodyEntry (baseEntry base) (stepEntry step (.interned 2) 3)
    (probe base step .depth 0 1) (probe base step (.uninterned 0) 1 2) (final base step) facts available

/-- Actual source construction and exposure produce finite exact shared rows without a stored-knot premise. -/
theorem source_rows [DecidableEq Symbol] (base step : Symbol) :
    ∃ result after fuel raw,
      InternedFreshOrdinaryConstruction.build (expression base step) [] empty =
        .done (record base step) (final base step) ∧
      InternedFreshOrdinaryStoredSubstitution.unfold (record base step) (final base step) = .done result after ∧
      Facts after ∧ Available after result ∧
      (∀ larger, fuel ≤ larger → SourceInternedRows.toRows (heap 2 ((nodeEdges result).map exposure))
        larger (some 2) = some raw) ∧
      (∀ term, Language.Accepts (SourceRowsMinimumAdapter.automaton raw) (.interned 2) term ↔ Chain base step term) := by
  obtain ⟨facts, available, _⟩ := constructed base step
  obtain ⟨_, _, _, _, _, _, cold, _, _⟩ := source_unfold base step
  obtain ⟨result, after, fuel, raw, done, afterFacts, resultAvailable, rowsDone, exactRows⟩ :=
    shared_exposure muEntry bodyEntry (baseEntry base) (stepEntry step (.interned 2) 3)
      (probe base step .depth 0 1) (probe base step (.uninterned 0) 1 2) (final base step) facts available
  refine ⟨result, after, fuel, raw, source_return base step, done, afterFacts, resultAvailable, rowsDone, ?_⟩
  intro term
  exact (exactRows term).trans (cold term)

end MicroCFTA.SourcePhysicalRecursiveConstruction
