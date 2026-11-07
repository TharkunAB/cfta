import MicroCFTA.SourceSynthesisUniverseColdReadback
import MicroCFTA.SourceSynthesisUniverseBodyReferenceControl
import MicroCFTA.SourceSynthesisUniverseTopConjunction

/-!
# Original-input universe entry into the actual row product

The cold original universe determines the two entered domains and the
ordinary body hash join. Both actual optional-Mu continuations remain in
the equation. It covers every child fuel, including exhausted executions.
It does not supply a successful body product or a sufficient work bound.
-/
namespace MicroCFTA.SourceSynthesisUniverseColdKernelEntry
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl
open SourceSynthesisUniverseBodyReferenceControl
open SourceSynthesisTypeSyntax

variable {Symbol Guard : Type}

/-- Five actual control steps expose the ordinary row product and both real continuations. -/
theorem reference_to_rows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (available : Available state.heap (.mu u (.node b rows 0 [.interned u.identity]) depth ordinary))
    (fuel : Nat) :
    execute emptyGuard conjoin (fuel + 5) IntersectionEmptyDomain.emptyDomain
      (.reference (.interned u.identity)) (.mu u (.node b rows 0 [.interned u.identity]) depth ordinary) state =
      ((node emptyGuard conjoin
        (execute emptyGuard conjoin fuel (second u b rows depth ordinary state).1)
        rows rows (secondState u b rows depth ordinary state)).bind
        (fun value after => construction
          (SourceRecursiveIntersectionMaybeMu.maybeMu (pair b.identity u.identity) value after.heap) after)).bind
        (fun value after => construction
          (SourceRecursiveIntersectionMaybeMu.maybeMu (pair u.identity u.identity) value after.heap) after) := by
  rw [show fuel + 5 = (fuel + 3) + 2 by omega,
    SourceSynthesisUniverseReferenceControl.execute_referenceMu]
  rw [show fuel + 3 = (fuel + 1) + 2 by omega,
    execute_body_reference u b rows depth ordinary emptyGuard conjoin (fuel + 1) state facts valid available]
  rw [execute, body_diagonal_onNode u b rows depth ordinary emptyGuard conjoin _ state facts valid available]

/-- The original library and query derive their actual universe and complete row-entry equation. -/
theorem typesOf_reference_to_rows
    [DecidableEq (EdgeKey String SourceSynthesisGeneralizeSyntax.Guard)]
    (lib : Library) (query : Query) :
    ∃ u b rows depth ordinary final,
      InternedFreshOrdinaryConstruction.build
        (SourceSynthesisFirstOrderConstruction.typesOf lib query) [] empty =
        .done (.mu u (.node b rows 0 [.interned u.identity]) depth ordinary) final ∧
      Facts final ∧ Available final (.mu u (.node b rows 0 [.interned u.identity]) depth ordinary) ∧
      SourceSynthesisUniverseBody.Shape SourceSynthesisGeneralizeSyntax.top
        (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
        (.interned u.identity) (.node b rows 0 [.interned u.identity]) ∧
      let state : Machine String SourceSynthesisGeneralizeSyntax.Guard := ⟨final, Cache.emptyState⟩
      ∀ fuel,
        execute SourceSynthesisGeneralizeSyntax.top SourceEqualityPCSNativeEdge.conjoin (fuel + 5)
          IntersectionEmptyDomain.emptyDomain (.reference (.interned u.identity))
          (.mu u (.node b rows 0 [.interned u.identity]) depth ordinary) state =
        ((node SourceSynthesisGeneralizeSyntax.top SourceEqualityPCSNativeEdge.conjoin
          (execute SourceSynthesisGeneralizeSyntax.top SourceEqualityPCSNativeEdge.conjoin fuel
            (second u b rows depth ordinary state).1)
          rows rows (secondState u b rows depth ordinary state)).bind
          (fun value after => construction
            (SourceRecursiveIntersectionMaybeMu.maybeMu (pair b.identity u.identity) value after.heap) after)).bind
          (fun value after => construction
            (SourceRecursiveIntersectionMaybeMu.maybeMu (pair u.identity u.identity) value after.heap) after) := by
  obtain ⟨u, body, depth, ordinary, final, done, facts, available, shape, _⟩ :=
    SourceSynthesisUniverseColdReadback.typesOf_cold_mu lib query
  have originalShape := shape
  obtain ⟨b, marker, arrow, rest, bodyEq, _⟩ := shape
  subst body
  refine ⟨u, b, _, depth, ordinary, final, done, facts, available, originalShape, ?_⟩
  dsimp only
  intro fuel
  exact reference_to_rows u b _ depth ordinary SourceSynthesisGeneralizeSyntax.top
    SourceEqualityPCSNativeEdge.conjoin ⟨final, Cache.emptyState⟩ facts Cache.empty_valid available fuel

end MicroCFTA.SourceSynthesisUniverseColdKernelEntry
