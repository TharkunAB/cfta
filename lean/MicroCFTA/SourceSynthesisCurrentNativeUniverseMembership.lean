import MicroCFTA.SourceSynthesisCurrentUniverseOwnership
import MicroCFTA.InternedGuardedExecution
import MicroCFTA.SourcePruningEnumerationSharedProperPathWitness
import MicroCFTA.SourcePruningEnumerationNativeLanguage
import MicroCFTA.SourceEqualityPCSConstructors

/-!
# Finite members of the same original stored universe

The accepted original build supplies the actual stored universe and its
language. Earlier cache entries and issued history preserve its native handle.
The two finite terms used by the proper-path assignment belong to this handle.
These laws do not establish membership in arbitrary narrowed domains.
-/
namespace MicroCFTA.SourceSynthesisCurrentNativeUniverseMembership
open Language Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (NodeKey)
open SourceSynthesisTypeSyntax (Library Query allTypes)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
open SourcePruningEnumerationNativeLanguage (handles)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- The same stored universe has the language of the accepted source's Type syntax. -/
theorem original_stored_universe_language
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary)) :
    Available sourceHeap (.mu entry body depth ordinary) ∧
      (Value.mu entry body depth ordinary).free = [] ∧
      ∀ (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol),
        InternedGuardedLanguage.meaning holds ambient (.mu entry body depth ordinary) =
          InternedGuardedSyntax.evaluate holds [] (mapSyntax literal
            (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query))) := by
  have sourceContext : InternedFreshOrdinaryContext.Context sourceHeap [] := by
    simpa only [built, Outcome.state] using
      InternedFreshOrdinaryContext.empty_context.build (ordinarySymbols whole)
  have sourceLanguages : InternedGuardedProbeHeap.Heap sourceHeap := by
    simpa only [built, Outcome.state] using
      InternedGuardedExecution.closed_heap (ordinarySymbols whole)
  rcases SourceSynthesisCurrentUniverseOwnership.current_build_single_universe
      lib query signed whole accepted rootValue sourceHeap built with absent | canonical
  · exact False.elim (absent key entry body depth ordinary stored)
  · obtain ⟨canonicalEntry, canonicalBody, canonicalDepth, canonicalOrdinary,
      _canonicalStored, canonicalAvailable, canonicalClosed, replay, unique⟩ := canonical
    have same : Value.mu entry body depth ordinary =
        .mu canonicalEntry canonicalBody canonicalDepth canonicalOrdinary :=
      unique key entry body depth ordinary stored
    have available : Available sourceHeap (.mu entry body depth ordinary) := by
      rw [same]
      exact canonicalAvailable
    have closed : (Value.mu entry body depth ordinary).free = [] := by
      rw [same]
      exact canonicalClosed
    refine ⟨available, closed, ?_⟩
    intro holds ambient
    have replayed := replay sourceHeap (grows_refl sourceHeap)
    rw [← same] at replayed
    have exactLanguage :=
      (InternedGuardedExecution.build_language
        (ordinarySymbols ((SourceSynthesisCurrentContext.context lib query).types))
        [] sourceHeap sourceContext sourceLanguages).result
          (.mu entry body depth ordinary) sourceHeap replayed holds ambient
    change InternedGuardedLanguage.meaning holds ambient (.mu entry body depth ordinary) =
      InternedGuardedSyntax.evaluate holds [] (ordinarySymbols
        (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query))) at exactLanguage
    rw [← SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] at exactLanguage
    exact exactLanguage

/-- Cache growth and issued history preserve a successful native lookup. -/
private theorem lookupNode_growth
    (before after : State Symbol Guard) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued)
    (node : Nat) (value : Value Symbol Guard)
    (present : lookupNode before node = some value) : lookupNode after node = some value := by
  cases node with
  | zero => exact present
  | succ identity =>
      cases issued : before.nodes.issued identity with
      | none =>
          simp only [lookupNode, issued] at present
          cases present
      | some key =>
          cases canonical : before.nodes.table key with
          | none =>
              simp only [lookupNode, issued, canonical] at present
              cases present
          | some entry =>
              by_cases winner : entry.identity = identity
              · simp only [lookupNode, issued, canonical, ite_eq_left winner] at present
                simpa only [lookupNode, history identity key issued,
                  growth.nodes key entry canonical, ite_eq_left winner] using
                    growth.nodeRecords key value present
              · simp only [lookupNode, issued, canonical, ite_eq_right winner] at present
                cases present

/-- Structural Type admission supplies membership in the same original native U handle. -/
theorem typeIn_original_universe_handle
    [DecidableEq FullSyntax.Formula] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : State Symbol Guard) (growth : Grows sourceHeap heap)
    (history : Extends sourceHeap.nodes.issued heap.nodes.issued) :
    ∃ handle,
      encodeNode (.mu entry body depth ordinary) = some handle ∧
      lookupNode sourceHeap handle = some (.mu entry body depth ordinary) ∧
      lookupNode heap handle = some (.mu entry body depth ordinary) ∧
      ∀ term, TypeIn (SourceSynthesisCurrentContext.constructorCatalog lib query) term →
        handles (SourceEqualityPCSGuard.holds formulas solver) ambient heap handle term := by
  obtain ⟨available, closed, language⟩ := original_stored_universe_language
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
  have sourceContext : InternedFreshOrdinaryContext.Context sourceHeap [] := by
    simpa only [built, Outcome.state] using
      InternedFreshOrdinaryContext.empty_context.build (ordinarySymbols whole)
  obtain ⟨handle, encoded, readback⟩ := SourcePruningEnumerationNodes.available_readback
    sourceHeap (.mu entry body depth ordinary) sourceContext.normal.facts.coherent available closed
  have laterReadback := lookupNode_growth sourceHeap heap growth history
    handle (.mu entry body depth ordinary) readback
  refine ⟨handle, encoded, readback, laterReadback, ?_⟩
  intro term admitted
  apply (SourcePruningEnumerationNativeLanguage.handles_lookup
    (SourceEqualityPCSGuard.holds formulas solver) ambient heap handle
    (.mu entry body depth ordinary) term laterReadback).mpr
  rw [language]
  exact admitted.member (SourceEqualityPCSGuard.holds formulas solver)
    (SourceEqualityPCSConstructors.top_true formulas solver)

/-- Use the same two finite terms as the selected proper-path witness. -/
noncomputable def properPathAssignment (representatives : UnionFind.Forest)
    (uv slot : Nat) : Term Symbol := by
  classical
  exact if UnionFind.SameClass representatives uv slot then
    .node (literal "->") [.node (literal "(->)") [],
      .node (literal "var1") [], .node (literal "var1") []]
  else .node (literal "var1") []

/-- Every value of the proper-path assignment belongs to the original native U. -/
theorem proper_path_assignment_original_universe
    [DecidableEq FullSyntax.Formula] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : State Symbol Guard) (growth : Grows sourceHeap heap)
    (history : Extends sourceHeap.nodes.issued heap.nodes.issued)
    (representatives : UnionFind.Forest) (uv : Nat) :
    ∃ handle,
      encodeNode (.mu entry body depth ordinary) = some handle ∧
      lookupNode sourceHeap handle = some (.mu entry body depth ordinary) ∧
      lookupNode heap handle = some (.mu entry body depth ordinary) ∧
      ∀ slot, handles (SourceEqualityPCSGuard.holds formulas solver) ambient heap handle
        (properPathAssignment representatives uv slot) := by
  classical
  obtain ⟨handle, encoded, originalReadback, readback, members⟩ :=
    typeIn_original_universe_handle formulas solver ambient lib query signed whole accepted
      rootValue sourceHeap built key entry body depth ordinary stored heap growth history
  refine ⟨handle, encoded, originalReadback, readback, ?_⟩
  intro slot
  have base : TypeIn (SourceSynthesisCurrentContext.constructorCatalog lib query)
      (.node (literal "var1") []) := .leaf "var1" (by simp)
  unfold properPathAssignment
  by_cases same : UnionFind.SameClass representatives uv slot
  · simp only [ite_eq_left same]
    exact members _ (TypeIn.arrow _ _ base base)
  · simp only [ite_eq_right same]
    exact members _ base

end MicroCFTA.SourceSynthesisCurrentNativeUniverseMembership
