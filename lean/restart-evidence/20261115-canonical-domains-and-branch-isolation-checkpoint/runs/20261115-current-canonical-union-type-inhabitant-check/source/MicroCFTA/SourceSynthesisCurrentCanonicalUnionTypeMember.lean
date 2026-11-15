import MicroCFTA.SourceSynthesisCurrentNativeUniverseMembership
import MicroCFTA.SourceSynthesisCurrentUniverseClosedMuClassification
import MicroCFTA.SourceCurrentRequiredUnionNormal
import MicroCFTA.InternedFreshOrdinaryNormal

/-!
# A finite Type member of an actual canonical union

A closed canonical union has a direct Mu member. Source normalization removes
empty members, flattens nested unions, and merges all ordinary members.
Only-U atoms identify that direct Mu as the complete original stored U.
The resulting finite member belongs to the actual union handle.
-/
namespace MicroCFTA.SourceSynthesisCurrentCanonicalUnionTypeMember
open Language Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedStoredMuOrigins (Normal)
open InternedBoundaryAtoms (atoms many_member)
open InternedBinderProtocol (NodeKey NodeRef)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
open SourcePruningEnumerationNativeLanguage (handles)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

private theorem all_nodes_ordinary_edges (values : List (Value Symbol Guard))
    (allNodes : ∀ value ∈ values, ∃ entry edges depth free,
      value = Value.node entry edges depth free) :
    ∃ edges, ordinaryEdges values = some edges := by
  induction values with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
      obtain ⟨entry, edges, depth, free, same⟩ := allNodes first List.mem_cons_self
      obtain ⟨tailEdges, tail⟩ := ih
        (fun value member => allNodes value (List.mem_cons_of_mem _ member))
      refine ⟨edges ++ tailEdges, ?_⟩
      simp only [same, ordinaryEdges, tail, Option.map_some]

/-- A closed available canonical union has an actual direct available Mu member. -/
theorem closed_canonical_union_mu_member
    (heap : State Symbol Guard) (normal : Normal heap)
    (irreducible : SourceCurrentRequiredUnionNormal.UnionNormal heap)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (available : Available heap (.union entry members depth free))
    (closed : (Value.union entry members depth free).free = []) :
    ∃ other body otherDepth ordinary,
      Value.mu other body otherDepth ordinary ∈ members ∧
      Available heap (.mu other body otherDepth ordinary) := by
  classical
  have flat := InternedUnionNormalForm.resident_flat heap normal.flat
    (.union entry members depth free) available.resident
  have nonempty := InternedUnionNonemptyMembers.resident_membersNonempty heap normal.members
    (.union entry members depth free) available.resident
  have noOrdinary : ordinaryEdges members = none :=
    irreducible entry.key (.union entry members depth free) (available.resident entry rfl)
  by_contra missing
  have allNodes : ∀ value ∈ members, ∃ other edges otherDepth otherFree,
      value = Value.node other edges otherDepth otherFree := by
    intro value present
    cases value with
    | empty => exact False.elim (nonempty .empty present rfl)
    | reference name =>
        have occurrence : NodeRef.ref name ∈ atoms (.union entry members depth free) :=
          (many_member members (.ref name)).mpr
            ⟨.reference name, present, by simp only [atoms, List.mem_singleton]⟩
        have escaped := InternedBoundaryProvenance.ref_free name
          (.union entry members depth free) heap normal.facts.coherent available occurrence
        simp only [closed, List.not_mem_nil] at escaped
    | node other edges otherDepth otherFree => exact ⟨other, edges, otherDepth, otherFree, rfl⟩
    | union other otherMembers otherDepth otherFree => exact False.elim (flat _ present)
    | mu other body otherDepth ordinary =>
        exact False.elim (missing ⟨other, body, otherDepth, ordinary, present,
          available.children _ present⟩)
  obtain ⟨edges, ordinary⟩ := all_nodes_ordinary_edges members allNodes
  rw [noOrdinary] at ordinary
  cases ordinary

/-- Only-U atoms in a canonical grown union give a finite member of that exact union handle. -/
theorem grown_union_original_universe_type_members
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
    (heap : State Symbol Guard) (normal : Normal heap)
    (irreducible : SourceCurrentRequiredUnionNormal.UnionNormal heap)
    (growth : Grows sourceHeap heap)
    (unionEntry : Interned NodeKey) (members : List (Value Symbol Guard))
    (unionDepth : Nat) (unionFree : List InternedBinderProtocol.Reference)
    (available : Available heap (.union unionEntry members unionDepth unionFree))
    (onlyU : ∀ atom ∈ atoms (.union unionEntry members unionDepth unionFree),
      atom = .mu entry.identity) :
    Value.mu entry body depth ordinary ∈ members ∧
      ∃ handle,
        encodeNode (.union unionEntry members unionDepth unionFree) = some handle ∧
        lookupNode heap handle = some (.union unionEntry members unionDepth unionFree) ∧
        ∀ term, TypeIn (SourceSynthesisCurrentContext.constructorCatalog lib query) term →
          handles (SourceEqualityPCSGuard.holds formulas solver) ambient heap handle term := by
  have closed :=
    SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_boundary_atoms_closed_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap normal.facts growth (.union unionEntry members unionDepth unionFree) available onlyU
  obtain ⟨other, otherBody, otherDepth, otherOrdinary, present, otherAvailable⟩ :=
    closed_canonical_union_mu_member heap normal irreducible unionEntry members
      unionDepth unionFree available closed
  have otherOnly : ∀ atom ∈ atoms (.mu other otherBody otherDepth otherOrdinary),
      atom = .mu entry.identity := by
    intro atom occurrence
    exact onlyU atom ((many_member members atom).mpr
      ⟨.mu other otherBody otherDepth otherOrdinary, present, occurrence⟩)
  have otherClosed :=
    SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_boundary_atoms_closed_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap normal.facts growth (.mu other otherBody otherDepth otherOrdinary) otherAvailable otherOnly
  have same := SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap normal.facts growth other otherBody otherDepth otherOrdinary
      otherAvailable otherClosed otherOnly
  have originalMember : Value.mu entry body depth ordinary ∈ members := by
    rw [← same]
    exact present
  obtain ⟨handle, encoded, readback⟩ := SourcePruningEnumerationNodes.available_readback
    heap (.union unionEntry members unionDepth unionFree) normal.facts.coherent available closed
  obtain ⟨_originalAvailable, _originalClosed, originalLanguage⟩ :=
    SourceSynthesisCurrentNativeUniverseMembership.original_stored_universe_language
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
  refine ⟨originalMember, handle, encoded, readback, ?_⟩
  intro term admitted
  refine ⟨.union unionEntry members unionDepth unionFree, readback, ?_⟩
  change ∃ member : {member // member ∈ members},
    InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
      ambient member.val term
  refine ⟨⟨.mu entry body depth ordinary, originalMember⟩, ?_⟩
  rw [originalLanguage]
  exact admitted.member (SourceEqualityPCSGuard.holds formulas solver)
    (SourceEqualityPCSConstructors.top_true formulas solver)

/-- The actual original source heap supplies all union invariants and a concrete var1 member. -/
theorem source_closed_union_finite_type_member
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
    (unionEntry : Interned NodeKey) (members : List (Value Symbol Guard))
    (unionDepth : Nat) (unionFree : List InternedBinderProtocol.Reference)
    (available : Available sourceHeap (.union unionEntry members unionDepth unionFree))
    (closed : (Value.union unionEntry members unionDepth unionFree).free = []) :
    Value.mu entry body depth ordinary ∈ members ∧
      ∃ handle,
        encodeNode (.union unionEntry members unionDepth unionFree) = some handle ∧
        lookupNode sourceHeap handle = some (.union unionEntry members unionDepth unionFree) ∧
        TypeIn (SourceSynthesisCurrentContext.constructorCatalog lib query)
          (.node (literal "var1") []) ∧
        handles (SourceEqualityPCSGuard.holds formulas solver) ambient sourceHeap handle
          (.node (literal "var1") []) := by
  have normal : Normal sourceHeap := by
    simpa only [built, Outcome.state] using
      InternedFreshOrdinaryNormal.closed_normal (ordinarySymbols whole)
  have irreducible : SourceCurrentRequiredUnionNormal.UnionNormal sourceHeap := by
    simpa only [built, Outcome.state] using
      SourceCurrentRequiredUnionNormal.source (ordinarySymbols whole)
  have onlyU := SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_startup_value_atoms
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      (.union unionEntry members unionDepth unionFree) available closed
  obtain ⟨originalMember, handle, encoded, readback, acceptedTerms⟩ :=
    grown_union_original_universe_type_members formulas solver ambient lib query signed whole accepted
      rootValue sourceHeap built key entry body depth ordinary stored sourceHeap normal irreducible
      (grows_refl sourceHeap) unionEntry members unionDepth unionFree available onlyU
  have finite : TypeIn (SourceSynthesisCurrentContext.constructorCatalog lib query)
      (.node (literal "var1") []) := .leaf "var1" (by simp)
  exact ⟨originalMember, handle, encoded, readback, finite, acceptedTerms _ finite⟩

/-- A source heap without Mu records has no closed available explicit union. -/
theorem source_without_mu_no_closed_union
    [DecidableEq (EdgeKey Symbol Guard)]
    (whole : Expression) (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (noMu : ∀ key entry body depth ordinary,
      sourceHeap.nodeRecords key ≠ some (.mu entry body depth ordinary))
    (unionEntry : Interned NodeKey) (members : List (Value Symbol Guard))
    (unionDepth : Nat) (unionFree : List InternedBinderProtocol.Reference)
    (available : Available sourceHeap (.union unionEntry members unionDepth unionFree))
    (closed : (Value.union unionEntry members unionDepth unionFree).free = []) : False := by
  have normal : Normal sourceHeap := by
    simpa only [built, Outcome.state] using
      InternedFreshOrdinaryNormal.closed_normal (ordinarySymbols whole)
  have irreducible : SourceCurrentRequiredUnionNormal.UnionNormal sourceHeap := by
    simpa only [built, Outcome.state] using
      SourceCurrentRequiredUnionNormal.source (ordinarySymbols whole)
  obtain ⟨entry, body, depth, ordinary, _present, actual⟩ :=
    closed_canonical_union_mu_member sourceHeap normal irreducible unionEntry members
      unionDepth unionFree available closed
  exact noMu entry.key entry body depth ordinary (actual.resident entry rfl)

end MicroCFTA.SourceSynthesisCurrentCanonicalUnionTypeMember

#print axioms MicroCFTA.SourceSynthesisCurrentCanonicalUnionTypeMember.closed_canonical_union_mu_member
#print axioms MicroCFTA.SourceSynthesisCurrentCanonicalUnionTypeMember.grown_union_original_universe_type_members
#print axioms MicroCFTA.SourceSynthesisCurrentCanonicalUnionTypeMember.source_closed_union_finite_type_member
#print axioms MicroCFTA.SourceSynthesisCurrentCanonicalUnionTypeMember.source_without_mu_no_closed_union
