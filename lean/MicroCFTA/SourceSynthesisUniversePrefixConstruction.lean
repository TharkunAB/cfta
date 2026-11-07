import MicroCFTA.SourceSynthesisUniversePrefixLists
import MicroCFTA.SourceSynthesisUniverseOrigins
import MicroCFTA.SourceSynthesisUniversePrefixReadback

/-!
# Actual finite prefixes over the first constructed universe

The proof follows source-order construction from the original empty cache.
It captures the first actual universe and replays that same value later.
Ordinary and union layers have a bound from the original instruction syntax.
A prefix with no universe atom does not require a resident universe witness.
Generated intersection and driver preservation remain separate obligations.
-/
namespace MicroCFTA.SourceSynthesisUniversePrefixConstruction
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedBoundaryAtoms
open SourceSynthesisUniversePrefixSeed
open SourceSynthesisUniversePrefixLists
open SourceSynthesisUniversePrefixHeight
open SourceSynthesisUniverseOrigins (OverUniverse Children)
open SourceSynthesisTypeSyntax
open SourceSynthesisFirstOrderConstruction (Expression Row)
open SourceSynthesisGeneralizeSyntax (Guard top)

variable [DecidableEq (EdgeKey String Guard)]

private theorem allowed_of_origin {catalog : List (String × Nat)}
    {pick : Option (Seed top catalog)} {value : Value String Guard}
    (origin : ∀ item ∈ atoms value, ∃ child, Allowed pick child ∧ item ∈ atoms child) : Allowed pick value := by
  cases pick <;> intro item occurrence <;>
    obtain ⟨child, allowed, found⟩ := origin item occurrence <;>
    exact allowed item found

private theorem atom_returns (catalog : List (String × Nat)) : Returns top catalog (allTypes top catalog) := by
  intro pick state facts covered ready
  obtain ⟨seed, after, done, nextReady, advance, allowed, _growth⟩ :=
    atom_complete top catalog pick state facts covered ready
  exact ⟨seed.value, after, some seed, done, nextReady, advance, allowed,
    by change 0 ≤ sizeOf (allTypes top catalog); exact Nat.zero_le _⟩

private theorem node_returns (catalog : List (String × Nat)) (rows : List Row)
    (checked : ∀ row ∈ rows, Children (Returns top catalog) row) : Returns top catalog (.node rows) := by
  intro pick state facts covered ready
  obtain ⟨values, after, next, done, nextReady, advance, allowed, bounded⟩ :=
    edges_returns top catalog rows (by
      intro row member
      cases row
      exact checked _ member) pick state facts covered ready
  have verified := InternedFreshOrdinaryFacts.buildEdges_verified rows [] state facts
    (by intro value member; cases member)
  have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
  have resident := verified.result values after done
  let result := run (makeNode values) after
  have resultReady : Ready next result.2 :=
    ready_makeNode next values after afterFacts.coherent.valid nextReady
  have resultAllowed : Allowed next result.1 := by
    apply allowed_of_origin
    intro item occurrence
    have source := makeNode_atom_origin values after afterFacts.coherent afterFacts.linked resident item occurrence
    obtain ⟨edge, member, child, included, found⟩ := (edge_member values item).mp source
    exact ⟨child, allowed edge member child included, found⟩
  have resultBound : height result.1 ≤ sizeOf (Syntax.node rows) := by
    have bound := makeNode_bound values after afterFacts resident (sizeOf rows + 1) (by
      intro edge member
      have own := (edgesHeight_le values (edgesHeight values)).mp (Nat.le_refl _) edge member
      omega)
    dsimp only [result]
    rw [Syntax.node.sizeOf_spec]
    omega
  exact ⟨result.1, result.2, next, by
    simp only [InternedFreshOrdinaryConstruction.build, done, Outcome.bind, work]
    rfl, resultReady, advance, resultAllowed, resultBound⟩

private theorem union_returns (catalog : List (String × Nat)) (members : List Expression)
    (checked : ∀ member ∈ members, Returns top catalog member) : Returns top catalog (.union members) := by
  intro pick state facts covered ready
  obtain ⟨values, after, next, done, nextReady, advance, allowed, bounded⟩ :=
    many_returns top catalog members checked pick state facts covered ready
  have verified := InternedFreshOrdinaryFacts.buildMany_verified members [] state facts
    (by intro value member; cases member)
  have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
  have available := verified.result values after done
  let result := run (makeUnion values) after
  have resultReady : Ready next result.2 :=
    ready_makeUnion next values after afterFacts.coherent.valid nextReady
  have resultAllowed : Allowed next result.1 := by
    apply allowed_of_origin
    intro item occurrence
    obtain ⟨value, member, found⟩ := makeUnion_atom_origin values after afterFacts.coherent
      afterFacts.cached afterFacts.linked available item occurrence
    exact ⟨value, allowed value member, found⟩
  have resultBound : height result.1 ≤ sizeOf (Syntax.union members) := by
    have bound := makeUnion_bound values after afterFacts available
    dsimp only [result]
    rw [Syntax.union.sizeOf_spec]
    omega
  exact ⟨result.1, result.2, next, by
    simp only [InternedFreshOrdinaryConstruction.build, done, Outcome.bind, work]
    rfl, resultReady, advance, resultAllowed, resultBound⟩

/-- Every source prefix derives its actual selected universe and its instruction-size height bound. -/
theorem overUniverse_returns (catalog : List (String × Nat)) (expression : Expression)
    (origin : OverUniverse (allTypes top catalog) expression) : Returns top catalog expression := by
  induction origin with
  | atom => exact atom_returns catalog
  | node rows _ children => exact node_returns catalog rows children
  | union members _ children => exact union_returns catalog members children

/-- Empty-cache execution derives every seed condition and complete actual output records. -/
theorem overUniverse_prefix_bound (catalog : List (String × Nat)) (expression : Expression)
    (origin : OverUniverse (allTypes top catalog) expression) :
    ∃ value final, ∃ pick : Option (Seed top catalog),
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value final ∧
      Facts final ∧ Available final value ∧ Ready pick final ∧ Allowed pick value ∧
      height value ≤ sizeOf expression := by
  obtain ⟨value, final, pick, done, ready, _advance, allowed, bounded⟩ :=
    overUniverse_returns catalog expression origin none empty empty_facts
      InternedRecordCoherence.empty_correct.2 (InternedShallowHeap.noNewMu_refl empty)
  have verified := InternedFreshOrdinaryFacts.closed_verified expression
  have finalFacts : Facts final := by simpa only [done, Outcome.state] using verified.facts
  exact ⟨value, final, pick, done, finalFacts, verified.result value final done, ready, allowed, bounded⟩

/-- Original signed synthesis requests retain errors and derive the actual physical prefix bound on success. -/
theorem firstOrderRaw_prefix_bound (lib : Library) (query : Query) (size : Int) :
    match SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression =>
        ∃ value final pick,
          InternedFreshOrdinaryConstruction.build expression [] empty = .done value final ∧
          Facts final ∧ Available final value ∧
          Ready (top := top) (catalog := SourceSynthesisFirstOrderConstruction.constructorCatalog lib query) pick final ∧
          Allowed pick value ∧ height value ≤ sizeOf expression := by
  cases returned : SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
  | error => trivial
  | ok expression =>
      exact overUniverse_prefix_bound _ expression
        (SourceSynthesisUniverseOrigins.firstOrderRaw_overUniverse lib query size expression returned)


/-- Original requests derive complete final universe records as well as the physical prefix bound. -/
theorem firstOrderRaw_physical_prefix_bound (lib : Library) (query : Query) (size : Int) :
    match SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression =>
        ∃ value final,
          InternedFreshOrdinaryConstruction.build expression [] empty = .done value final ∧
          Facts final ∧ Available final value ∧ height value ≤ sizeOf expression ∧
          (atoms value = [] ∨ ∃ entry body depth ordinary,
            Available final (.mu entry body depth ordinary) ∧
            SourceSynthesisUniverseBody.Shape top
              (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query) (.interned entry.identity) body ∧
            SourceSynthesisUniverseResidentRows.Rows top
              (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query) (.interned entry.identity) body final ∧
            SourceSynthesisUniverseResidentRows.Rows top
              (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query) .depth depth final ∧
            SourceSynthesisUniverseResidentRows.Rows top
              (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
              (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) ordinary final ∧
            ∀ item ∈ atoms value, item = .mu entry.identity) := by
  cases returned : SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
  | error => trivial
  | ok expression =>
      have derived := firstOrderRaw_prefix_bound lib query size
      rw [returned] at derived
      obtain ⟨value, final, pick, done, facts, available, ready, allowed, bounded⟩ := derived
      refine ⟨value, final, done, facts, available, bounded, ?_⟩
      cases pick with
      | none =>
          left
          cases same : atoms value with
          | nil => rfl
          | cons first rest =>
              exact False.elim (allowed first (by simp only [same, List.mem_cons_self]))
      | some seed =>
          right
          obtain ⟨bodyRows, depthRows, ordinaryRows⟩ := seed.rows_after final ready
          exact ⟨seed.entry, seed.body, seed.depth, seed.ordinary, seed.available_after final facts ready,
            seed.body_shape, bodyRows, depthRows, ordinaryRows, allowed⟩

end MicroCFTA.SourceSynthesisUniversePrefixConstruction
