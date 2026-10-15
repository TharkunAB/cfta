import MicroCFTA.SourceEqualityProjectionRead
import MicroCFTA.SourceEqualityNativeDemandFieldHeap
import MicroCFTA.MergedFreshOrdinaryConstraintHeap
import MicroCFTA.ConservativeEmptinessRows

/-!
# Accepted rows of actual conservative emptiness exposure

The source reads nodeEdges and removes contradictory equality payloads.
Complete guard acceptance supplies satisfaction of the actual equalities
accessor, including positive guard extraction. Actual resident fields supply
normalized nontrivial classes. No accepted-row oracle is assumed.
-/
namespace MicroCFTA.SourceEmptinessExposure
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionRead
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap

/-- Read the actual accessor classes in their stored order, without subsumption sorting. -/
noncomputable def row (edge : EdgeValue Symbol Guard) : ConservativeEmptinessRows.Row (Value Symbol Guard) :=
  ⟨edge.children, (SourceCompactGuards.sourceEqualities edge.entry.key.constraint).getD []⟩

/-- Keep source row order and omit exactly the contradictory accessor results. -/
noncomputable def rows (edges : List (EdgeValue Symbol Guard)) : List (ConservativeEmptinessRows.Row (Value Symbol Guard)) :=
  (edges.filter (fun edge => (SourceCompactGuards.sourceEqualities edge.entry.key.constraint).isSome)).map row

/-- Every actual closed row read retains normalized stored equality fields. -/
theorem read_fields [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : Read value before edges after) (semantic : SemanticReady before) (fields : FieldHeap before)
    (available : Available before value) (closed : value.free = []) : FieldHeap after := by
  cases trace with
  | done fuel completed =>
      simpa only [SourceEqualityNativeDemandFieldHeap.Heap, completed, MergedSourceExposure.Result.state] using
        MergedFreshOrdinaryConstraintHeap.nodeEdges_heap
          (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities) fuel value before
          semantic.ready.semantic semantic.ready.covered fields available closed

/-- Actual complete guard acceptance survives the filter with its normalized original classes. -/
theorem accepted_row (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env Symbol)
    (edges : List (EdgeValue Symbol Guard)) (edge : EdgeValue Symbol Guard) (member : edge ∈ edges)
    (cached : SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities)
    (term : Term Symbol)
    (accepted : MergedColdInterpretation.EdgeMeaning (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
      (SourceEqualityPCSGuard.holds formulas solver) edge term) :
    row edge ∈ rows edges ∧ Active (row edge).classes ∧ Satisfies term (row edge).classes ∧
      ∃ terms, term = .node edge.entry.key.symbol terms ∧
        All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) (row edge).children terms := by
  obtain ⟨terms, shape, forest, guard⟩ := accepted
  have own := SourceEqualityPCSGuard.own_sat formulas solver edge.entry.key.constraint term guard
  cases extracted : SourceCompactGuards.sourceEqualities edge.entry.key.constraint with
  | none => simp only [extracted, SourceEqualityGuardReadback.Sat] at own
  | some classes =>
      have active := (SourceEqualityGuardReadback.source_cached edge.entry.key.constraint cached classes extracted).1
      have rowClasses : (row edge).classes = classes := by simp only [row, extracted, Option.getD_some]
      refine ⟨List.mem_map.mpr ⟨edge, List.mem_filter.mpr ⟨member, by simp only [extracted, Option.isSome_some]⟩, rfl⟩,
        ?_, ?_, terms, shape, forest⟩
      · simpa only [rowClasses] using active
      · simpa only [rowClasses, extracted, SourceEqualityGuardReadback.Sat] using own

/-- A concrete nodeEdges read supplies an accepted retained row and every class premise needed by emptiness. -/
theorem read_witness [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : Read value before edges after) (semantic : SemanticReady before) (fields : FieldHeap before)
    (available : Available before value) (closed : value.free = [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
    (accepted : meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term) :
    ∃ edge ∈ edges, row edge ∈ rows edges ∧ Active (row edge).classes ∧ Satisfies term (row edge).classes ∧
      ∃ terms, term = .node edge.entry.key.symbol terms ∧
        All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) (row edge).children terms := by
  have checked := trace.verified semantic available closed
  have afterFields := read_fields trace semantic fields available closed
  obtain ⟨edge, member, edgeAccepted⟩ :=
    (trace.exact semantic available closed (SourceEqualityPCSGuard.holds formulas solver) ambient term).mpr accepted
  have cached := SourceEqualityNativeDemandFieldHeap.resident_cached after afterFields edge (checked.2.2.1 edge member)
  exact ⟨edge, member, accepted_row formulas solver ambient edges edge member cached term edgeAccepted⟩

/-- Original closed construction derives finite row reads and accepted normalized rows from source syntax. -/
theorem source [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (annotations : InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities) expression)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ value before edges after, InternedFreshOrdinaryConstruction.build expression [] empty = .done value before ∧
      Read value before edges after ∧ Keeps before after ∧ SemanticReady after ∧ FieldHeap after ∧
      ∀ ambient term, InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver) [] expression term →
        ∃ edge ∈ edges, row edge ∈ rows edges ∧ Active (row edge).classes ∧ Satisfies term (row edge).classes ∧
          ∃ terms, term = .node edge.entry.key.symbol terms ∧
            All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) (row edge).children terms := by
  obtain ⟨value, before, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value before built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value before built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value before built
  have fields : FieldHeap before := by
    simpa only [SourceEqualityNativeDemandFieldHeap.Heap, built, InternedNestedConstruction.Outcome.state] using
      InternedFreshOrdinaryConstraintHeap.build_heap
        (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities) expression [] empty
        (InternedFreshOrdinaryConstraintHeap.empty_heap _) annotations
  obtain ⟨edges, after, trace, keeps, finalSemantic, _⟩ := SourceEqualityProjectionRead.complete value before semantic available closed
  refine ⟨value, before, edges, after, built, trace, keeps, finalSemantic,
    read_fields trace semantic fields available closed, ?_⟩
  intro ambient term accepted
  apply read_witness trace semantic fields available closed formulas solver ambient term
  simpa only [InternedGuardedExecution.closed_language expression value before built
    (SourceEqualityPCSGuard.holds formulas solver) ambient] using accepted

end MicroCFTA.SourceEmptinessExposure
