import MicroCFTA.SourceEqualityRequiredAPI
import MicroCFTA.SourceClosedGateCache
import MicroCFTA.SourceEqualitySelectionEntry

/-!
# Ordered source selection followed by required-path filtering

The path union uses ascending natural path-set order, then the signed source
indices. Actual closed gate traces derive the constructor cache supplied to
the required-path worker. The two stages retain their actual complete receipts.
-/
namespace MicroCFTA.SourceEqualitySelectedRequired
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredSemanticCache SourceEqualityRequiredAPI
open SourceEqualityRequiredWorkerComplete SourceEqualityRequiredExecution
open InternedSourceClassSelection (Query Trace selected select)
open InternedGuardedLanguage (meaning)

/-- Read the union of selected path sets in ascending order with signed source indices. -/
def paths (classes : EqualityNormalize.Constraints) : List SourceEqualityNeeded.Path :=
  (EqualityNormalize.canonicalClass classes.flatten).map (List.map Int.ofNat)

/-- Natural source selection paths derive every signed nonnegative-key premise. -/
theorem paths_nonnegative (classes : EqualityNormalize.Constraints) :
    ∀ path ∈ paths classes, ∀ index ∈ path, 0 ≤ index := by
  intro path member index included
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  obtain ⟨natural, _, rfl⟩ := List.mem_map.mp included
  simp

/-- Signed lookup of a normalized natural path is the original natural lookup. -/
theorem lookup_natural (term : Term Symbol) (path : EqualityNormalize.Path) :
    SymbolicSignedPaths.lookup term (path.map Int.ofNat) = term.atPath path := by
  have decoded : SymbolicSignedPaths.decode (path.map Int.ofNat) = some path := by
    induction path with
    | nil => rfl
    | cons index rest ih => simp [SymbolicSignedPaths.decode, ih]
  rw [SymbolicSignedPaths.lookup_decode, decoded, Option.bind_some]

/-- The ascending source union requires exactly the complete paths of every selected class. -/
theorem paths_exist (classes : EqualityNormalize.Constraints) (term : Term Symbol) :
    (∀ path ∈ paths classes, ∃ part, SymbolicSignedPaths.lookup term path = some part) ↔
      ∀ path ∈ classes.flatten, ∃ part, term.atPath path = some part := by
  constructor
  · intro allPaths path member
    have included : path.map Int.ofNat ∈ paths classes :=
      List.mem_map.mpr ⟨path, (EqualityNormalize.mem_canonicalClass path classes.flatten).mpr member, rfl⟩
    simpa only [lookup_natural] using allPaths _ included
  · intro allPaths path member
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    simpa only [lookup_natural] using allPaths original ((EqualityNormalize.mem_canonicalClass _ _).mp included)

/-- Complete actual stage receipts retain the selected path list and the returned cache between stages. -/
structure Execution [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (classes : EqualityNormalize.Constraints)
    (before : State Symbol Guard) (queries : List (Query Symbol Guard))
    (middle : State Symbol Guard) (results : List (Value Symbol Guard)) (after : State Symbol Guard) : Prop where
  selection : Trace unconstrained values classes before queries middle
  required : ∃ fuel readFuel, requireAll fuel readFuel (paths (selected queries)) values middle = .done results after

/-- The paired actual stages derive the final semantic cache and exact required forest language. -/
theorem exact [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {values classes before queries middle results after}
    (trace : Execution unconstrained values classes before queries middle results after)
    (semantic : SemanticReady before) (available : Values before values) (closed : ClosedValues values) :
    SemanticReady after ∧ ∀ holds ambient terms, All₂ (meaning holds ambient) results terms ↔
      All₂ (meaning holds ambient) values terms ∧ ForestRequired (paths (selected queries)) terms := by
  have same := SourceClosedGateCache.selection_state trace.selection semantic.ready.semantic.1.normal.facts available closed
  cases same
  obtain ⟨fuel, readFuel, done⟩ := trace.required
  have graph := (requireAll_execution_iff _ _ _ _ _).mpr ⟨fuel, readFuel, done⟩
  have afterSemantic : SemanticReady after := by
    cases compiled : SourceEqualityNeeded.build (paths (selected queries)) with
    | node entries =>
        simp only [compiled] at graph
        exact SourceEqualityRequiredSemanticEffects.children graph semantic available closed
  exact ⟨afterSemantic, requireAll_done fuel readFuel _ values results before after done
    (paths_nonnegative _) semantic available closed⟩

/-- Actual selected requirements derive both narrowing and preservation laws used by the pure source pass. -/
theorem narrow_keep [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {values classes before queries middle results after}
    (trace : Execution unconstrained values classes before queries middle results after)
    (semantic : SemanticReady before) (available : Values before values) (closed : ClosedValues values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) :
    (All₂ (meaning holds ambient) results terms → All₂ (meaning holds ambient) values terms) ∧
      (All₂ (meaning holds ambient) values terms →
        (∀ path ∈ (selected queries).flatten, ∃ part, (Term.node symbol terms).atPath path = some part) →
          All₂ (meaning holds ambient) results terms) := by
  refine ⟨fun accepted => ((exact trace semantic available closed).2 holds ambient terms).mp accepted |>.1, ?_⟩
  intro accepted allPaths
  have same := SourceClosedGateCache.selection_state trace.selection semantic.ready.semantic.1.normal.facts available closed
  cases same
  obtain ⟨fuel, readFuel, done⟩ := trace.required
  exact requireAll_keep fuel readFuel _ values results before after done (paths_nonnegative _)
    semantic available closed holds ambient symbol terms accepted ((paths_exist _ _).mpr allPaths)

open SourceObservations SourceSymbolicIndex EqualityNormalize
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained

/-- Both actual source memos and finite stage bounds compose on each ready closed source forest. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (node : InternedFreshOrdinaryGateRank.Node Symbol Guard)
    (values : List (Value Symbol Guard)) (classes : Constraints)
    (semantic : SemanticReady node.state) (available : Values node.state values) (closed : ClosedValues values) :
    ∃ bound queries, ∃ middle : InternedFreshOrdinaryGateRank.Node Symbol Guard, ∃ results after,
      ∃ unfolding predicate, ∃ trace : Execution source values classes node.state queries middle.state results after,
        SourceMemoClassSelection.Reads values trace.selection InternedFreshOrdinaryUnfoldMemo.empty SourceUnconstrainedMemo.empty unfolding predicate ∧
        SourcePredicateGateTrace.Keeps node.state middle.state unfolding predicate ∧ SemanticReady after ∧
        (∀ extra, select source (bound + extra) values classes node.state = .done (some (selected queries)) middle.state) ∧
        StableRun (fun fuel readFuel => requireAll fuel readFuel (paths (selected queries)) values middle.state) results after := by
  obtain ⟨bound, queries, middle, unfolding, predicate, selection, reads, kept, stable⟩ :=
    SourceMemoClassSelection.complete node values available classes InternedFreshOrdinaryUnfoldMemo.empty
      (InternedFreshOrdinaryUnfoldMemo.empty_correct node.state) SourceUnconstrainedMemo.empty
      (SourceUnconstrainedMemo.empty_correct node.state)
  have same := SourceClosedGateCache.selection_state selection semantic.ready.semantic.1.normal.facts available closed
  have middleSemantic : SemanticReady middle.state := same ▸ semantic
  have middleAvailable : Values middle.state values := same ▸ available
  obtain ⟨results, after, _, afterSemantic, _, _, requiredStable, _⟩ :=
    SourceEqualityRequiredAPI.complete (paths (selected queries)) values middle.state (paths_nonnegative _)
      middleSemantic middleAvailable closed
  obtain ⟨fuel, readFuel, enough⟩ := requiredStable
  have required := enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨bound, queries, middle, results, after, unfolding, predicate, ⟨selection, fuel, readFuel, required⟩,
    reads, kept, afterSemantic, stable, fuel, readFuel, enough⟩

/-- Original closed construction supplies both complete stages after the actual live precheck branch. -/
theorem source_edges [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard) :
    ∃ value state, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges,
        ∀ own inherited records, SourceEqualityPrecheck.precheck own inherited = .ok (.classes records) →
          ∃ queries middle results after unfolding predicate,
            SourceEqualitySelectionEntry.Execution edge.children own inherited state
              InternedFreshOrdinaryUnfoldMemo.empty SourceUnconstrainedMemo.empty
              (.selected (selected queries)) middle unfolding predicate ∧
            Execution source edge.children (records.map SourceEqualityClassOrder.Record.paths) state queries middle results after ∧
            SemanticReady after ∧ StableRun
              (fun fuel readFuel => requireAll fuel readFuel (paths (selected queries)) edge.children middle) results after ∧
            ∀ holds ambient terms, All₂ (meaning holds ambient) results terms ↔
              All₂ (meaning holds ambient) edge.children terms ∧ ForestRequired (paths (selected queries)) terms := by
  obtain ⟨value, state, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value state built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value state built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value state built
  refine ⟨value, state, built, ?_⟩
  intro entry edges depth free original edge member own inherited records checked
  let node := InternedFreshOrdinaryGateRank.fromCompleted expression value state built
  have facts := semantic.ready.semantic.1.normal.facts
  have edgeResident := InternedEdgeResidency.resident_edges state facts.linked value available.resident
  rw [original] at edgeResident
  have childrenAvailable := facts.cached.edges edge.entry.key edge (edgeResident edge member)
  have childrenClosed : ClosedValues edge.children := by
    rw [original] at available closed
    exact MergedColdReaderClosed.node_children_closed state facts entry edges depth free available closed edge member
  obtain ⟨bound, queries, middle, results, after, unfolding, predicate, trace, reads, _, _, _, stable⟩ :=
    complete node edge.children (records.map SourceEqualityClassOrder.Record.paths) semantic childrenAvailable childrenClosed
  exact ⟨queries, middle.state, results, after, unfolding, predicate,
    .select checked trace.selection reads, trace, (exact trace semantic childrenAvailable childrenClosed).1, stable,
    (exact trace semantic childrenAvailable childrenClosed).2⟩

end MicroCFTA.SourceEqualitySelectedRequired
