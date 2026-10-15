import MicroCFTA.SourceEqualityRequiredLanguage

/-!
# Finite required-path execution at the independent source language

The compiled forest entry has conditional requirements at present root
positions. A root arity premise gives existence of every complete path.
The source child-list entry does not reject a missing root position.
-/
namespace MicroCFTA.SourceEqualityRequiredAPI
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityNeeded SourceEqualityNeededMeaning SourceEqualityNeededNonnegative
open SourceEqualityRequiredCache SourceEqualityRequiredGraph SourceEqualityRequiredSemanticCache
open SourceEqualityRequiredWorker SourceEqualityRequiredWorkerComplete SourceEqualityRequiredExecution
open SourceEqualityRequiredForestMeaning SourceEqualityRequiredLanguage
open InternedGuardedLanguage (meaning)

/-- The compiled top-level child scan checks requirements only at present positions. -/
def ForestRequired (paths : List Path) (terms : List (Term Symbol)) : Prop :=
  match build paths with
  | .node entries => Required entries 0 terms

/-- Every successful instrumented node execution has the exact independent filter language. -/
theorem node_done [DecidableEq (EdgeKey Symbol Guard)]
    (fuel readFuel : Nat) (needed : Needed) (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : require fuel readFuel needed value before = .done result after)
    (valid : SourceEqualityNeeded.Valid needed) (nonnegative : Nonnegative needed)
    (semantic : SemanticReady before) (available : Available before value) (closed : value.free = []) :
    ∀ holds ambient term, meaning holds ambient result term ↔ meaning holds ambient value term ∧ Matches needed term :=
  node_exact (SourceEqualityRequiredWorkerSound.require_graph fuel readFuel needed value before result after done)
    valid nonnegative semantic available closed

/-- The actual compiled child worker agrees with the ordered source fold on independent languages. -/
theorem requireAll_done [DecidableEq (EdgeKey Symbol Guard)]
    (fuel readFuel : Nat) (paths : List Path) (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : requireAll fuel readFuel paths values before = .done results after)
    (indices : ∀ path ∈ paths, ∀ index ∈ path, 0 ≤ index)
    (semantic : SemanticReady before) (available : Values before values) (closed : ClosedValues values) :
    ∀ holds ambient terms, All₂ (meaning holds ambient) results terms ↔
      All₂ (meaning holds ambient) values terms ∧ ForestRequired paths terms := by
  have trace := (requireAll_execution_iff paths values before results after).mpr ⟨fuel, readFuel, done⟩
  have valid := build_valid paths
  have nonnegative := build_nonnegative paths indices
  cases compiled : build paths with
  | node entries =>
      simp only [compiled] at trace valid nonnegative
      simpa only [ForestRequired, compiled] using children_exact trace valid nonnegative semantic available closed

/-- A root arity bound gives precisely the original forest and existence of all complete input paths. -/
theorem requireAll_paths [DecidableEq (EdgeKey Symbol Guard)]
    (fuel readFuel : Nat) (paths : List Path) (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : requireAll fuel readFuel paths values before = .done results after)
    (indices : ∀ path ∈ paths, ∀ index ∈ path, 0 ≤ index)
    (rootFits : fits (build paths) values.length = true)
    (semantic : SemanticReady before) (available : Values before values) (closed : ClosedValues values) :
    ∀ holds ambient symbol terms, All₂ (meaning holds ambient) results terms ↔
      All₂ (meaning holds ambient) values terms ∧
        ∀ path ∈ paths, ∃ part, SymbolicSignedPaths.lookup (.node symbol terms) path = some part := by
  intro holds ambient symbol terms
  rw [requireAll_done fuel readFuel paths values results before after done indices semantic available closed holds ambient terms,
    ← build_exact]
  have valid := build_valid paths
  have nonnegative := build_nonnegative paths indices
  cases compiled : build paths with
  | node entries =>
      simp only [ForestRequired, compiled] at valid nonnegative rootFits ⊢
      have keys : ∀ key child, (key, child) ∈ entries → 0 ≤ key := by
        rw [Nonnegative] at nonnegative
        exact fun key child member => (nonnegative key child member).1
      exact checked_exact (meaning holds ambient) entries valid keys values symbol terms rootFits

/-- Requiring paths keeps every original forest term in which all those paths exist. -/
theorem requireAll_keep [DecidableEq (EdgeKey Symbol Guard)]
    (fuel readFuel : Nat) (paths : List Path) (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : requireAll fuel readFuel paths values before = .done results after)
    (indices : ∀ path ∈ paths, ∀ index ∈ path, 0 ≤ index)
    (semantic : SemanticReady before) (available : Values before values) (closed : ClosedValues values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (accepted : All₂ (meaning holds ambient) values terms)
    (pathsExist : ∀ path ∈ paths, ∃ part, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) :
    All₂ (meaning holds ambient) results terms := by
  have matched := (build_exact paths (.node symbol terms)).mpr pathsExist
  have rootFits := matching_row_fits (build paths) (build_valid paths) symbol terms matched
  rw [← accepted.length_eq] at rootFits
  exact (requireAll_paths fuel readFuel paths values results before after done indices rootFits semantic available closed
    holds ambient symbol terms).mpr ⟨accepted, pathsExist⟩

/-- Every ready closed forest has finite stable execution with exact conditional path filtering. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (indices : ∀ path ∈ paths, ∀ index ∈ path, 0 ≤ index)
    (semantic : SemanticReady before) (available : Values before values) (closed : ClosedValues values) :
    ∃ results after, Keeps before after ∧ SemanticReady after ∧ Values after results ∧ ClosedValues results ∧
      StableRun (fun fuel readFuel => requireAll fuel readFuel paths values before) results after ∧
      ∀ holds ambient terms, All₂ (meaning holds ambient) results terms ↔
        All₂ (meaning holds ambient) values terms ∧ ForestRequired paths terms := by
  obtain ⟨results, after, keeps, resultAvailable, resultClosed, stable⟩ :=
    requireAll_complete paths values before semantic.ready available closed
  obtain ⟨fuel, readFuel, done⟩ : ∃ fuel readFuel, requireAll fuel readFuel paths values before = .done results after := by
    obtain ⟨fuel, readFuel, enough⟩ := stable
    exact ⟨fuel, readFuel, enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)⟩
  have trace := (requireAll_execution_iff paths values before results after).mpr ⟨fuel, readFuel, done⟩
  have afterSemantic : SemanticReady after := by
    cases compiled : build paths with
    | node entries =>
        simp only [compiled] at trace
        exact SourceEqualityRequiredSemanticEffects.children trace semantic available closed
  exact ⟨results, after, keeps, afterSemantic, resultAvailable, resultClosed, stable,
    requireAll_done fuel readFuel paths values results before after done indices semantic available closed⟩

/-- Original closed construction derives stable node filtering by the complete source path set. -/
theorem source [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (paths : List Path) (indices : ∀ path ∈ paths, ∀ index ∈ path, 0 ≤ index) :
    ∃ value state result after,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value state ∧
      Keeps state after ∧ SemanticReady after ∧ result.free = [] ∧
      StableRun (fun fuel readFuel => require fuel readFuel (build paths) value state) result after ∧
      ∀ holds ambient term, meaning holds ambient result term ↔
        InternedGuardedSyntax.evaluate holds [] expression term ∧
          ∀ path ∈ paths, ∃ part, SymbolicSignedPaths.lookup term path = some part := by
  obtain ⟨value, state, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value state built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value state built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value state built
  obtain ⟨result, after, trace, keeps, _, resultClosed⟩ :=
    SourceEqualityRequiredComplete.complete (build paths) value state semantic.ready available closed
  refine ⟨value, state, result, after, built, keeps,
    SourceEqualityRequiredSemanticEffects.node trace semantic available closed, resultClosed, node_stable trace, ?_⟩
  intro holds ambient term
  rw [node_exact trace (build_valid paths) (build_nonnegative paths indices) semantic available closed holds ambient term,
    build_exact, InternedGuardedExecution.closed_language expression value state built holds ambient]

/-- A missing top-level child remains absent; the source list entry does not reject it. -/
theorem missing_root_boundary :
    requireAll (Symbol := Nat) (Guard := Unit) 0 0 [[3, 0]] [] empty = .done [] empty ∧
      ForestRequired (Symbol := Nat) [[3, 0]] [] ∧
        ¬ Matches (build [[3, 0]]) (Term.node 0 []) := by
  refine ⟨rfl, trivial, ?_⟩
  rw [build_exact]
  intro allPaths
  obtain ⟨part, found⟩ := allPaths [3, 0] (by simp)
  simp [SymbolicSignedPaths.lookup] at found

end MicroCFTA.SourceEqualityRequiredAPI
