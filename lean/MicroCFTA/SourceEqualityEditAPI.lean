import MicroCFTA.SourceEqualityEditLanguage

/-!
# Source entry for exact simultaneous edit filtering

Node and list branches keep their different root-leaf behavior. Original
construction derives cache and closed-input premises. Per-leaf completion
and language contracts remain explicit until concrete callbacks supply them.
-/
namespace MicroCFTA.SourceEqualityEditAPI
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityEdits SourceEqualityEditGraph SourceEqualityEditMeaning
open SourceEqualityEditLanguage SourceEqualityEditWorker SourceEqualityEditExecution
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityRequiredWorkerComplete (StableRun)
open InternedGuardedLanguage (meaning)

/-- A list-root leaf is ignored; a below-node applies conditions at present child positions. -/
def ListCondition (condition : Action → Term Symbol → Prop) (edits : Edits Action) (terms : List (Term Symbol)) : Prop :=
  match edits with
  | .editAt _ => True
  | .editBelow entries => Forest condition entries 0 terms

variable [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard)
  (condition : Action → Term Symbol → Prop) (holds : Guard → Term Symbol → Bool)
  (ambient : InternedGuardedLanguage.Env Symbol)

/-- Actual list graphs retain precisely the original forest terms that satisfy their list conditions. -/
theorem list_exact {edits values before results after} (trace : EditList call edits values before results after)
    (valid : SourceEqualityEdits.Valid edits) (laws : All (LeafLaw call condition holds ambient) edits)
    (semantic : SemanticReady before) (available : Values before values) (closed : ClosedValues values) :
    ∀ terms, All₂ (meaning holds ambient) results terms ↔
      All₂ (meaning holds ambient) values terms ∧ ListCondition condition edits terms := by
  cases trace with
  | leaf => intro terms; exact ⟨fun accepted => ⟨accepted, trivial⟩, fun accepted => accepted.1⟩
  | children trace => exact children_exact call condition holds ambient trace valid laws semantic available closed

/-- Every successful instrumented node edit has the exact independent output language. -/
theorem node_done (fuel readFuel : Nat) (edits : Edits Action) (value result : Value Symbol Guard)
    (before after : State Symbol Guard) (done : edit call fuel readFuel edits value before = .done result after)
    (valid : SourceEqualityEdits.Valid edits) (laws : All (LeafLaw call condition holds ambient) edits)
    (semantic : SemanticReady before) (available : Available before value) (closed : value.free = []) :
    ∀ term, meaning holds ambient result term ↔ meaning holds ambient value term ∧ Matches condition edits term :=
  node_exact call condition holds ambient (SourceEqualityEditWorkerSound.edit_graph call fuel readFuel edits value before result after done)
    valid laws semantic available closed

/-- Actual compilation derives the exact list condition from original per-callback laws. -/
theorem editAll_done (fuel readFuel : Nat) (edits : List (Path × Action)) (values results : List (Value Symbol Guard))
    (before after : State Symbol Guard) (done : editAll call fuel readFuel edits values before = .done results after)
    (laws : ∀ path action, (path, action) ∈ edits → LeafLaw call condition holds ambient action)
    (semantic : SemanticReady before) (available : Values before values) (closed : ClosedValues values) :
    ∀ terms, All₂ (meaning holds ambient) results terms ↔
      All₂ (meaning holds ambient) values terms ∧ ListCondition condition (build edits) terms :=
  list_exact call condition holds ambient (SourceEqualityEditWorkerSound.editAll_graph call fuel readFuel edits values results before after done)
    (build_valid edits) (build_all _ edits laws) semantic available closed

/-- Finite stable compiled execution has the exact independent list language and all final invariants. -/
theorem complete (edits : List (Path × Action))
    (laws : ∀ path action, (path, action) ∈ edits → LeafLaw call condition holds ambient action)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) :
    ∃ results after, EditList call (build edits) values before results after ∧ Keeps before after ∧ SemanticReady after ∧
      Values after results ∧ ClosedValues results ∧
      StableRun (fun fuel readFuel => editAll call fuel readFuel edits values before) results after ∧
      ∀ terms, All₂ (meaning holds ambient) results terms ↔
        All₂ (meaning holds ambient) values terms ∧ ListCondition condition (build edits) terms := by
  obtain ⟨results, after, trace, keeps, afterSemantic, resident, resultClosed, stable⟩ :=
    SourceEqualityEditExecution.compiled_complete call edits (fun path action member => (laws path action member).complete)
      values before semantic available closed
  exact ⟨results, after, trace, keeps, afterSemantic, resident, resultClosed, stable,
    list_exact call condition holds ambient trace (build_valid edits) (build_all _ edits laws) semantic available closed⟩

/-- Original closed syntax derives stable node editing at its independent source language. -/
theorem source (expression : InternedNestedConstruction.Syntax Symbol Guard) (edits : Edits Action)
    (valid : SourceEqualityEdits.Valid edits) (laws : All (LeafLaw call condition holds ambient) edits) :
    ∃ value state result after,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value state ∧
      Keeps state after ∧ SemanticReady after ∧ result.free = [] ∧
      StableRun (fun fuel readFuel => edit call fuel readFuel edits value state) result after ∧
      ∀ term, meaning holds ambient result term ↔ InternedGuardedSyntax.evaluate holds [] expression term ∧ Matches condition edits term := by
  obtain ⟨value, state, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value state built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value state built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value state built
  obtain ⟨result, after, trace, keeps, afterSemantic, _, resultClosed⟩ :=
    SourceEqualityEditComplete.complete call edits (leaves_complete call condition holds ambient laws) value state semantic available closed
  refine ⟨value, state, result, after, built, keeps, afterSemantic, resultClosed,
    SourceEqualityEditWorkerComplete.node_stable trace, ?_⟩
  intro term
  rw [node_exact call condition holds ambient trace valid laws semantic available closed term,
    InternedGuardedExecution.closed_language expression value state built holds ambient]

/-- Every original closed source edge derives finite compiled editing and exact ordered forest filtering. -/
theorem source_edges (expression : InternedNestedConstruction.Syntax Symbol Guard) (edits : List (Path × Action))
    (laws : ∀ path action, (path, action) ∈ edits → LeafLaw call condition holds ambient action) :
    ∃ value state, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges,
        ∃ results after, Keeps state after ∧ SemanticReady after ∧ Values after results ∧ ClosedValues results ∧
          StableRun (fun fuel readFuel => editAll call fuel readFuel edits edge.children state) results after ∧
          ∀ terms, All₂ (meaning holds ambient) results terms ↔
            All₂ (meaning holds ambient) edge.children terms ∧ ListCondition condition (build edits) terms := by
  obtain ⟨value, state, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value state built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value state built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value state built
  refine ⟨value, state, built, ?_⟩
  intro entry edges depth free original edge member
  rw [original] at available closed
  have facts := semantic.ready.semantic.1.normal.facts
  have resident := InternedEdgeResidency.resident_edges state facts.linked _ available.resident
  have childrenAvailable := facts.cached.edges edge.entry.key edge (resident edge member)
  have childrenClosed := MergedColdReaderClosed.node_children_closed state facts entry edges depth free available closed edge member
  obtain ⟨results, after, _, keeps, afterSemantic, resident, resultClosed, stable, exactLanguage⟩ :=
    complete call condition holds ambient edits laws edge.children state semantic childrenAvailable childrenClosed
  exact ⟨results, after, keeps, afterSemantic, resident, resultClosed, stable, exactLanguage⟩

end MicroCFTA.SourceEqualityEditAPI
