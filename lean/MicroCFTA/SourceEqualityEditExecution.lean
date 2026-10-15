import MicroCFTA.SourceEqualityEditComplete
import MicroCFTA.SourceEqualityEditWorkerComplete
import MicroCFTA.SourceEqualityRequiredExecution

/-!
# Complete simultaneous edit execution and returned invariants

Successful graphs and bounded executions agree in both directions. Graphs
have one result and one complete cache. Leaf completion contracts remain
explicit; no whole edit-worker completion premise is supplied.
-/
namespace MicroCFTA.SourceEqualityEditExecution
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityEdits SourceEqualityEditGraph SourceEqualityEditWorker
open SourceEqualityEditComplete SourceEqualityEditWorkerComplete SourceEqualityEditWorkerSound
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityRequiredWorkerComplete (StableRun)
open SourceEqualityRequiredExecution (stable_unique)

/-- Any two completed node graphs have identical results and complete final caches. -/
theorem node_unique [DecidableEq (EdgeKey Symbol Guard)]
    {call : Callback Action Symbol Guard} {edits value before first afterFirst second afterSecond}
    (left : EditNode call edits value before first afterFirst) (right : EditNode call edits value before second afterSecond) :
    first = second ∧ afterFirst = afterSecond := stable_unique (node_stable left) (node_stable right)

/-- Node graphs are precisely the successful bounded physical executions. -/
theorem node_execution_iff [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard)
    (edits : Edits Action) (value : Value Symbol Guard) (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) :
    EditNode call edits value before result after ↔ ∃ fuel readFuel, edit call fuel readFuel edits value before = .done result after := by
  constructor
  · intro trace
    obtain ⟨fuel, readFuel, stable⟩ := node_stable trace
    exact ⟨fuel, readFuel, stable fuel readFuel (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨fuel, readFuel, done⟩
    exact edit_graph call fuel readFuel edits value before result after done

/-- Every successful node graph derives final semantic heaps and closed output from the leaf contracts. -/
theorem node_verified [DecidableEq (EdgeKey Symbol Guard)]
    {call : Callback Action Symbol Guard} {edits value before result after}
    (trace : EditNode call edits value before result after) (callbacks : All (CallbackComplete call) edits)
    (semantic : SemanticReady before) (available : Available before value) (closed : value.free = []) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = [] := by
  obtain ⟨actual, final, completed, keeps, afterSemantic, resident, resultClosed⟩ :=
    SourceEqualityEditComplete.complete call edits callbacks value before semantic available closed
  obtain ⟨sameValue, sameState⟩ := node_unique completed trace
  cases sameValue
  cases sameState
  exact ⟨keeps, afterSemantic, resident, resultClosed⟩

/-- Every child graph derives the exact final closed and resident forest. -/
theorem children_verified [DecidableEq (EdgeKey Symbol Guard)]
    {call : Callback Action Symbol Guard} {entries index values before results after}
    (trace : EditChildren call entries index values before results after)
    (callbacks : All (CallbackComplete call) (.editBelow entries))
    (semantic : SemanticReady before) (available : Values before values) (closed : ClosedValues values) :
    Keeps before after ∧ SemanticReady after ∧ Values after results ∧ ClosedValues results := by
  rw [All] at callbacks
  have children : ChildComplete call entries := by
    intro index edits member value before semantic available closed
    exact SourceEqualityEditComplete.complete call edits (callbacks index edits member) value before semantic available closed
  obtain ⟨actual, final, completed, keeps, afterSemantic, resident, resultClosed⟩ :=
    children_complete call entries children index values before semantic available closed
  obtain ⟨sameValues, sameState⟩ := stable_unique (children_stable completed) (children_stable trace)
  cases sameValues
  cases sameState
  exact ⟨keeps, afterSemantic, resident, resultClosed⟩

/-- Every row graph derives its actual final resident edges and closed child payloads. -/
theorem rows_verified [DecidableEq (EdgeKey Symbol Guard)]
    {call : Callback Action Symbol Guard} {entries edges before results after}
    (trace : EditRows call entries edges before results after)
    (callbacks : All (CallbackComplete call) (.editBelow entries))
    (semantic : SemanticReady before) (resident : Edges before edges) (closed : ClosedEdges edges) :
    Keeps before after ∧ SemanticReady after ∧ Edges after results ∧ ClosedEdges results := by
  rw [All] at callbacks
  have children : ChildComplete call entries := by
    intro index edits member value before semantic available closed
    exact SourceEqualityEditComplete.complete call edits (callbacks index edits member) value before semantic available closed
  obtain ⟨actual, final, completed, keeps, afterSemantic, resident, resultClosed⟩ :=
    rows_complete call entries children edges before semantic resident closed
  obtain ⟨sameRows, sameState⟩ := stable_unique (rows_stable completed) (rows_stable trace)
  cases sameRows
  cases sameState
  exact ⟨keeps, afterSemantic, resident, resultClosed⟩

/-- Both source child-list branches supply exact stable bounded execution. -/
theorem list_stable [DecidableEq (EdgeKey Symbol Guard)]
    {call : Callback Action Symbol Guard} {edits values before results after}
    (trace : EditList call edits values before results after) :
    StableRun (fun fuel readFuel => editList (edit call fuel readFuel) edits values before) results after := by
  cases trace with
  | leaf => exact ⟨0, 0, fun _ _ _ _ => rfl⟩
  | children trace => exact children_stable trace

/-- The actual compiled entry has exactly the successful source list graph. -/
theorem editAll_execution_iff [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard)
    (edits : List (Path × Action)) (values results : List (Value Symbol Guard)) (before after : State Symbol Guard) :
    EditList call (build edits) values before results after ↔
      ∃ fuel readFuel, editAll call fuel readFuel edits values before = .done results after := by
  constructor
  · intro trace
    obtain ⟨fuel, readFuel, stable⟩ := list_stable trace
    exact ⟨fuel, readFuel, stable fuel readFuel (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨fuel, readFuel, done⟩
    exact editAll_graph call fuel readFuel edits values results before after done

/-- The original compiled callback contracts derive finite stable whole-list execution. -/
theorem compiled_complete [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard)
    (edits : List (Path × Action)) (callbacks : ∀ path action, (path, action) ∈ edits → CallbackComplete call action)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) :
    ∃ results after, EditList call (build edits) values before results after ∧ Keeps before after ∧
      SemanticReady after ∧ Values after results ∧ ClosedValues results ∧
      StableRun (fun fuel readFuel => editAll call fuel readFuel edits values before) results after := by
  obtain ⟨results, after, trace, keeps, afterSemantic, resident, resultClosed⟩ :=
    SourceEqualityEditComplete.compiled_complete call edits callbacks values before semantic available closed
  exact ⟨results, after, trace, keeps, afterSemantic, resident, resultClosed, list_stable trace⟩

/-- Original closed construction derives every initial cache premise for finite node edits. -/
theorem source [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (call : Callback Action Symbol Guard) (edits : Edits Action) (callbacks : All (CallbackComplete call) edits) :
    ∃ value state result after,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value state ∧
      EditNode call edits value state result after ∧ Keeps state after ∧ SemanticReady after ∧ result.free = [] ∧
      StableRun (fun fuel readFuel => edit call fuel readFuel edits value state) result after := by
  obtain ⟨value, state, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value state built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value state built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value state built
  obtain ⟨result, after, trace, keeps, afterSemantic, _, resultClosed⟩ :=
    SourceEqualityEditComplete.complete call edits callbacks value state semantic available closed
  exact ⟨value, state, result, after, built, trace, keeps, afterSemantic, resultClosed, node_stable trace⟩

/-- Each original closed source edge derives finite compiled list execution from its original leaf contracts. -/
theorem source_edges [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (call : Callback Action Symbol Guard) (edits : List (Path × Action))
    (callbacks : ∀ path action, (path, action) ∈ edits → CallbackComplete call action) :
    ∃ value state, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges,
        ∃ results after, EditList call (build edits) edge.children state results after ∧ Keeps state after ∧
          SemanticReady after ∧ Values after results ∧ ClosedValues results ∧
          StableRun (fun fuel readFuel => editAll call fuel readFuel edits edge.children state) results after := by
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
  exact compiled_complete call edits callbacks edge.children state semantic childrenAvailable childrenClosed

end MicroCFTA.SourceEqualityEditExecution
