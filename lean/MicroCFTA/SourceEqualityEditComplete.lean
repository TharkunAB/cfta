import MicroCFTA.SourceEqualityEditWorker
import MicroCFTA.SourceEqualityRequiredSemanticCache

/-!
# Finite simultaneous edit graphs from actual leaf callback contracts

Only callbacks stored at leaves supply completion contracts. The finite edit
trie derives node recursion and complete ordered scans. Actual constructors
and closed head exposure derive every other cache and output invariant.
Concrete equality-narrowing callbacks must still discharge the leaf contracts.
-/
namespace MicroCFTA.SourceEqualityEditComplete
open InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (edge_grows)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityEdits SourceEqualityEditGraph
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache

/-- One stored callback completes on closed available inputs with its actual cache effects. -/
def CallbackComplete [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard) (action : Action) : Prop :=
  ∀ (value : Value Symbol Guard) (before : State Symbol Guard),
    SemanticReady before → Available before value → value.free = [] →
    ∃ result after, call action value before = .done result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = []

/-- The edit-depth induction supplies completion only for stored child edit subtrees. -/
def ChildComplete [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard)
    (entries : List (Int × Edits Action)) : Prop :=
  ∀ index edits, (index, edits) ∈ entries → ∀ (value : Value Symbol Guard) (before : State Symbol Guard),
    SemanticReady before → Available before value → value.free = [] →
    ∃ result after, EditNode call edits value before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = []

/-- Finite child scans derive all intermediate states and preserve untouched positions. -/
theorem children_complete [DecidableEq (EdgeKey Symbol Guard)]
    (call : Callback Action Symbol Guard) (entries : List (Int × Edits Action)) (children : ChildComplete call entries)
    (index : Nat) (values : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) :
    ∃ results after, EditChildren call entries index values before results after ∧ Keeps before after ∧
      SemanticReady after ∧ Values after results ∧ ClosedValues results := by
  induction values generalizing index before with
  | nil => exact ⟨[], before, .nil, pure_keeps before semantic.ready, semantic, by simp [Values], by simp [ClosedValues]⟩
  | cons value values ih =>
      have firstAvailable := available value List.mem_cons_self
      have restAvailable : Values before values := fun child member => available child (List.mem_cons_of_mem _ member)
      have firstClosed := closed value List.mem_cons_self
      have restClosed : ClosedValues values := fun child member => closed child (List.mem_cons_of_mem _ member)
      cases found : SourceEqualityNeededMap.lookup (index : Int) entries with
      | none =>
          obtain ⟨results, after, trace, keeps, afterSemantic, resultAvailable, resultClosed⟩ :=
            ih (index + 1) before semantic restAvailable restClosed
          refine ⟨value :: results, after, .unselected index found trace, keeps, afterSemantic, ?_, ?_⟩
          · intro child member
            rcases List.mem_cons.mp member with rfl | member
            · exact keeps.available _ firstAvailable
            · exact resultAvailable child member
          · intro child member
            rcases List.mem_cons.mp member with rfl | member
            · exact firstClosed
            · exact resultClosed child member
      | some edits =>
          obtain ⟨result, middle, firstTrace, firstKeeps, middleSemantic, firstResident, firstResultClosed⟩ :=
            children (index : Int) edits (SourceEqualityNeededMap.lookup_mem _ _ _ found) value before semantic firstAvailable firstClosed
          have restAvailable : Values middle values := fun child member => firstKeeps.available child (restAvailable child member)
          obtain ⟨results, after, restTrace, restKeeps, afterSemantic, resultAvailable, resultClosed⟩ :=
            ih (index + 1) middle middleSemantic restAvailable restClosed
          refine ⟨result :: results, after, .selected index found firstTrace restTrace, firstKeeps.trans restKeeps, afterSemantic, ?_, ?_⟩
          · intro child member
            rcases List.mem_cons.mp member with rfl | member
            · exact restKeeps.available _ firstResident
            · exact resultAvailable child member
          · intro child member
            rcases List.mem_cons.mp member with rfl | member
            · exact firstResultClosed
            · exact resultClosed child member

/-- Every original row is rebuilt in order with complete resident and closed output invariants. -/
theorem rows_complete [DecidableEq (EdgeKey Symbol Guard)]
    (call : Callback Action Symbol Guard) (entries : List (Int × Edits Action)) (children : ChildComplete call entries)
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges) :
    ∃ results after, EditRows call entries edges before results after ∧ Keeps before after ∧
      SemanticReady after ∧ Edges after results ∧ ClosedEdges results := by
  induction edges generalizing before with
  | nil => exact ⟨[], before, .nil, pure_keeps before semantic.ready, semantic, by simp [Edges], by simp [ClosedEdges]⟩
  | cons edge edges ih =>
      have facts := semantic.ready.semantic.1.normal.facts
      have available : Values before edge.children := facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
      have restResident : Edges before edges := fun original member => resident original (List.mem_cons_of_mem _ member)
      have restClosed : ClosedEdges edges := fun original member => closed original (List.mem_cons_of_mem _ member)
      obtain ⟨values, middle, childTrace, childKeeps, middleSemantic, valuesAvailable, valuesClosed⟩ :=
        children_complete call entries children 0 edge.children before semantic available (closed edge List.mem_cons_self)
      let actual := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle
      have built := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle middleSemantic.ready valuesAvailable
      have edgeSemantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle middleSemantic valuesAvailable
      have firstKeeps : Keeps before actual.2 := childKeeps.trans built.1
      have restResident : Edges actual.2 edges := fun original member =>
        edge_grows before actual.2 firstKeeps.growth original (restResident original member)
      obtain ⟨results, after, restTrace, restKeeps, afterSemantic, residentResults, closedResults⟩ :=
        ih actual.2 edgeSemantic restResident restClosed
      refine ⟨actual.1 :: results, after, .cons childTrace rfl restTrace, firstKeeps.trans restKeeps, afterSemantic, ?_, ?_⟩
      · intro original member
        rcases List.mem_cons.mp member with rfl | member
        · exact edge_grows actual.2 after restKeeps.growth actual.1 built.2.1
        · exact residentResults original member
      · intro original member
        rcases List.mem_cons.mp member with rfl | member
        · rw [show actual.1.children = values from built.2.2]
          exact valuesClosed
        · exact closedResults original member

/-- Ordinary node edits complete from the induction hypotheses for their child subtrees. -/
theorem ordinary_complete [DecidableEq (EdgeKey Symbol Guard)]
    (call : Callback Action Symbol Guard) (entries : List (Int × Edits Action)) (children : ChildComplete call entries)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (ordinary : Ordinary value) :
    ∃ result after, EditNode call (.editBelow entries) value before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = [] := by
  cases value with
  | empty => exact ⟨.empty, before, .empty, pure_keeps before semantic.ready, semantic, available, rfl⟩
  | reference | union | mu => cases ordinary
  | node entry edges depth free =>
      have facts := semantic.ready.semantic.1.normal.facts
      have resident : Edges before edges := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
      have closedEdges := MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed
      obtain ⟨rebuilt, middle, rows, firstKeeps, middleSemantic, residentRows, closedRows⟩ :=
        rows_complete call entries children edges before semantic resident closedEdges
      have finished := SourceEqualityRequiredCache.node rebuilt middle middleSemantic.ready residentRows closedRows
      have finalSemantic := SourceEqualityRequiredSemanticCache.node rebuilt middle middleSemantic residentRows closedRows
      exact ⟨_, _, .ordinary rows rfl, firstKeeps.trans finished.1, finalSemantic, finished.2.1, finished.2.2.1⟩

/-- Finite edit depth and the stored leaf contracts derive complete physical node execution graphs. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard) (edits : Edits Action)
    (callbacks : All (CallbackComplete call) edits) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Available before value) (closed : value.free = []) :
    ∃ result after, EditNode call edits value before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = [] := by
  cases shape : edits with
  | editAt action =>
      rw [shape, All] at callbacks
      obtain ⟨result, after, actual, keeps, afterSemantic, resultAvailable, resultClosed⟩ :=
        callbacks value before semantic available closed
      exact ⟨result, after, .leaf actual, keeps, afterSemantic, resultAvailable, resultClosed⟩
  | editBelow entries =>
      rw [shape, All] at callbacks
      have children : ChildComplete call entries := by
        intro index child member value before semantic available closed
        exact complete call child (callbacks index child member) value before semantic available closed
      cases value with
      | empty => exact ⟨.empty, before, .empty, pure_keeps before semantic.ready, semantic, available, rfl⟩
      | reference name => simp [Value.free] at closed
      | node entry edges depth free => exact ordinary_complete call entries children _ before semantic available closed trivial
      | union entry members depth free =>
          obtain ⟨exposed, middle, head, headKeeps, headAvailable, headClosed, ordinary⟩ :=
            SourceEqualityRequiredHead.complete (.union entry members depth free) before semantic.ready available closed
          have middleSemantic := SourceEqualityRequiredSemanticCache.head head semantic available closed
          obtain ⟨result, after, body, bodyKeeps, afterSemantic, resultAvailable, resultClosed⟩ :=
            ordinary_complete call entries children exposed middle middleSemantic headAvailable headClosed ordinary
          exact ⟨result, after, .recursive trivial head body, headKeeps.trans bodyKeeps, afterSemantic, resultAvailable, resultClosed⟩
      | mu entry body depth probe =>
          obtain ⟨exposed, middle, head, headKeeps, headAvailable, headClosed, ordinary⟩ :=
            SourceEqualityRequiredHead.complete (.mu entry body depth probe) before semantic.ready available closed
          have middleSemantic := SourceEqualityRequiredSemanticCache.head head semantic available closed
          obtain ⟨result, after, bodyTrace, bodyKeeps, afterSemantic, resultAvailable, resultClosed⟩ :=
            ordinary_complete call entries children exposed middle middleSemantic headAvailable headClosed ordinary
          exact ⟨result, after, .recursive trivial head bodyTrace, headKeeps.trans bodyKeeps, afterSemantic, resultAvailable, resultClosed⟩
termination_by sizeOf edits
decreasing_by
  rw [shape]
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec, Edits.editBelow.sizeOf_spec] at *
  omega

/-- The actual compiled source list entry needs completion only for its original callbacks. -/
theorem compiled_complete [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard)
    (edits : List (Path × Action)) (callbacks : ∀ path action, (path, action) ∈ edits → CallbackComplete call action)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) :
    ∃ results after, EditList call (build edits) values before results after ∧ Keeps before after ∧
      SemanticReady after ∧ Values after results ∧ ClosedValues results := by
  have allCallbacks := build_all (CallbackComplete call) edits callbacks
  cases compiled : build edits with
  | editAt action =>
      exact ⟨values, before, .leaf, pure_keeps before semantic.ready, semantic, available, closed⟩
  | editBelow entries =>
      rw [compiled, All] at allCallbacks
      have children : ChildComplete call entries := by
        intro index child member value before semantic available closed
        exact complete call child (allCallbacks index child member) value before semantic available closed
      obtain ⟨results, after, trace, keeps, afterSemantic, resultAvailable, resultClosed⟩ :=
        children_complete call entries children 0 values before semantic available closed
      exact ⟨results, after, .children trace, keeps, afterSemantic, resultAvailable, resultClosed⟩

end MicroCFTA.SourceEqualityEditComplete
