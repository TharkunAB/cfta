import MicroCFTA.SourceCurrentConjunctionTuplesCoverage
import MicroCFTA.SourceCurrentConjunctionEquality
import MicroCFTA.SourceCurrentConjunctionRequirements

/-!
# Allocated rows of the current conjunction check

Each tuple runs the actual equality accessor fold before any requirement
projection. Contradiction removes that tuple. Live tuples thread their
returned constructor heap and equality cache into the next tuple.
The completed exposure schedule has a separate lazy-runtime boundary.
-/
namespace MicroCFTA.SourceCurrentConjunctionRowsAllocation
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
namespace Eq
export SourceCurrentConjunctionEquality (Fields FieldAvailable fold grows_trans)
end Eq
namespace Req
export SourceCurrentConjunctionRequirements (Requirements RowsReady SameArity arity)
end Req
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Constructor reads and equality allocation retain their separate actual states. -/
structure State (Symbol Formula : Type) where
  heap : InternedConstructorTemplates.State Symbol (SourceSymbolicIndex.Constraint Formula)
  equality : SourceEqualityConstraintMemoAllocation.State

/-- Initial physical invariants supply each reached operation. -/
structure Ready (state : State Symbol Formula) : Prop where
  semantic : SemanticReady state.heap
  costs : CostHeap state.heap
  valid : SourceEqualityConstraintMemoAllocation.Valid state.equality
  fields : Eq.Fields state.equality state.heap

/-- A completed row graph retains both actual state components. -/
structure Effects (before after : State Symbol Formula) : Prop where
  keeps : Keeps before.heap after.heap
  ready : Ready after
  grows : SourceEqualityConstraintMemoAllocation.Grows before.equality after.equality

/-- An empty operation sequence retains the initial state. -/
theorem Effects.refl (state : State Symbol Formula) (ready : Ready state) : Effects state state :=
  ⟨pure_keeps _ ready.semantic.ready, ready, SourceEqualityConstraintMemoAllocation.grows_refl _⟩

/-- Consecutive actual row operations retain earlier records and equality allocations. -/
theorem Effects.trans {before middle after : State Symbol Formula}
    (first : Effects before middle) (second : Effects middle after) : Effects before after :=
  ⟨first.keeps.trans second.keeps, second.ready, Eq.grows_trans first.grows second.grows⟩

/-- A completed tuple either stops at contradiction or constructs its actual requirements. -/
inductive Tuple [DecidableEq (EdgeKey Symbol Guard)] (tuple : List (EdgeValue Symbol Guard)) :
    State Symbol Formula → Option (List (List (Value Symbol Guard))) → State Symbol Formula → Prop where
  | contradiction (folded : (Eq.fold tuple before.equality).1 = .ok (some result))
      (empty : SourceEqualityInheritedPayload.classes result.payload = none) :
      Tuple tuple before none ⟨before.heap, (Eq.fold tuple before.equality).2⟩
  | live (folded : (Eq.fold tuple before.equality).1 = .ok (some result))
      (classes : SourceEqualityInheritedPayload.classes result.payload = some constraints)
      (requirements : Req.Requirements tuple constraints before.heap rows heap) :
      Tuple tuple before (some rows) ⟨heap, (Eq.fold tuple before.equality).2⟩

/-- Every returned tuple row has closed available operands. -/
def OptionalReady (state : State Symbol Formula) : Option (List (List (Value Symbol Guard))) → Prop
  | none => True
  | some rows => Req.RowsReady state.heap rows

/-- Actual tuple allocation derives the returned cache and constructor invariants. -/
theorem Tuple.verified [DecidableEq (EdgeKey Symbol Guard)]
    {tuple : List (EdgeValue Symbol Guard)} {before after : State Symbol Formula}
    {rows : Option (List (List (Value Symbol Guard)))} (actual : Tuple tuple before rows after)
    (ready : Ready before) (resident : Edges before.heap tuple) (closed : ClosedEdges tuple) :
    Effects before after ∧ OptionalReady after rows := by
  obtain ⟨result, done, valid, _, _, _, growth, fields⟩ :=
    SourceCurrentConjunctionEquality.fold_heap_correct tuple before.heap before.equality
      ready.valid ready.fields resident
  cases actual with
  | contradiction _ _ =>
      exact ⟨⟨pure_keeps _ ready.semantic.ready, ⟨ready.semantic, ready.costs, valid, fields⟩, growth⟩, trivial⟩
  | live _ _ requirements =>
      have own := requirements.verified (Eq.FieldAvailable (Eq.fold tuple before.equality).2)
        ready.semantic ready.costs fields resident closed
      exact ⟨⟨own.1.keeps, ⟨own.1.semantic, own.1.costs, valid, own.1.annotations⟩, growth⟩, own.2⟩

/-- A finite resident tuple constructs its own actual result without a completion premise. -/
theorem tuple_complete [DecidableEq (EdgeKey Symbol Guard)]
    (tuple : List (EdgeValue Symbol Guard)) (before : State Symbol Formula) (ready : Ready before)
    (resident : Edges before.heap tuple) (closed : ClosedEdges tuple) (same : Req.SameArity tuple) :
    ∃ rows after, Tuple tuple before rows after ∧ Effects before after ∧ OptionalReady after rows := by
  obtain ⟨result, done, valid, _, _, _, _, fields⟩ :=
    SourceCurrentConjunctionEquality.fold_heap_correct tuple before.heap before.equality
      ready.valid ready.fields resident
  cases classes : SourceEqualityInheritedPayload.classes result.payload with
  | none =>
      have actual := Tuple.contradiction (tuple := tuple) done classes
      exact ⟨_, _, actual, actual.verified ready resident closed⟩
  | some constraints =>
      obtain ⟨rows, heap, requirements, _, _⟩ := SourceCurrentConjunctionRequirements.complete
        (Eq.FieldAvailable (Eq.fold tuple before.equality).2) tuple constraints before.heap
        ready.semantic ready.costs fields resident closed same
      have actual := Tuple.live done classes requirements
      exact ⟨_, _, actual, actual.verified ready resident closed⟩

/-- Tuple filtering retains matching physical child arities. -/
theorem matching_arity (tuple : List (EdgeValue Symbol Guard))
    (matched : SourceCurrentConjunctionTuples.Matching tuple) : Req.SameArity tuple := by
  cases tuple with
  | nil => simp [Req.SameArity]
  | cons first rest =>
      intro edge member
      rcases List.mem_cons.mp member with rfl | member
      · rfl
      · exact (congrArg Prod.snd ((List.pairwise_cons.mp matched).1 edge member)).symm

/-- Process literal tuples in order, retaining only noncontradictory rows. -/
inductive Tuples [DecidableEq (EdgeKey Symbol Guard)] :
    List (List (EdgeValue Symbol Guard)) → State Symbol Formula →
      List (List (List (Value Symbol Guard))) → State Symbol Formula → Prop where
  | nil : Tuples [] state [] state
  | skip (first : Tuple tuple before none middle) (rest : Tuples tuples middle rows after) :
      Tuples (tuple :: tuples) before rows after
  | keep (first : Tuple tuple before (some row) middle) (rest : Tuples tuples middle rows after) :
      Tuples (tuple :: tuples) before (row :: rows) after

/-- Each stored tuple row retains all of its closed available requirements. -/
def RowsReady (state : State Symbol Formula) (rows : List (List (List (Value Symbol Guard)))) : Prop :=
  ∀ row ∈ rows, Req.RowsReady state.heap row

/-- Constructor growth retains every requirement value of an earlier row. -/
theorem rows_keeps {before after : State Symbol Formula} (keeps : Keeps before.heap after.heap)
    {rows : List (List (List (Value Symbol Guard)))} (ready : RowsReady before rows) : RowsReady after rows := by
  intro row member requirement included
  have own := ready row member requirement included
  exact ⟨fun value present => keeps.available value (own.1 value present), own.2⟩

/-- Every finite literal tuple list derives its own allocated rows and retained invariants. -/
theorem tuples_complete [DecidableEq (EdgeKey Symbol Guard)]
    (tuples : List (List (EdgeValue Symbol Guard))) (before : State Symbol Formula) (ready : Ready before)
    (resident : ∀ tuple ∈ tuples, Edges before.heap tuple)
    (closed : ∀ tuple ∈ tuples, ClosedEdges tuple) (same : ∀ tuple ∈ tuples, Req.SameArity tuple) :
    ∃ rows after, Tuples tuples before rows after ∧ Effects before after ∧ RowsReady after rows := by
  induction tuples generalizing before with
  | nil => exact ⟨[], before, .nil, Effects.refl before ready, by simp [RowsReady]⟩
  | cons tuple tuples ih =>
      obtain ⟨row, middle, first, own, rowReady⟩ := tuple_complete tuple before ready
        (resident tuple List.mem_cons_self) (closed tuple List.mem_cons_self) (same tuple List.mem_cons_self)
      obtain ⟨rows, after, rest, later, rowsReady⟩ := ih middle own.ready
        (fun chosen member edge present => InternedEdgeResidency.edge_grows before.heap middle.heap
          own.keeps.growth edge (resident chosen (List.mem_cons_of_mem _ member) edge present))
        (fun chosen member => closed chosen (List.mem_cons_of_mem _ member))
        (fun chosen member => same chosen (List.mem_cons_of_mem _ member))
      cases row with
      | none => exact ⟨rows, after, .skip first rest, own.trans later, rowsReady⟩
      | some row =>
          refine ⟨row :: rows, after, .keep first rest, own.trans later, ?_⟩
          intro chosen member
          rcases List.mem_cons.mp member with rfl | member
          · intro requirement included
            have earlier := rowReady requirement included
            exact ⟨fun value present => later.keeps.available value (earlier.1 value present), earlier.2⟩
          · exact rowsReady chosen member

/-- One admitted conjunction retains its actual exposures and literal allocated tuple sequence. -/
inductive Rows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodes : List (Value Symbol Guard)) : State Symbol Formula →
      List (List (List (Value Symbol Guard))) → State Symbol Formula → Prop where
  | run (reads : SourceCurrentConjunctionCompletionReads.Exposures nodes before.heap edges heap)
      (tuples : Tuples (SourceCurrentConjunctionTuples.tuples edges) ⟨heap, before.equality⟩ rows after) :
      Rows nodes before rows after

/-- Actual reads and allocations complete each admitted closed resident conjunction. -/
theorem rows_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodes : List (Value Symbol Guard)) (before : State Symbol Formula) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    ∃ rows after, Rows nodes before rows after ∧ Effects before after ∧ RowsReady after rows := by
  obtain ⟨edges, heap, reads, own, _⟩ := SourceCurrentConjunctionCompletionReads.exposures_complete
    (Eq.FieldAvailable before.equality) nodes before.heap ready.semantic ready.costs ready.fields available closed
  have middle : Ready (⟨heap, before.equality⟩ : State Symbol Formula) :=
    ⟨own.semantic, own.costs, ready.valid, own.annotations⟩
  obtain ⟨rows, after, actual, later, rowsReady⟩ := tuples_complete (SourceCurrentConjunctionTuples.tuples edges)
    ⟨heap, before.equality⟩ middle
    (fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified (Eq.FieldAvailable before.equality)
      reads ready.semantic ready.costs ready.fields available closed tuple member).2.1)
    (fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified (Eq.FieldAvailable before.equality)
      reads ready.semantic ready.costs ready.fields available closed tuple member).2.2)
    (fun tuple member => matching_arity tuple (SourceCurrentConjunctionTuples.tuples_matching edges tuple member))
  exact ⟨rows, after, .run reads actual,
    ⟨own.keeps.trans later.keeps, later.ready, later.grows⟩, rowsReady⟩

end MicroCFTA.SourceCurrentConjunctionRowsAllocation
