import MicroCFTA.SourceCurrentConjunctionSharedWorklistMaterialization

/-!
# Exact graphs of the actual cached materializer

The row graph records each cached head, ordered requirement read, and strict
tail credit from the existing reader. Both correspondence directions use
that reader's public equation. Table readback retains each original entry
and row handle. These graphs execute no projection and assert no semantic
coverage or future cache completion.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistMaterializationGraph
open Language
open InternedConstructorTemplates (Value)
open SourceCurrentConjunctionSharedWorklistMaterialization
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "SharedEntry" => SourceCurrentConjunctionSharedWorklistStep.Entry Symbol Formula
local notation "OldEntry" => SourceCurrentConjunctionEmptinessTable.Entry Node
local notation "CellLookup" => SourceCurrentConjunctionRequirementCells.lookup
local notation "SpineLookup" => SourceCurrentConjunctionRequirementRows.lookupSpine

/-- One cached row stream records the same reads and strict credit checks as materialization. -/
inductive RowsRead (credits : List Nat) (before : Storage) : Nat → List (List (List Node)) → Prop where
  | nil {handle credit : Nat} (own : credits[handle]? = some credit)
      (cached : SpineLookup handle before = some (.done none)) : RowsRead credits before handle []
  | cons {handle credit next tail : Nat} {handles : List Nat}
      {row : List (List Node)} {rows : List (List (List Node))}
      (own : credits[handle]? = some credit)
      (cached : SpineLookup handle before = some (.done (some (handles, tail))))
      (head : readRow handles before = some row) (nextFound : credits[tail]? = some next)
      (smaller : next < credit) (rest : RowsRead credits before tail rows) :
      RowsRead credits before handle (row :: rows)

private theorem readCell_graph (handle : Nat) (before : Storage) (nodes : List Node)
    (actual : readCell handle before = some nodes) :
    CellLookup handle before.requirements = some (.done nodes) := by
  unfold readCell at actual
  cases found : CellLookup handle before.requirements with
  | none => simp only [found] at actual; cases actual
  | some cell =>
      cases cell with
      | column values => simp only [found] at actual; cases actual
      | pending cursor => simp only [found] at actual; cases actual
      | done values =>
          simp only [found] at actual
          cases actual
          rfl

/-- Every successful row read pairs its handles with the identical cached nodes in order. -/
theorem readRow_graph (handles : List Nat) (before : Storage) (row : List (List Node))
    (actual : readRow handles before = some row) :
    All₂ (fun handle nodes => CellLookup handle before.requirements = some (.done nodes)) handles row := by
  induction handles generalizing row with
  | nil => cases actual; exact .nil
  | cons handle rest ih =>
      rw [readRow, List.mapM_cons] at actual
      change (readCell handle before).bind (fun nodes => (readRow rest before).bind
        (fun tail => some (nodes :: tail))) = some row at actual
      cases first : readCell handle before with
      | none => simp only [first, Option.bind_none] at actual; cases actual
      | some nodes =>
          cases last : readRow rest before with
          | none => simp only [first, last, Option.bind_some, Option.bind_none] at actual; cases actual
          | some tail =>
              simp only [first, last, Option.bind_some] at actual
              cases actual
              exact .cons (readCell_graph handle before nodes first) (ih tail last)

/-- An ordered cached-handle graph replays the identical actual row reader. -/
theorem readRow_replay (handles : List Nat) (before : Storage) (row : List (List Node))
    (graph : All₂ (fun handle nodes => CellLookup handle before.requirements = some (.done nodes)) handles row) :
    readRow handles before = some row := by
  induction graph with
  | nil => rfl
  | @cons handle nodes handles rows found rest ih =>
      rw [readRow, List.mapM_cons]
      change (readCell handle before).bind (fun first => (readRow handles before).bind
        (fun tail => some (first :: tail))) = some (nodes :: rows)
      rw [readCell_done handle before nodes found]
      change (readRow handles before).bind (fun tail => some (nodes :: tail)) = some (nodes :: rows)
      rw [ih]
      rfl

/-- Every successful actual stream read derives its full cached read graph. -/
theorem readRows_graph (credits : List Nat) (handle : Nat) (before : Storage)
    (rows : List (List (List Node))) (actual : readRows credits handle before = some rows) :
    RowsRead credits before handle rows := by
  have derive : ∀ credit handle rows, credits[handle]? = some credit →
      readRows credits handle before = some rows → RowsRead credits before handle rows := by
    intro credit
    induction credit using Nat.strongRecOn with
    | ind credit smallerCredit =>
        intro handle rows own observed
        rw [readRows_eq, own] at observed
        cases cached : SpineLookup handle before with
        | none => simp only [cached] at observed; cases observed
        | some spine =>
            cases spine with
            | pending tuples => simp only [cached] at observed; cases observed
            | done cachedRow =>
                cases cachedRow with
                | none =>
                    simp only [cached] at observed
                    cases observed
                    exact .nil own cached
                | some pair =>
                    rcases pair with ⟨handles, tail⟩
                    cases first : readRow handles before with
                    | none => simp only [cached, first, Option.bind_none] at observed; cases observed
                    | some row =>
                        cases nextFound : credits[tail]? with
                        | none =>
                            simp only [cached, first, nextFound, Option.bind_some, Option.bind_none] at observed
                            cases observed
                        | some next =>
                            by_cases smaller : next < credit
                            · cases last : readRows credits tail before with
                              | none =>
                                  simp only [cached, first, nextFound, Option.bind_some, ite_eq_left smaller,
                                    last, Option.map_none] at observed
                                  cases observed
                              | some remaining =>
                                  simp only [cached, first, nextFound, Option.bind_some, ite_eq_left smaller,
                                    last, Option.map_some] at observed
                                  cases observed
                                  exact .cons own cached first nextFound smaller
                                    (smallerCredit next smaller tail remaining nextFound last)
                            · simp only [cached, first, nextFound, Option.bind_some, ite_eq_right smaller] at observed
                              cases observed
  cases own : credits[handle]? with
  | none => rw [readRows_eq, own] at actual; cases actual
  | some credit => exact derive credit handle rows own actual

/-- The cached read graph replays the same actual stream reader without another read supplier. -/
theorem RowsRead.replay {credits : List Nat} {before : Storage} {handle : Nat}
    {rows : List (List (List Node))} (graph : RowsRead credits before handle rows) :
    readRows credits handle before = some rows := by
  induction graph with
  | nil own cached =>
      rw [readRows_eq]
      simp only [own, cached]
  | cons own cached head nextFound smaller rest ih =>
      rw [readRows_eq]
      simp only [own, cached, head, nextFound, Option.bind_some, ite_eq_left smaller, ih, Option.map_some]

/-- A materialized table entry retains its original query and exact optional row handle. -/
def EntryRead (credits : List Nat) (before : Storage) (original : SharedEntry) (result : OldEntry) : Prop :=
  result.nodes = original.nodes ∧
    match original.rows with
    | none => result.rows = []
    | some handle => RowsRead credits before handle result.rows

private theorem mapM_graph (read : α → Option β) (inputs : List α) (outputs : List β)
    (actual : inputs.mapM read = some outputs) : All₂ (fun input output => read input = some output) inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases actual; exact .nil
  | cons input rest ih =>
      rw [List.mapM_cons] at actual
      change (read input).bind (fun first => (rest.mapM read).bind
        (fun last => some (first :: last))) = some outputs at actual
      cases first : read input with
      | none => simp only [first, Option.bind_none] at actual; cases actual
      | some output =>
          cases last : rest.mapM read with
          | none => simp only [first, last, Option.bind_some, Option.bind_none] at actual; cases actual
          | some tail =>
              simp only [first, last, Option.bind_some] at actual
              cases actual
              exact .cons first (ih tail last)

/-- Actual table reading derives ordered query, handle, and cached-row correspondence. -/
theorem readTable_graph (credits : List Nat) (before : WorkState)
    (table : SourceCurrentConjunctionWorker.Table Symbol Formula) (actual : readTable credits before = some table) :
    All₂ (EntryRead credits before.storage) before.table table := by
  unfold readTable at actual
  have aligned := mapM_graph _ before.table table actual
  refine All₂.imp (fun original result observed => ?_) aligned
  unfold EntryRead
  cases selected : original.rows with
  | none =>
      simp only [selected] at observed
      cases observed
      exact ⟨rfl, rfl⟩
  | some handle =>
      simp only [selected] at observed
      cases read : readRows credits handle before.storage with
      | none => simp only [read] at observed; cases observed
      | some rows =>
          simp only [read] at observed
          cases observed
          exact ⟨rfl, readRows_graph credits handle before.storage rows read⟩

private theorem all₂_preimage {α β : Type} {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (aligned : All₂ relation inputs outputs) (output : β) (member : output ∈ outputs) :
    ∃ input ∈ inputs, relation input output := by
  induction aligned with
  | nil => cases member
  | @cons input first inputs outputs own rest ih =>
      rcases List.mem_cons.mp member with same | remaining
      · cases same
        exact ⟨input, List.mem_cons_self, own⟩
      · obtain ⟨source, present, related⟩ := ih remaining
        exact ⟨source, List.mem_cons_of_mem _ present, related⟩

/-- Every materialized entry comes from the same actual stored query and row handle. -/
theorem readTable_member (credits : List Nat) (before : WorkState)
    (table : SourceCurrentConjunctionWorker.Table Symbol Formula) (actual : readTable credits before = some table)
    (result : OldEntry) (member : result ∈ table) :
    ∃ original ∈ before.table, EntryRead credits before.storage original result := by
  exact all₂_preimage (readTable_graph credits before table actual) result member

end MicroCFTA.SourceCurrentConjunctionSharedWorklistMaterializationGraph
