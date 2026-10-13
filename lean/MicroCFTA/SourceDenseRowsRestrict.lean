import MicroCFTA.SourceDenseRowsCanonical
import MicroCFTA.SourceInternedRowsValidated
import MicroCFTA.SourceSizedDecided

/-!
# Restrict raw interned rows to their finite key carrier

Closed interpreted rows supply the membership proof for every child.
Restriction changes only the child type. It retains the exact transition
list, constructor symbols, and original constraints. Forgetting membership
proofs recovers the original rows in order.
-/

namespace MicroCFTA.SourceDenseRowsRestrict

open Language FTAValidation SourceInternedRows SourceDenseRows SymbolicGraphView

variable {keys : List State}

/-- A raw transition table has exactly its declared finite child domain. -/
def Closed (table : List (State × List (Transition Symbol Constraint))) : Prop :=
  ∀ state edge, edge ∈ lookup table state → ∀ child ∈ edge.children, child ∈ SourceDenseRows.keys table

/-- The existing interpreted closedness test derives raw child-key membership. -/
theorem closed_of_interpreted (holds : Constraint → Term Symbol → Bool)
    (table : List (State × List (Transition Symbol Constraint)))
    (closed : FTAValidation.Closed (interpretedRows holds table)) : Closed table := by
  intro state edge member child childIn
  have interpreted : interpret holds edge ∈ rowFor (interpretedRows holds table) state := by
    rw [interpreted_lookup]
    exact List.mem_map.mpr ⟨edge, member, rfl⟩
  obtain ⟨outgoing, row, member⟩ := (rowFor_exact _ _ _).mp interpreted
  have present : interpret holds edge ∈ edges (interpretedRows holds table) :=
    List.mem_flatMap.mpr ⟨(state, outgoing), row, member⟩
  apply (mem_keys table child).mpr
  rw [← interpreted_keys holds table]
  exact closed _ present child childIn

/-- Attach the derived key membership to each original child in its original position. -/
def children (table : List (State × List (Transition Symbol Constraint))) (closed : Closed table)
    (state : State) (edge : Transition Symbol Constraint) (member : edge ∈ lookup table state) :
    List (Member (SourceDenseRows.keys table)) :=
  edge.children.attach.map fun child => ⟨child.val, closed state edge member child.val child.property⟩

/-- Child restriction keeps the exact original sequence, including repeated children. -/
theorem children_values (table : List (State × List (Transition Symbol Constraint))) (closed : Closed table)
    (state : State) (edge : Transition Symbol Constraint) (member : edge ∈ lookup table state) :
    (children table closed state edge member).map Subtype.val = edge.children := by
  simp [children, List.map_map, Function.comp_def]

/-- A restricted row retains its source symbol and unevaluated constraint. -/
def row (table : List (State × List (Transition Symbol Constraint))) (closed : Closed table)
    (state : State) (edge : Transition Symbol Constraint) (member : edge ∈ lookup table state) :
    SourceSizedDecided.Row (Member (SourceDenseRows.keys table)) Symbol Constraint :=
  ⟨edge.label, children table closed state edge member, edge.constraint⟩

/-- Restrict the actual raw lookup list without sorting or removing any transition. -/
def rows (table : List (State × List (Transition Symbol Constraint))) (closed : Closed table)
    (state : Member (SourceDenseRows.keys table)) :
    List (SourceSizedDecided.Row (Member (SourceDenseRows.keys table)) Symbol Constraint) :=
  (lookup table state.val).attach.map fun edge => row table closed state.val edge.val edge.property

/-- Forget only the child-membership proofs of a restricted row. -/
def forget (edge : SourceSizedDecided.Row (Member keys) Symbol Constraint) : Transition Symbol Constraint :=
  ⟨edge.label, edge.children.map Subtype.val, edge.constraint⟩

/-- Original symbols, ordered children, and complete constraints are all recovered. -/
theorem forget_row (table : List (State × List (Transition Symbol Constraint))) (closed : Closed table)
    (state : State) (edge : Transition Symbol Constraint) (member : edge ∈ lookup table state) :
    forget (row table closed state edge member) = edge := by
  cases edge
  unfold forget row
  rw [children_values]

/-- Finite restriction has exact ordered raw-row readback. -/
theorem rows_readback (table : List (State × List (Transition Symbol Constraint))) (closed : Closed table)
    (state : Member (SourceDenseRows.keys table)) :
    (rows table closed state).map forget = lookup table state.val := by
  simp [rows, List.map_map, Function.comp_def, forget_row]

/-- Every restricted row comes from an actual source row at the same key. -/
theorem rows_origin (table : List (State × List (Transition Symbol Constraint))) (closed : Closed table)
    (state : Member (SourceDenseRows.keys table)) (edge)
    (member : edge ∈ rows table closed state) : forget edge ∈ lookup table state.val := by
  rw [← rows_readback table closed state]
  exact List.mem_map.mpr ⟨edge, member, rfl⟩

/-- Interpret the retained constraints after attaching finite child identities. -/
def automaton (table : List (State × List (Transition Symbol Constraint))) (closed : Closed table)
    (holds : Constraint → Term Symbol → Bool) : Automaton (Member (SourceDenseRows.keys table)) Symbol :=
  SourceSizedDecided.automaton (rows table closed) holds

/-- Guard interpretation commutes with forgetting the finite child carrier. -/
theorem interpret_forget (holds : Constraint → Term Symbol → Bool)
    (edge : SourceSizedDecided.Row (Member keys) Symbol Constraint) :
    interpret holds (forget edge) = renameEdge Subtype.val (edge.edge holds) := rfl

/-- The interpreted finite rows recover the complete original ordered transition sequence. -/
theorem ordered_readback (table : List (State × List (Transition Symbol Constraint))) (closed : Closed table)
    (holds : Constraint → Term Symbol → Bool) (state : Member (SourceDenseRows.keys table)) :
    rowFor (interpretedRows holds table) state.val =
      (automaton table closed holds state).map (renameEdge Subtype.val) := by
  rw [interpreted_lookup, ← rows_readback table closed state]
  simp only [automaton, SourceSizedDecided.automaton, List.map_map, Function.comp_def, interpret_forget]

/-- Guarded acceptance is exact after finite restriction, with no semantic adapter premise. -/
theorem accepts_exact (table : List (State × List (Transition Symbol Constraint))) (closed : Closed table)
    (holds : Constraint → Term Symbol → Bool) (state : Member (SourceDenseRows.keys table)) (term) :
    Accepts (automaton table closed holds) state term ↔ Accepts (rowFor (interpretedRows holds table)) state.val term := by
  symm
  apply rowsCorrespond_exact
  intro state edge
  rw [ordered_readback table closed holds state]
  simp only [List.mem_map, eq_comm]

/-- The count-table run sequence is unchanged at every size and declared state. -/
theorem enumeration_exact (table : List (State × List (Transition Symbol Constraint))) (closed : Closed table)
    (holds : Constraint → Term Symbol → Bool) (state : Member (SourceDenseRows.keys table)) (size : Nat) :
    RecursiveSize.enumerate (automaton table closed holds) size state =
      RecursiveSize.enumerate (rowFor (interpretedRows holds table)) size state.val := by
  symm
  exact SourceSizedDispatch.enumerate_ordered_rows _ _ Subtype.val (ordered_readback table closed holds) size state

/-- Exact ordered row readback also preserves guarded first-occurrence size classes. -/
theorem guarded_classes_rename [DecidableEq Symbol]
    (source : Automaton Source Symbol) (target : Automaton Target Symbol) (encode : Source → Target)
    (copied : ∀ state, target (encode state) = (source state).map (renameEdge encode))
    (size : Nat) (state : Source) :
    SourceSizedReference.classes target size (encode state) = SourceSizedReference.classes source size state := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
    cases size with
    | zero => simp [SourceSizedReference.classes_zero]
    | succ budget =>
      rw [SourceSizedReference.classes, SourceSizedReference.classes, copied]
      simp only [SourceSizedReference.classOf, List.flatMap_map]
      congr 1
      apply TablePosition.flatMap_congr
      intro edge _
      simp only [renameEdge, SourceSizedCandidates.candidates_succ]
      have forests := SourceSizedDispatch.forests_rename
        (fun size state => if _smaller : size ≤ budget then SourceSizedReference.classes source size state else [])
        (fun size state => if _smaller : size ≤ budget then SourceSizedReference.classes target size state else []) encode
        (fun childSize child => by
          by_cases smaller : childSize ≤ budget
          · simp only [smaller]
            exact ih childSize (by omega) child
          · simp [smaller]) edge.children
      rw [forests]

/-- Exact guarded size classes retain their order and first-occurrence duplicate policy. -/
theorem classes_exact [DecidableEq Symbol]
    (table : List (State × List (Transition Symbol Constraint))) (closed : Closed table)
    (holds : Constraint → Term Symbol → Bool) (state : Member (SourceDenseRows.keys table)) (size : Nat) :
    SourceSizedReference.classes (automaton table closed holds) size state =
      SourceSizedReference.classes (rowFor (interpretedRows holds table)) size state.val :=
  (guarded_classes_rename _ _ Subtype.val (ordered_readback table closed holds) size state).symm

/-- A completed source readback supplies its root's finite membership directly. -/
def root (heap : Heap Symbol Constraint) (fuel : Nat) (rootRef : Ref)
    (table : List (State × List (Transition Symbol Constraint))) (done : toRows heap fuel rootRef = some table) :
    Member (SourceDenseRows.keys table) :=
  ⟨stateOf rootRef, (mem_keys table _).mpr (toRows_initial heap fuel rootRef table done)⟩

/-- Every declared source readback state retains the exact exposed heap row in order. -/
theorem toRows_ordered_lookup (heap : Heap Symbol Constraint) (holds : Constraint → Term Symbol → Bool)
    (fuel : Nat) (rootRef : Ref) (table : List (State × List (Transition Symbol Constraint)))
    (done : toRows heap fuel rootRef = some table) (state : Member (SourceDenseRows.keys table)) :
    rowFor (interpretedRows holds table) state.val = graph heap holds state.val := by
  have declared := (mem_keys table state.val).mp state.property
  cases rootRef with
  | none =>
    have same : table = [(.empty, [])] := (Option.some.inj done).symm
    have empty : state.val = .empty := by simpa [same] using declared
    simp [same, empty, interpretedRows, rowFor, graph]
  | some identity =>
    obtain ⟨visited, walked, same⟩ := Option.map_eq_some_iff.mp done
    subst table
    obtain ⟨node, present, equal⟩ := (table_keys heap visited state.val).mp declared
    rw [equal, interpreted_table, ite_eq_left present]

/-- Restriction of actual completed readback preserves all guarded heap rows exactly. -/
theorem heap_ordered_readback (heap : Heap Symbol Constraint) (holds : Constraint → Term Symbol → Bool)
    (fuel : Nat) (rootRef : Ref) (table : List (State × List (Transition Symbol Constraint)))
    (done : toRows heap fuel rootRef = some table) (closed : Closed table)
    (state : Member (SourceDenseRows.keys table)) :
    graph heap holds state.val = (automaton table closed holds state).map (renameEdge Subtype.val) := by
  rw [← toRows_ordered_lookup heap holds fuel rootRef table done state]
  exact ordered_readback table closed holds state

/-- The finite carrier of completed raw rows accepts exactly the original guarded heap root language. -/
theorem root_accepts (heap : Heap Symbol Constraint) (holds : Constraint → Term Symbol → Bool)
    (fuel : Nat) (rootRef : Ref) (table : List (State × List (Transition Symbol Constraint)))
    (done : toRows heap fuel rootRef = some table) (closed : Closed table) (term) :
    Accepts (automaton table closed holds) (root heap fuel rootRef table done) term ↔
      Accepts (graph heap holds) (stateOf rootRef) term := by
  rw [accepts_exact]
  exact toRows_language heap holds fuel rootRef table done term

/-- The finite carrier also preserves the source heap's guarded class order and duplicate policy. -/
theorem root_classes [DecidableEq Symbol]
    (heap : Heap Symbol Constraint) (holds : Constraint → Term Symbol → Bool)
    (fuel : Nat) (rootRef : Ref) (table : List (State × List (Transition Symbol Constraint)))
    (done : toRows heap fuel rootRef = some table) (closed : Closed table) (size : Nat) :
    SourceSizedReference.classes (automaton table closed holds) size (root heap fuel rootRef table done) =
      SourceSizedReference.classes (graph heap holds) size (stateOf rootRef) :=
  (guarded_classes_rename _ _ Subtype.val (heap_ordered_readback heap holds fuel rootRef table done closed)
    size (root heap fuel rootRef table done)).symm

end MicroCFTA.SourceDenseRowsRestrict
