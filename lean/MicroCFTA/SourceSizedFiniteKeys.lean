import MicroCFTA.SizedLanguageTheorem
import MicroCFTA.SourceDenseRowsRestrict

/-!
# Sized input from finite validated row-map keys

A finite explicit FTA may use an infinite state type. The actual map keys
supply the finite carrier. Validation derives the root and child membership
proofs. Restriction retains all rows, including unreachable and dead rows,
with their constraints and order. No whole-state-type finiteness is assumed.
-/
namespace MicroCFTA.SourceSizedFiniteKeys
open Language SourceSizedDecided SourceDenseRows Std
attribute [local instance] lexOrd

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State]

/-- Explicit source table rows retain the complete raw constraint. -/
abbrev Table (State Symbol Payload : Type) := List (State × List (Row State Symbol Payload))

/-- Functional map readback merges every occurrence in original alternative order. -/
def lookup (table : Table State Symbol Payload) (state : State) : List (Row State Symbol Payload) :=
  table.flatMap fun entry => if entry.1 = state then entry.2 else []

/-- Interpret constraints without changing keys or transition order. -/
def interpreted (table : Table State Symbol Payload) (holds : Payload → Term Symbol → Bool) :
    FTAValidation.Rows State Symbol := table.map fun entry => (entry.1, entry.2.map (Row.edge holds))

omit [DecidableEq State] [Ord State] in
/-- Interpreted tables retain exactly the original state-key inventory. -/
theorem interpreted_keys (table : Table State Symbol Payload) (holds : Payload → Term Symbol → Bool) :
    (interpreted table holds).map Prod.fst = table.map Prod.fst := by simp [interpreted, List.map_map]

omit [Ord State] in
/-- Interpretation commutes with the actual merged lookup list. -/
theorem interpreted_lookup (table : Table State Symbol Payload) (holds : Payload → Term Symbol → Bool) (state : State) :
    FTAValidation.rowFor (interpreted table holds) state = (lookup table state).map (Row.edge holds) := by
  simp only [FTAValidation.rowFor, interpreted, List.flatMap_map, lookup, List.map_flatMap]
  apply TablePosition.flatMap_congr
  intro entry _
  split <;> simp_all

/-- A raw table is closed precisely when each retained child is a declared key. -/
def Closed (table : Table State Symbol Payload) : Prop :=
  ∀ state edge, edge ∈ lookup table state → ∀ child ∈ edge.children, child ∈ SourceDenseRows.keys table

/-- Successful structural validation derives raw child membership independently of guards. -/
theorem validated_closed [DecidableEq Symbol] (table : Table State Symbol Payload) (root : State)
    (success : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) : Closed table := by
  have valid := (FTAValidation.validateRows_exact root _).mp success
  intro state edge member child childIn
  have present : edge.edge (fun _ _ => true) ∈ FTAValidation.rowFor (interpreted table (fun _ _ => true)) state := by
    rw [interpreted_lookup]
    exact List.mem_map.mpr ⟨edge, member, rfl⟩
  obtain ⟨edges, row, found⟩ := (FTAValidation.rowFor_exact _ _ _).mp present
  have inEdges : edge.edge (fun _ _ => true) ∈ FTAValidation.edges (interpreted table (fun _ _ => true)) :=
    List.mem_flatMap.mpr ⟨(state, edges), row, found⟩
  apply (mem_keys table child).mpr
  rw [← interpreted_keys table (fun _ _ => true)]
  exact valid.2.1 _ inEdges child childIn

/-- Successful validation derives the initial state's finite key membership. -/
theorem validated_root [DecidableEq Symbol] (table : Table State Symbol Payload) (root : State)
    (success : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) : root ∈ SourceDenseRows.keys table := by
  apply (mem_keys table root).mpr
  rw [← interpreted_keys table (fun _ _ => true)]
  exact ((FTAValidation.validateRows_exact root _).mp success).1

/-- Attach the derived key membership to each child without changing its position. -/
def restrictRow (table : Table State Symbol Payload) (closed : Closed table) (state : State)
    (edge : Row State Symbol Payload) (member : edge ∈ lookup table state) :
    Row (Member (SourceDenseRows.keys table)) Symbol Payload :=
  ⟨edge.label, edge.children.attach.map (fun child => ⟨child.val, closed state edge member child.val child.property⟩), edge.constraint⟩

/-- The finite row function reads the original complete alternative list. -/
def restricted (table : Table State Symbol Payload) (closed : Closed table)
    (state : Member (SourceDenseRows.keys table)) : List (Row (Member (SourceDenseRows.keys table)) Symbol Payload) :=
  (lookup table state.val).attach.map fun edge => restrictRow table closed state.val edge.val edge.property

/-- Forget only finite-carrier membership proofs. -/
def forget {keys : List State} (edge : Row (Member keys) Symbol Payload) : Row State Symbol Payload :=
  ⟨edge.label, edge.children.map Subtype.val, edge.constraint⟩

/-- Original row payload and complete child order survive restriction. -/
theorem forget_restrictRow (table : Table State Symbol Payload) (closed : Closed table) (state : State)
    (edge : Row State Symbol Payload) (member : edge ∈ lookup table state) :
    forget (restrictRow table closed state edge member) = edge := by
  cases edge
  simp [forget, restrictRow, List.map_map, Function.comp_def]

/-- Restriction retains repeated alternatives and their original order. -/
theorem rows_readback (table : Table State Symbol Payload) (closed : Closed table)
    (state : Member (SourceDenseRows.keys table)) :
    (restricted table closed state).map forget = lookup table state.val := by
  simp [restricted, List.map_map, Function.comp_def, forget_restrictRow]

/-- Constraint interpretation commutes with exact finite-carrier readback. -/
theorem ordered_readback (table : Table State Symbol Payload) (closed : Closed table)
    (holds : Payload → Term Symbol → Bool) (state : Member (SourceDenseRows.keys table)) :
    automaton (lookup table) holds state.val =
      (automaton (restricted table closed) holds state).map (SymbolicGraphView.renameEdge Subtype.val) := by
  rw [automaton, ←rows_readback table closed state]
  simp only [List.map_map, automaton, Function.comp_def]
  rfl

/-- Every guarded accepted term has exactly the original explicit-table meaning. -/
theorem accepts_exact (table : Table State Symbol Payload) (closed : Closed table)
    (holds : Payload → Term Symbol → Bool) (state : Member (SourceDenseRows.keys table)) (term : Term Symbol) :
    Accepts (automaton (restricted table closed) holds) state term ↔
      Accepts (automaton (lookup table) holds) state.val term := by
  symm
  apply SymbolicGraphView.rowsCorrespond_exact
  intro state edge
  rw [ordered_readback table closed holds state]
  simp only [List.mem_map, eq_comm]

/-- Every first-occurrence exact-size sequence survives finite restriction. -/
theorem classes_exact [DecidableEq Symbol] (table : Table State Symbol Payload) (closed : Closed table)
    (holds : Payload → Term Symbol → Bool) (state : Member (SourceDenseRows.keys table)) (size : Nat) :
    SourceSizedReference.classes (automaton (restricted table closed) holds) size state =
      SourceSizedReference.classes (automaton (lookup table) holds) size state.val :=
  (SourceDenseRowsRestrict.guarded_classes_rename _ _ Subtype.val (ordered_readback table closed holds) size state).symm

/-- Build every finite-domain public input field from a successful explicit FTA validation. -/
def input [DecidableEq Symbol] (table : Table State Symbol Payload) (root : State)
    (success : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) :
    SourceSizedPreprocessing.Input (Member (SourceDenseRows.keys table)) Symbol Payload where
  root := ⟨root, validated_root table root success⟩
  states := (SourceDenseRows.keys table).attach
  complete := member_complete _
  distinct := member_nodup _ (keys_nodup table)
  rows := restricted table (validated_closed table root success)

/-- The finite public input accepts exactly the source root language under arbitrary guards. -/
theorem input_language [DecidableEq Symbol] (table : Table State Symbol Payload) (root : State)
    (success : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) (holds : Payload → Term Symbol → Bool) (term : Term Symbol) :
    Accepts (automaton (input table root success).rows holds) (input table root success).root term ↔
      Accepts (automaton (lookup table) holds) root term :=
  accepts_exact table _ holds _ term

/-- Complete dense numbering computes exactly the canonical classes used by the finite public input. -/
theorem canonical_numbering [DecidableEq Symbol] [Ord Symbol] [TransOrd Symbol] [LawfulEqOrd Symbol]
    (table : Table State Symbol Payload) (root : State)
    (success : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) :
    CanonicalClasses.canonical (SourceDenseRowsCanonical.denseGraph (SourceDenseRows.keys table)
      (automaton (input table root success).rows (fun _ _ => true)) id) =
      (CanonicalClasses.canonical (SourceSizedPreprocessing.graph (input table root success))).map
        (fun classes index => classes (unnumber (SourceDenseRows.keys table) index)) := by
  have same : SourceDenseRowsCanonical.sourceGraph (SourceDenseRows.keys table) (keys_nodup table)
      (automaton (input table root success).rows (fun _ _ => true)) id =
      SourceSizedPreprocessing.graph (input table root success) := by
    unfold SourceDenseRowsCanonical.sourceGraph SourceSizedPreprocessing.graph
    simp only [automaton, List.map_map, Function.comp_def, Row.edge, id_eq]
    rfl
  rw [←same]
  exact SourceDenseRowsCanonical.canonical_numbering _ (keys_nodup table) _ id

end MicroCFTA.SourceSizedFiniteKeys
