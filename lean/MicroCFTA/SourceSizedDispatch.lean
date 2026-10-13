import MicroCFTA.SourceCyclicAutomaton
import MicroCFTA.CanonicalClasses
import MicroCFTA.SourceSizedReference

/-!
# The optimized Sized query adapter

The count-table branch checks every requested class rank before selection.
Listing all checked ranks reconstructs the exact ordered class. Structural
row correspondence must preserve order. Language equivalence alone does
not imply this correspondence. In particular, `fromFTA` trims its input.
-/
namespace MicroCFTA.SourceSizedDispatch
open Language RecursiveSize SizedRank SymbolicGraphView

/-- Selecting all list positions in ascending order recovers the list. -/
theorem range_select (values : List α) :
    (List.range values.length).filterMap (fun rank => values[rank]?) = values := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      simpa [List.range_succ_eq_map, List.filterMap_map, Function.comp_def] using
        congrArg (List.cons value) ih

/-- The source optimized selector checks signed ranks against its class count. -/
def select (automaton : Automaton State Symbol) (root : State) (size rank : Int) :
    Option (Term Symbol) :=
  if 0 ≤ rank ∧ rank.toNat < countAt automaton size.toNat root then
    replayPosition automaton root ⟨size.toNat, rank.toNat⟩
  else none

/-- The source count-table selector reads precisely the valid class position. -/
theorem select_exact (automaton : Automaton State Symbol) (root : State) (size rank : Int) :
    select automaton root size rank =
      if 0 ≤ rank then (RecursiveSize.enumerate automaton size.toNat root)[rank.toNat]? else none := by
  by_cases nonnegative : 0 ≤ rank
  · by_cases valid : rank.toNat < countAt automaton size.toNat root
    · simp [select, nonnegative, valid, replayPosition, decode_compileAt]
    · have outside : (RecursiveSize.enumerate automaton size.toNat root).length ≤ rank.toNat := by
        rw [← countAt_correct]
        omega
      simp [select, nonnegative, valid, List.getElem?_eq_none outside]
  · simp [select, nonnegative]

/-- Zero and negative sizes have empty count-table classes. -/
theorem select_nonpositive (automaton : Automaton State Symbol) (root : State) (size rank : Int)
    (nonpositive : size ≤ 0) : select automaton root size rank = none := by
  rw [select_exact]
  have zero : size.toNat = 0 := Int.toNat_eq_zero.mpr nonpositive
  simp [zero, enumerate_zero]

/-- The source list comprehension traverses the complete valid class interval. -/
def terms (automaton : Automaton State Symbol) (root : State) (size : Nat) : List (Term Symbol) :=
  (List.range (countAt automaton size root)).filterMap fun rank =>
    select automaton root (Int.ofNat size) (Int.ofNat rank)

/-- The optimized terms query reconstructs the original ordered table class. -/
theorem terms_exact (automaton : Automaton State Symbol) (root : State) (size : Nat) :
    terms automaton root size = RecursiveSize.enumerate automaton size root := by
  simp only [terms, select_exact, countAt_correct]
  exact range_select _

/-- Renaming ordered child references leaves the nested product sequence unchanged. -/
theorem forests_rename (source : Nat → Source → List (Term Symbol))
    (target : Nat → Target → List (Term Symbol)) (encode : Source → Target)
    (same : ∀ size state, target size (encode state) = source size state)
    (states : List Source) :
    forests target (states.map encode) = forests source states := by
  induction states using snoc_induction with
  | empty => rfl
  | step states state ih =>
      simp only [List.map_append, List.map_singleton, forests_snoc, ih]
      congr 1
      funext size
      exact same size state

/-- Exact ordered row readback preserves every run and its size-class position.
This is an adapter obligation, not a claim about the current interned constructor. -/
theorem enumerate_ordered_rows (source : Automaton Source Symbol)
    (target : Automaton Target Symbol) (encode : Source → Target)
    (rows : ∀ state, target (encode state) = (source state).map (renameEdge encode))
    (size : Nat) (state : Source) :
    RecursiveSize.enumerate target size (encode state) = RecursiveSize.enumerate source size state := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
      cases size with
      | zero => simp [enumerate_zero]
      | succ budget =>
          rw [RecursiveSize.enumerate, RecursiveSize.enumerate, rows]
          simp only [List.flatMap_map]
          apply TablePosition.flatMap_congr
          intro edge _
          dsimp only [Function.comp_def, renameEdge]
          congr 1
          apply congrFun (forests_rename _ _ encode ?_ edge.children) budget
          intro childSize child
          by_cases smaller : childSize ≤ budget
          · simp only [dite_eq_left smaller]
            exact ih childSize (by omega) child
          · simp only [dite_eq_right smaller]

/-- Ordered row readback also fixes counts and every signed selection query. -/
theorem queries_ordered_rows (source : Automaton Source Symbol)
    (target : Automaton Target Symbol) (encode : Source → Target)
    (rows : ∀ state, target (encode state) = (source state).map (renameEdge encode))
    (state : Source) :
    (∀ size, terms target (encode state) size = RecursiveSize.enumerate source size state) ∧
    (∀ size, countAt target size (encode state) = (RecursiveSize.enumerate source size state).length) ∧
    (∀ size rank, select target (encode state) size rank =
      if 0 ≤ rank then (RecursiveSize.enumerate source size.toNat state)[rank.toNat]? else none) := by
  refine ⟨?_, ?_, ?_⟩
  · intro size
    rw [terms_exact, enumerate_ordered_rows source target encode rows]
  · intro size
    rw [countAt_correct, enumerate_ordered_rows source target encode rows]
  · intro size rank
    rw [select_exact, enumerate_ordered_rows source target encode rows]

/-- A successful cyclic precheck gives both inverse laws for optimized class queries. -/
theorem compiled_queries [DecidableEq State] [DecidableEq Formula]
    (formulas : SourceGuards.Formulas Formula) (solver : SourceGuards.Entailment Formula)
    (input : SourceCyclicAutomaton.Input State Formula)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs)
    (output : Automaton State (SourceObservations.Label Formula))
    (success : SourceCyclicAutomaton.compile formulas solver input pairs complete = .ok output) :
    (∀ size, terms output input.root size = RecursiveSize.enumerate output size input.root) ∧
    (∀ position term, TablePosition.positionsOf output term input.root = some position ↔
      select output input.root (Int.ofNat position.size) (Int.ofNat position.rank) = some term) := by
  refine ⟨terms_exact output input.root, ?_⟩
  intro position term
  rw [(SourceCyclicAutomaton.exact_index_api formulas solver input pairs complete output success).1]
  rw [select_exact]
  simp [replayPosition, decode_compileAt]

/-- The optimized branch agrees with the source reference under exact ordered
row readback. Cyclic prechecks derive plainness and uniqueness. The remaining
premise is the `fromFTA`, `rowsOf`, and canonical-sort adapter obligation. -/
theorem compiled_reference_agreement [DecidableEq State] [DecidableEq Formula]
    (formulas : SourceGuards.Formulas Formula) (solver : SourceGuards.Entailment Formula)
    (input : SourceCyclicAutomaton.Input State Formula)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs)
    (output : Automaton State (SourceObservations.Label Formula))
    (success : SourceCyclicAutomaton.compile formulas solver input pairs complete = .ok output)
    (source : Automaton Source (SourceObservations.Label Formula)) (encode : Source → State)
    (rows : ∀ state, output (encode state) = (source state).map (renameEdge encode))
    (root : Source) (rootReadback : input.root = encode root) :
    (∀ size, terms output input.root size = SourceSizedReference.classes source size root) ∧
    (∀ size, countAt output size input.root = (SourceSizedReference.classes source size root).length) ∧
    (∀ size rank, select output input.root size rank =
      if 0 ≤ rank then (SourceSizedReference.classes source size.toNat root)[rank.toNat]? else none) ∧
    (∀ term, TablePosition.positionsOf output term input.root =
      (rankOf (SourceSizedReference.classes source (nodeSize term) root) term).map
        (fun rank => (⟨nodeSize term, rank⟩ : Position))) := by
  obtain ⟨plain, unique, _⟩ :=
    SourceCyclicAutomaton.compile_exact formulas solver input pairs complete output success
  have sourcePlain : Decoder.Plain source := by
    intro state edge member term
    have present : renameEdge encode edge ∈ output (encode state) := by
      rw [rows]
      exact List.mem_map.mpr ⟨edge, member, rfl⟩
    exact plain (encode state) (renameEdge encode edge) present term
  have sourceUnique : Unambiguous source := by
    intro state size
    rw [← enumerate_ordered_rows source output encode rows]
    exact unique (encode state) size
  have reference := SourceSizedReference.classes_eq_enumerate source sourcePlain sourceUnique
  rw [rootReadback]
  obtain ⟨listed, counted, selected⟩ := queries_ordered_rows source output encode rows root
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro size
    rw [reference]
    exact listed size
  · intro size
    rw [reference]
    exact counted size
  · intro size rank
    rw [reference]
    exact selected size rank
  · intro term
    rw [TablePosition.positionsOf_eq_termPosition output plain unique, termPosition,
      enumerate_ordered_rows source output encode rows, reference]
    rfl

end MicroCFTA.SourceSizedDispatch
