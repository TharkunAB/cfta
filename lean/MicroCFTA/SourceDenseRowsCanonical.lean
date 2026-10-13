import MicroCFTA.SourceDenseRows
import MicroCFTA.SourceSizedDispatch

/-!
# Canonical classes and row order after dense numbering

automatonRows uses dense identities only for canonical refinement. It sorts
and returns the original transitions. The numeric map is constructed from
the key inventory. Its inverse laws derive the canonical renaming contract.
The supplied order key can identify different symbols; row symbols and
guards remain attached throughout the stable sort.
-/

namespace MicroCFTA.SourceDenseRowsCanonical

open Language SourceDenseRows CanonicalClasses SymbolicGraphView Std
attribute [local instance] lexOrd

variable [DecidableEq State]

/-- Canonical refinement on the finite original key carrier. -/
def sourceGraph (keys : List State) (unique : keys.Nodup)
    (rows : Automaton (Member keys) Symbol) (order : Symbol → Key) : Graph (Member keys) (Nat × Key) where
  nodes := keys.attach
  complete := member_complete keys
  distinct := member_nodup keys unique
  rows state := (rows state).map fun edge => ((edge.children.length, order edge.label), edge.children)

/-- Dense transitions rename only child states, retaining the complete row sequence. -/
def denseRows (keys : List State) (rows : Automaton (Member keys) Symbol) : Automaton (Fin keys.length) Symbol :=
  fun index => (rows (unnumber keys index)).map (renameEdge (number keys))

/-- The dense canonical domain is exactly the numbered IntMap key interval. -/
def denseGraph (keys : List State) (rows : Automaton (Member keys) Symbol) (order : Symbol → Key) :
    Graph (Fin keys.length) (Nat × Key) where
  nodes := List.finRange keys.length
  complete := by intro index; simp
  distinct := List.nodup_finRange _
  rows index := (denseRows keys rows index).map fun edge => ((edge.children.length, order edge.label), edge.children)

/-- The source dense map reads precisely the original outgoing transitions. -/
theorem denseRows_number (keys : List State) (rows : Automaton (Member keys) Symbol) (state : Member keys) :
    denseRows keys rows (number keys state) = (rows state).map (renameEdge (number keys)) := by
  simp [denseRows, unnumber_number]

/-- Derived map roundtrips provide every canonical graph renaming law. -/
def denseRenaming (keys : List State) (unique : keys.Nodup)
    (rows : Automaton (Member keys) Symbol) (order : Symbol → Key) :
    Renaming (sourceGraph keys unique rows order) (denseGraph keys rows order) where
  forward := number keys
  backward := unnumber keys
  left_inverse := unnumber_number keys
  right_inverse := number_unnumber keys unique
  rows := by
    intro state
    simp [sourceGraph, denseGraph, denseRows_number, List.map_map, Function.comp_def, renameEdge]

/-- Complete canonical refinement commutes with the concrete dense key numbering. -/
theorem canonical_numbering [DecidableEq Key] [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (keys : List State) (unique : keys.Nodup) (rows : Automaton (Member keys) Symbol) (order : Symbol → Key) :
    canonical (denseGraph keys rows order) =
      (canonical (sourceGraph keys unique rows order)).map (fun classes index => classes (unnumber keys index)) :=
  canonical_rename _ _ (denseRenaming keys unique rows order)

/-- Successful dense classes have the same numeric class at every original state. -/
theorem classes_at_number [DecidableEq Key] [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (keys : List State) (unique : keys.Nodup) (rows : Automaton (Member keys) Symbol) (order : Symbol → Key)
    (sourceClasses : Member keys → Nat) (denseClasses : Fin keys.length → Nat)
    (sourceDone : canonical (sourceGraph keys unique rows order) = some sourceClasses)
    (denseDone : canonical (denseGraph keys rows order) = some denseClasses) (state : Member keys) :
    denseClasses (number keys state) = sourceClasses state := by
  have same := canonical_numbering keys unique rows order
  rw [sourceDone, denseDone] at same
  have tables := Option.some.inj same
  simp [tables, unnumber_number]

/-- The exact source transition key retains arity, supplied order key, and ordered child classes. -/
def transitionKey (order : Symbol → Key) (classes : Node → Nat) (edge : Edge Node Symbol) :
    (Nat × Key) × List Nat :=
  ((edge.children.length, order edge.label), edge.children.map classes)

/-- The original transition has exactly the same sort key after dense canonical lookup. -/
theorem transitionKey_number [DecidableEq Key] [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (keys : List State) (unique : keys.Nodup) (rows : Automaton (Member keys) Symbol) (order : Symbol → Key)
    (sourceClasses : Member keys → Nat) (denseClasses : Fin keys.length → Nat)
    (sourceDone : canonical (sourceGraph keys unique rows order) = some sourceClasses)
    (denseDone : canonical (denseGraph keys rows order) = some denseClasses) (edge : Edge (Member keys) Symbol) :
    transitionKey order (fun child => denseClasses (number keys child)) edge = transitionKey order sourceClasses edge := by
  simp [transitionKey, classes_at_number keys unique rows order sourceClasses denseClasses sourceDone denseDone]

/-- Sort complete original transitions stably with the source triple key. -/
def sortRows [Ord Key] (rows : Automaton Node Symbol) (order : Symbol → Key) (classes : Node → Nat) :
    Automaton Node Symbol := fun state => (rows state).mergeSort fun first second =>
      (compare (transitionKey order classes first) (transitionKey order classes second)).isLE

/-- Dense canonical lookup preserves the exact sorted transitions, including equal-key ties. -/
theorem sorted_original [DecidableEq Key] [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (keys : List State) (unique : keys.Nodup) (rows : Automaton (Member keys) Symbol) (order : Symbol → Key)
    (sourceClasses : Member keys → Nat) (denseClasses : Fin keys.length → Nat)
    (sourceDone : canonical (sourceGraph keys unique rows order) = some sourceClasses)
    (denseDone : canonical (denseGraph keys rows order) = some denseClasses) :
    sortRows rows order (fun child => denseClasses (number keys child)) = sortRows rows order sourceClasses := by
  have same : (fun child => denseClasses (number keys child)) = sourceClasses :=
    funext (classes_at_number keys unique rows order sourceClasses denseClasses sourceDone denseDone)
  rw [same]

/-- Stable sorting commutes with renaming even when the supplied symbol keys collide. -/
theorem sorted_dense [DecidableEq Key] [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (keys : List State) (unique : keys.Nodup) (rows : Automaton (Member keys) Symbol) (order : Symbol → Key)
    (sourceClasses : Member keys → Nat) (denseClasses : Fin keys.length → Nat)
    (sourceDone : canonical (sourceGraph keys unique rows order) = some sourceClasses)
    (denseDone : canonical (denseGraph keys rows order) = some denseClasses) (state : Member keys) :
    sortRows (denseRows keys rows) order denseClasses (number keys state) =
      (sortRows rows order sourceClasses state).map (renameEdge (number keys)) := by
  unfold sortRows
  rw [denseRows_number]
  symm
  apply List.map_mergeSort
  intro first _ second _
  simp only [transitionKey, renameEdge, List.length_map, List.map_map, Function.comp_def]
  simp only [classes_at_number keys unique rows order sourceClasses denseClasses sourceDone denseDone]

/-- The current automatonRows worker computes dense classes and sorts original transitions. -/
def prepare [DecidableEq Key] [Ord Key]
    (keys : List State) (rows : Automaton (Member keys) Symbol) (order : Symbol → Key) :
    Option (Automaton (Member keys) Symbol) :=
  (canonical (denseGraph keys rows order)).map fun classes =>
    sortRows rows order (fun child => classes (number keys child))

/-- The public dense preparation finishes on every finite key inventory. -/
theorem prepare_complete [DecidableEq Key] [Ord Key]
    (keys : List State) (rows : Automaton (Member keys) Symbol) (order : Symbol → Key) :
    ∃ output, prepare keys rows order = some output := by
  obtain ⟨classes, completed⟩ := canonical_terminates (denseGraph keys rows order)
  exact ⟨sortRows rows order (fun child => classes (number keys child)), by simp [prepare, completed]⟩

/-- Successful source preparation is the exact original-state canonical row sequence. -/
theorem prepare_source [DecidableEq Key] [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (keys : List State) (unique : keys.Nodup) (rows : Automaton (Member keys) Symbol) (order : Symbol → Key)
    (output : Automaton (Member keys) Symbol) (prepared : prepare keys rows order = some output) :
    ∃ classes, canonical (sourceGraph keys unique rows order) = some classes ∧
      output = sortRows rows order classes := by
  obtain ⟨sourceClasses, sourceDone⟩ := canonical_terminates (sourceGraph keys unique rows order)
  obtain ⟨denseClasses, denseDone, outputEq⟩ := Option.map_eq_some_iff.mp prepared
  exact ⟨sourceClasses, sourceDone, outputEq.symm.trans
    (sorted_original keys unique rows order sourceClasses denseClasses sourceDone denseDone)⟩

/-- Source preparation changes row order only and retains every stored guard and symbol. -/
theorem prepare_perm [DecidableEq Key] [Ord Key]
    (keys : List State) (rows : Automaton (Member keys) Symbol) (order : Symbol → Key)
    (output : Automaton (Member keys) Symbol) (prepared : prepare keys rows order = some output)
    (state : Member keys) : (output state).Perm (rows state) := by
  obtain ⟨classes, _, same⟩ := Option.map_eq_some_iff.mp prepared
  subst output
  exact List.mergeSort_perm _ _

/-- Canonical dense rows and original-state rows enumerate exactly the same ordered runs at every size. -/
theorem dense_sequence [DecidableEq Key] [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (keys : List State) (unique : keys.Nodup) (rows : Automaton (Member keys) Symbol) (order : Symbol → Key)
    (sourceClasses : Member keys → Nat) (denseClasses : Fin keys.length → Nat)
    (sourceDone : canonical (sourceGraph keys unique rows order) = some sourceClasses)
    (denseDone : canonical (denseGraph keys rows order) = some denseClasses) (size : Nat) (state : Member keys) :
    RecursiveSize.enumerate (sortRows (denseRows keys rows) order denseClasses) size (number keys state) =
      RecursiveSize.enumerate (sortRows rows order sourceClasses) size state :=
  SourceSizedDispatch.enumerate_ordered_rows _ _ (number keys)
    (sorted_dense keys unique rows order sourceClasses denseClasses sourceDone denseDone) size state

/-- Dense numbering preserves count-table counts, ordered terms, and every signed rank selection. -/
theorem dense_queries [DecidableEq Key] [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (keys : List State) (unique : keys.Nodup) (rows : Automaton (Member keys) Symbol) (order : Symbol → Key)
    (sourceClasses : Member keys → Nat) (denseClasses : Fin keys.length → Nat)
    (sourceDone : canonical (sourceGraph keys unique rows order) = some sourceClasses)
    (denseDone : canonical (denseGraph keys rows order) = some denseClasses) (state : Member keys) :
    (∀ size, SourceSizedDispatch.terms (sortRows (denseRows keys rows) order denseClasses) (number keys state) size =
      RecursiveSize.enumerate (sortRows rows order sourceClasses) size state) ∧
    (∀ size, RecursiveSize.countAt (sortRows (denseRows keys rows) order denseClasses) size (number keys state) =
      (RecursiveSize.enumerate (sortRows rows order sourceClasses) size state).length) ∧
    (∀ size rank, SourceSizedDispatch.select (sortRows (denseRows keys rows) order denseClasses)
      (number keys state) size rank = if 0 ≤ rank then
        (RecursiveSize.enumerate (sortRows rows order sourceClasses) size.toNat state)[rank.toNat]? else none) :=
  SourceSizedDispatch.queries_ordered_rows _ _ (number keys)
    (sorted_dense keys unique rows order sourceClasses denseClasses sourceDone denseDone) state

end MicroCFTA.SourceDenseRowsCanonical
