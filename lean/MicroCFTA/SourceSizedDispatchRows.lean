import MicroCFTA.SourceSizedDispatch
import MicroCFTA.SourceSizedRows

/-!
# Canonical sorting in an ordered representation adapter

Raw row readback and a bijective change of state identities suffice for
the complete sorted-row sequence. Canonical numbering and sorting are
proved here. The hypotheses describe a sufficient representation adapter;
they do not assert that `fromFTA` satisfies them for every input. Interning
can identify distinct states, so that constructor needs a more general
quotient proof as well as its completion proof.
-/
namespace MicroCFTA.SourceSizedDispatchRows
open Language SourceSizedRows SymbolicGraphView CanonicalClasses Std
attribute [local instance] lexOrd

/-- An ordered raw-row adapter changes state identities and retains each guard. -/
structure Readback (source : Input Source Symbol) (target : Input Target Symbol) where
  forward : Source → Target
  backward : Target → Source
  left_inverse : ∀ state, backward (forward state) = state
  right_inverse : ∀ state, forward (backward state) = state
  rows : ∀ state, target.rows (forward state) = (source.rows state).map (renameEdge forward)

/-- Ordered raw-row readback supplies the canonical graph renaming contract. -/
def Readback.renaming {source : Input Source Symbol} {target : Input Target Symbol}
    (readback : Readback source target) : Renaming (graph source) (graph target) where
  forward := readback.forward
  backward := readback.backward
  left_inverse := readback.left_inverse
  right_inverse := readback.right_inverse
  rows := by
    intro state
    dsimp only [graph]
    rw [readback.rows]
    simp only [List.map_map, Function.comp_def, renameEdge, List.length_map]
    exact List.Perm.refl _

/-- Transported canonical classes give the same complete source row key. -/
theorem rowKey_rename {source : Input Source Symbol} {target : Input Target Symbol}
    (readback : Readback source target) (classes : Source → Nat) (edge : Edge Source Symbol) :
    rowKey (transport readback.renaming classes) (renameEdge readback.forward edge) =
      rowKey classes edge := by
  simp [rowKey, transport, Readback.renaming, renameEdge, List.map_map,
    Function.comp_def, readback.left_inverse]

/-- Stable row sorting commutes with the proved canonical class transport. -/
theorem sortedRows_rename [Ord Symbol]
    {source : Input Source Symbol} {target : Input Target Symbol}
    (readback : Readback source target) (classes : Source → Nat) (state : Source) :
    sortedRows target (transport readback.renaming classes) (readback.forward state) =
      (sortedRows source classes state).map (renameEdge readback.forward) := by
  unfold sortedRows
  rw [readback.rows]
  symm
  apply List.map_mergeSort
  intro first _ second _
  rw [rowKey_rename, rowKey_rename]

/-- Successful finite canonical preprocessing preserves the ordered raw-row adapter. -/
theorem prepare_readback [DecidableEq Symbol] [Ord Symbol] [TransOrd Symbol] [LawfulEqOrd Symbol]
    {source : Input Source Symbol} {target : Input Target Symbol}
    (readback : Readback source target)
    (sourceRows : Automaton Source Symbol) (targetRows : Automaton Target Symbol)
    (sourceDone : prepare source = some sourceRows) (targetDone : prepare target = some targetRows)
    (state : Source) :
    targetRows (readback.forward state) = (sourceRows state).map (renameEdge readback.forward) := by
  obtain ⟨classes, done, sourceSame⟩ := Option.map_eq_some_iff.mp sourceDone
  have renamed := canonical_rename (graph source) (graph target) readback.renaming
  rw [done] at renamed
  have targetSame : sortedRows target (transport readback.renaming classes) = targetRows := by
    exact Option.some.inj (by simpa only [prepare, renamed, Option.map_some] using targetDone)
  rw [← sourceSame, ← targetSame]
  exact sortedRows_rename readback classes state

/-- Canonical preprocessing followed by count-table construction preserves each sequence. -/
theorem prepared_sequence [DecidableEq Symbol] [Ord Symbol] [TransOrd Symbol] [LawfulEqOrd Symbol]
    {source : Input Source Symbol} {target : Input Target Symbol}
    (readback : Readback source target)
    (sourceRows : Automaton Source Symbol) (targetRows : Automaton Target Symbol)
    (sourceDone : prepare source = some sourceRows) (targetDone : prepare target = some targetRows)
    (size : Nat) (state : Source) :
    SourceSizedDispatch.terms targetRows (readback.forward state) size =
      RecursiveSize.enumerate sourceRows size state := by
  rw [SourceSizedDispatch.terms_exact]
  exact SourceSizedDispatch.enumerate_ordered_rows sourceRows targetRows readback.forward
    (prepare_readback readback sourceRows targetRows sourceDone targetDone) size state

end MicroCFTA.SourceSizedDispatchRows
