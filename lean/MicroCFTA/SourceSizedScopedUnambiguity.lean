import MicroCFTA.SourceSizedCurrentUnambiguity
import MicroCFTA.SourceSizedScopedTrimClosure
import MicroCFTA.SourceSizedTrimRunClasses

/-!
# Unambiguity on the actual scoped trimmed table

The source erases constraints after trimming at the query state. Its key
shortcut and product scan run on that retained table. Current structural
validation derives the retained root, child closure, and finite key carrier.

A passing check gives distinct raw classes at the original query root.
Every transport preserves row order and repeated runs. The raw state type
need not be finite. No global original uniqueness or plainness is assumed.
Native container storage and execution work remain separate.
-/
namespace MicroCFTA.SourceSizedScopedUnambiguity
open Language SourceSizedDecided SourceSizedFiniteKeys SourceDenseRows Std
open SourceSizedScopedTrimInventory

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State]

/-- The actual retained table has the same ascending keys as its trim inventory. -/
theorem keys_readback [TransOrd State] [LawfulEqOrd State]
    (table : Table State Symbol Payload) (root : State) :
    keys (trimmedTable table root) = inventory table root := by
  unfold keys
  rw [trimmedTable_keys]
  exact SourceSizedDeterminizationTargetReadback.sortedSet_eq_self _
    (inventory_nodup table root)
    ((SourceSizedDeterminizationTableInput.keys_ordered table).filter _)

/-- Construct the finite input from the validated actual trimmed table. -/
def input (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) :=
  SourceSizedStructuralKeys.input (trimmedTable table root) root
    (SourceSizedScopedTrimClosure.validated_trimmed table root success)

/-- Finite-carrier rows retain the exact source trimmed row sequence. -/
theorem input_readback (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (state : Member (keys (trimmedTable table root))) :
    automaton (lookup (trimmedTable table root)) (fun _ _ => true) state.val =
      (automaton (input table root success).rows (fun _ _ => true) state).map
        (SymbolicGraphView.renameEdge Subtype.val) :=
  ordered_readback (trimmedTable table root) _ (fun _ _ => true) state

/-- Erased constraints make every row of the actual finite gate graph plain. -/
theorem input_plain (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) :
    Decoder.Plain (automaton (input table root success).rows (fun _ _ => true)) :=
  SourceSizedDispatcher.ordinary_plain _

/-- Actual retained-row lookup interprets exactly the structural trimmed graph. -/
theorem trimmed_automaton (table : Table State Symbol Payload) (root : State) :
    automaton (lookup (trimmedTable table root)) (fun _ _ => true) =
      GraphTrim.trim (keys table) (SourceSizedDeterminizationTableInput.rows table) root := by
  unfold SourceSizedDeterminizationTableInput.rows
  rw [SourceSizedTrimGuards.trim_interpretation]
  funext state
  simp only [automaton, trimmed_lookup]

variable [DecidableEq Symbol]

/-- Run both source check branches on the actual retained finite map keys. -/
def unambiguousRows (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) : Bool :=
  SourceSizedCurrentUnambiguity.unambiguousRows
    (automaton (input table root success).rows (fun _ _ => true))
    (input table root success).states (input table root success).complete

/-- A passing actual scoped check gives distinct root runs in the raw trimmed table. -/
theorem trimmed_root_unique (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : unambiguousRows table root success = true) (size : Nat) :
    (RecursiveSize.enumerate
      (automaton (lookup (trimmedTable table root)) (fun _ _ => true)) size root).Nodup := by
  have unique := SourceSizedCurrentUnambiguity.gate_unique
    (automaton (input table root success).rows (fun _ _ => true)) (input_plain table root success)
    (input table root success).states (input table root success).complete passed
  have readback := SourceSizedDispatch.enumerate_ordered_rows _ _ Subtype.val
    (input_readback table root success) size (input table root success).root
  exact readback.symm ▸ unique (input table root success).root size

/-- The actual scoped gate derives original root uniqueness without global uniqueness. -/
theorem root_unique (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : unambiguousRows table root success = true) (size : Nat) :
    (RecursiveSize.enumerate (SourceSizedDeterminizationTableInput.rows table) size root).Nodup := by
  let closed := SourceSizedStructuralKeys.validated_closed table root success
  let finiteRoot : Member (keys table) :=
    ⟨root, SourceSizedStructuralKeys.validated_root table root success⟩
  let source := automaton (restricted table closed) (fun _ _ => true)
  let trimmed := GraphTrim.trim (keys table).attach source finiteRoot
  have unique := trimmed_root_unique table root success passed size
  rw [trimmed_automaton] at unique
  have trimmedReadback := SourceSizedDispatch.enumerate_ordered_rows trimmed
    (GraphTrim.trim (keys table) (SourceSizedDeterminizationTableInput.rows table) root)
    Subtype.val (SourceSizedFiniteKeysTrim.restricted_trim table closed (fun _ _ => true) finiteRoot)
    size finiteRoot
  have originalReadback := SourceSizedDispatch.enumerate_ordered_rows source
    (SourceSizedDeterminizationTableInput.rows table) Subtype.val
    (ordered_readback table closed (fun _ _ => true)) size finiteRoot
  exact originalReadback.symm ▸
    (SourceSizedTrimRunClasses.trim_enumerate
      (keys table).attach (member_complete (keys table)) source finiteRoot size ▸
      (trimmedReadback ▸ unique))

end MicroCFTA.SourceSizedScopedUnambiguity
