import MicroCFTA.SourceSizedFiniteKeysTrimTransport

/-!
# The actual raw-map state inventory of Sized

Validation supplies every child and root key. The original raw graph and
its finite key restriction compute exactly the same ordered trim inventory.
The native bounded fold therefore uses the actual raw trim keys directly.
-/
namespace MicroCFTA.SourceSizedFiniteKeysTrim
open Language SourceSizedDecided SourceDenseRows SourceSizedFiniteKeys

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State]

/-- Structural productivity on the actual raw keys agrees with the finite restriction. -/
theorem restricted_productive (table : SourceSizedFiniteKeys.Table State Symbol Payload) (closed : Closed table)
    (holds : Payload → Term Symbol → Bool) (state : Member (SourceDenseRows.keys table)) :
    Productivity.productive (SourceDenseRows.keys table) (automaton (lookup table) holds) state.val =
      Productivity.productive (SourceDenseRows.keys table).attach (automaton (restricted table closed) holds) state := by
  simpa only [List.attach_map_subtype_val] using
    SourceSizedFiniteKeysTrimTransport.productive_readback Subtype.val
      (automaton (restricted table closed) holds) (automaton (lookup table) holds)
      (ordered_readback table closed holds) (SourceDenseRows.keys table).attach state

/-- The original raw live-successor closure agrees at every finite key. -/
theorem restricted_reach (table : SourceSizedFiniteKeys.Table State Symbol Payload) (closed : Closed table)
    (holds : Payload → Term Symbol → Bool) (root state : Member (SourceDenseRows.keys table)) :
    Productivity.reachClosure (SourceDenseRows.keys table)
      (Productivity.successors (GraphTrim.live (SourceDenseRows.keys table) (automaton (lookup table) holds))) [root.val] state.val =
      Productivity.reachClosure (SourceDenseRows.keys table).attach
        (Productivity.successors (GraphTrim.live (SourceDenseRows.keys table).attach (automaton (restricted table closed) holds)))
        [root] state := by
  simpa only [List.attach_map_subtype_val, List.map_cons, List.map_nil] using
    SourceSizedFiniteKeysTrimTransport.reachClosure_readback Subtype.val (fun _ _ same => Subtype.ext same)
      (SourceDenseRows.keys table).attach [root]
      (Productivity.successors (GraphTrim.live (SourceDenseRows.keys table).attach (automaton (restricted table closed) holds)))
      (Productivity.successors (GraphTrim.live ((SourceDenseRows.keys table).attach.map Subtype.val) (automaton (lookup table) holds)))
      (SourceSizedFiniteKeysTrimTransport.successors_readback Subtype.val
        (automaton (restricted table closed) holds) (automaton (lookup table) holds)
        (ordered_readback table closed holds) (SourceDenseRows.keys table).attach) state

/-- Exact validated row readback derives the complete raw root-preserving trim inventory. -/
theorem restricted_trimKeys (table : SourceSizedFiniteKeys.Table State Symbol Payload) (closed : Closed table)
    (holds : Payload → Term Symbol → Bool) (root : Member (SourceDenseRows.keys table)) :
    SourceSizedDecidedTrim.trimKeys (SourceDenseRows.keys table) (automaton (lookup table) holds) root.val =
      (SourceSizedDecidedTrim.trimKeys (SourceDenseRows.keys table).attach
        (automaton (restricted table closed) holds) root).map Subtype.val := by
  simpa only [List.attach_map_subtype_val] using
    SourceSizedFiniteKeysTrimTransport.trimKeys_readback Subtype.val (fun _ _ same => Subtype.ext same)
      (automaton (restricted table closed) holds) (automaton (lookup table) holds)
      (ordered_readback table closed holds) (SourceDenseRows.keys table).attach root

/-- Complete guarded trim rows retain exact original child and alternative order. -/
theorem restricted_trim (table : SourceSizedFiniteKeys.Table State Symbol Payload) (closed : Closed table)
    (holds : Payload → Term Symbol → Bool) (root state : Member (SourceDenseRows.keys table)) :
    GraphTrim.trim (SourceDenseRows.keys table) (automaton (lookup table) holds) root.val state.val =
      (GraphTrim.trim (SourceDenseRows.keys table).attach (automaton (restricted table closed) holds) root state).map
        (SymbolicGraphView.renameEdge Subtype.val) := by
  simpa only [List.attach_map_subtype_val] using
    SourceSizedFiniteKeysTrimTransport.trim_readback Subtype.val (fun _ _ same => Subtype.ext same)
      (automaton (restricted table closed) holds) (automaton (lookup table) holds)
      (ordered_readback table closed holds) (SourceDenseRows.keys table).attach root state

/-- Structural trimming retains the complete raw constraints and row order under readback. -/
theorem trimmedRows_readback (table : SourceSizedFiniteKeys.Table State Symbol Payload) (closed : Closed table)
    (root state : Member (SourceDenseRows.keys table)) :
    (SourceSizedTrimGuards.trimmedRows (restricted table closed) (SourceDenseRows.keys table).attach root state).map forget =
      SourceSizedTrimGuards.trimmedRows (lookup table) (SourceDenseRows.keys table) root.val state.val := by
  dsimp only [SourceSizedTrimGuards.trimmedRows]
  rw [restricted_productive table closed (fun _ _ => true) state,
    restricted_reach table closed (fun _ _ => true) root state]
  split
  · rw [←rows_readback table closed state, List.filter_map]
    simp only [Function.comp_def, forget, List.all_map,
      restricted_productive table closed (fun _ _ => true)]
  · rfl

/-- The public finite inventory equals the actual raw trim keys under every guard interpretation. -/
theorem reached_readback [DecidableEq Symbol]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) (holds : Payload → Term Symbol → Bool) :
    (SourceSizedDecidedPublic.reached (input table root valid)).map Subtype.val =
      SourceSizedDecidedTrim.trimKeys (SourceDenseRows.keys table) (automaton (lookup table) holds) root := by
  rw [SourceSizedDecidedPublic.reached_interpretation (input table root valid) holds]
  exact (restricted_trimKeys table (validated_closed table root valid) holds
    ⟨root, validated_root table root valid⟩).symm

/-- A validated raw root remains in the state fold even when it is unproductive. -/
theorem root_mem [DecidableEq Symbol]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) (holds : Payload → Term Symbol → Bool) :
    root ∈ SourceSizedDecidedTrim.trimKeys (SourceDenseRows.keys table) (automaton (lookup table) holds) root := by
  simp [SourceSizedDecidedTrim.trimKeys, validated_root table root valid]

/-- Raw trim preserves the original map-key order and never repeats a state. -/
theorem inventory_order (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (root : State) (holds : Payload → Term Symbol → Bool) :
    (SourceSizedDecidedTrim.trimKeys (SourceDenseRows.keys table) (automaton (lookup table) holds) root).Sublist
        (SourceDenseRows.keys table) ∧
      (SourceSizedDecidedTrim.trimKeys (SourceDenseRows.keys table) (automaton (lookup table) holds) root).Nodup := by
  exact ⟨List.filter_sublist, (keys_nodup table).filter _⟩

open Std
attribute [local instance] lexOrd

/-- Actual raw trim keys and actual dense sorted rows compute the same bounded public result. -/
theorem native_public [DecidableEq Symbol] [Ord Symbol] [TransOrd Symbol] [LawfulEqOrd Symbol]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (holds : Payload → Term Symbol → Bool) (answer : Payload × Term Symbol → Guards.Verdict) (bound : Int) :
    (sizedUpToSigned (nativeSorted table root valid)
      (SourceSizedDecidedTrim.trimKeys (SourceDenseRows.keys table) (automaton (lookup table) holds) root)
      answer bound).map (SourceSizedFiniteKeysExecution.pull Subtype.val) =
      SourceSizedDecidedPublic.publicSizedUpTo (input table root valid) answer bound := by
  rw [←reached_readback table root valid holds]
  exact SourceSizedFiniteKeysExecution.native_public table root valid answer bound

end MicroCFTA.SourceSizedFiniteKeysTrim
