import MicroCFTA.SourceSizedDeterminizationTableInput

/-!
# Literal found-set and difference readback

The source computes found keys with its zip target, then removes known
keys with set difference. Original table keys derive literal target
equality. Distinct found-set readback makes the controller's duplicate
removal redundant. The resulting fresh list is the source ordered filter.
These laws concern values, not native container storage or machine sizes.
-/
namespace MicroCFTA.SourceSizedDeterminizationSetDifference
open Language SourceSizedDeterminizationKernel SourceSizedDeterminizationDiscovery Std
attribute [local instance] lexOrd

/-- Removing duplicates retains a list that already has distinct entries. -/
theorem eraseDups_eq_self {Key : Type} [BEq Key] [LawfulBEq Key]
    (keys : List Key) (distinct : keys.Nodup) : keys.eraseDups = keys := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    have facts := List.nodup_cons.mp distinct
    rw [List.eraseDups_cons]
    have retained : rest.filter (fun other => !other == key) = rest := by
      apply List.filter_eq_self.mpr
      intro other member
      have different : other ≠ key := fun same => facts.1 (same ▸ member)
      simp [different]
    rw [retained, ih facts.2]

/-- A distinct found-set list needs only the source known-membership filter. -/
theorem fresh_filter {Key : Type} [DecidableEq Key] (known found : List Key)
    (distinct : found.Nodup) :
    fresh known found = found.filter (fun key => decide (key ∉ known)) := by
  unfold fresh
  rw [eraseDups_eq_self found distinct]

variable {State Symbol Payload : Type} [DecidableEq State] [DecidableEq Symbol] [Ord State]

/-- Read found-map keys from literal source zip targets of its emitted choices. -/
def foundKeys (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (choices : List (Choice State Symbol)) : List (List State) :=
  CanonicalClasses.sortedSet (choices.map fun choice =>
    SourceSizedDeterminizationZipTarget.sourceTarget (SourceDenseRows.keys table)
      (SourceSizedDeterminizationTableInput.rows table) (choice.1, choice.2.length) choice.2)

variable [TransOrd State] [LawfulEqOrd State]

/-- Literal source targets give exactly the controller's ordered found keys. -/
theorem foundKeys_readback (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (choices : List (Choice State Symbol)) :
    foundKeys table choices = SourceSizedDeterminizationOrderedRun.foundKeys
      (SourceDenseRows.keys table) (SourceSizedDeterminizationTableInput.rows table) choices := by
  unfold foundKeys SourceSizedDeterminizationOrderedRun.foundKeys SourceSizedDeterminizationRun.targets
  congr 1
  apply List.map_congr_left
  intro choice _
  exact SourceSizedDeterminizationTableInput.source_target_readback table
    (choice.1, choice.2.length) choice.2 rfl

/-- Every source-loop freshness check is the literal ordered set-difference filter. -/
theorem fresh_readback (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (known : List (List State)) (choices : List (Choice State Symbol)) :
    fresh known (SourceSizedDeterminizationOrderedRun.foundKeys
      (SourceDenseRows.keys table) (SourceSizedDeterminizationTableInput.rows table) choices) =
      (foundKeys table choices).filter (fun key => decide (key ∉ known)) := by
  rw [← foundKeys_readback table choices]
  apply (fresh_filter known (foundKeys table choices) (CanonicalClasses.sortedSet_nodup _)).trans
  apply List.filter_congr
  intro key _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

end MicroCFTA.SourceSizedDeterminizationSetDifference
