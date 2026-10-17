import MicroCFTA.SourceCurrentConstrainedCapRequiredScanResources

/-!
# Initial numeric bounds for supported Required node graphs

The original Needed size bounds child recursion. A recursive input uses
its anchored support to derive a same-heap warm Head certificate. The
ordinary phase fixes row and child limits before their exact scans. One
final profile supplies every actual Head with a common reader fuel.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapRequiredNumeric
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityRequiredCache (Ordinary)
open SourceCurrentRequiredSupport (NodeSupport RowsSupport)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentConstrainedCapRequiredResources (HeapFits readFuel)
open SourceCurrentConstrainedCapRequiredForecast
  (scalar stageProfile stage_ge stage_head_profile stage_constructor_profile planProfile plan_ge
    plan_stage plan_succ rowStep rowStep_ge scan scan_ge scan_count_mono)
namespace Replay
export SourceCurrentRequiredNumericReplay (NodeReady ChildrenReady RowsReady)
end Replay
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

private theorem rows_length {entries : List (Int × Needed)}
    {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireRows entries edges before results after) : results.length ≤ edges.length := by
  induction edges generalizing before results after with
  | nil => cases actual; exact Nat.le_refl _
  | cons edge edges ih =>
      cases actual with
      | rejected _ rest => exact Nat.le_trans (ih rest) (Nat.le_succ _)
      | kept _ _ _ rest => simpa only [List.length_cons] using Nat.add_le_add_right (ih rest) 1

private theorem ordinary_support {unconstrained : Value Symbol Guard → Bool} {anchor before : State Symbol Guard}
    {needed : Needed} {value : Value Symbol Guard} (ordinary : Ordinary value)
    (support : NodeSupport unconstrained anchor needed value) (anchorSemantic : SemanticReady anchor)
    (semantic : SemanticReady before) (available : Available before value) :
    RowsSupport unconstrained anchor needed (InternedEdgeResidency.nodeEdges value) := by
  cases value with
  | empty => intro edge member; cases member
  | node => exact SourceCurrentRequiredSupport.ordinary_rows support anchorSemantic semantic available
  | reference | union | mu => cases ordinary

private theorem ordinary (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (level : Nat) (entries : List (Int × Needed))
    (child : SourceCurrentConstrainedCapRequiredScanResources.ChildBound unconstrained anchor entries level)
    (profile : Profile) {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode (.node entries) value before result after) (ordinary : Ordinary value)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (growth : Grows anchor before) (support : RowsSupport unconstrained anchor (.node entries)
      (InternedEdgeResidency.nodeEdges value)) (fits : HeapFits (stageProfile profile) before) :
    HeapFits (planProfile (level + 1) profile) after ∧
      Replay.NodeReady (readFuel (planProfile (level + 1) profile)) actual := by
  cases actual with
  | identity => exact ⟨fits.mono (plan_stage (level + 1) profile), SourceCurrentRequiredNumericReplay.NodeReady.identity _ _ _⟩
  | empty nonempty => exact ⟨fits.mono (plan_stage (level + 1) profile), SourceCurrentRequiredNumericReplay.NodeReady.empty _ nonempty _⟩
  | @ordinary _ rows _ _ _ _ _ _ _ _ nonempty rowGraph rebuilt =>
      let start := stageProfile profile
      let width := scalar start
      let allRows := scan (rowStep level width) width start
      let ceiling := planProfile (level + 1) profile
      have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
      have length : rows.length ≤ width := SourceCurrentConstrainedCapRequiredResources.node_width fits available
      have widths : ∀ edge ∈ rows, edge.children.length ≤ width :=
        fun edge member => SourceCurrentConstrainedCapRequiredResources.edge_width fits edge (resident edge member)
      have selected := SourceCurrentConstrainedCapRequiredScanResources.rows unconstrained anchor entries level width child
        rowGraph anchorSemantic semantic costs resident growth support widths start (Nat.le_refl _) fits
      have padding : Le (scan (rowStep level width) rows.length start) allRows :=
        scan_count_mono _ (rowStep_ge level width) length start
      have returnedFits : HeapFits allRows _ := selected.1.mono padding
      have effects := SourceCurrentRequiredHeapEffects.rows (fun _ => True) rowGraph semantic costs
        (by intro _ _ _; trivial) resident
      have outputLength : _ ≤ width := Nat.le_trans (rows_length rowGraph) length
      have final := SourceCurrentConstrainedCapRequiredResources.node allRows width _ _ returnedFits
        effects.2.2.2.2 outputLength
      have widthFits : width ≤ scalar allRows := SourceCurrentConstrainedCapEditForecast.scalar_mono
        (scan_ge _ (rowStep_ge level width) width start)
      have bound := final.mono (stage_constructor_profile allRows widthFits)
      have ready := selected.2.mono (SourceCurrentConstrainedCapRequiredResources.readFuel_mono
        (padding.trans (stage_ge allRows)))
      have resultSame := congrArg Prod.fst rebuilt
      have stateSame := congrArg Prod.snd rebuilt
      dsimp only at resultSame stateSame
      subst result
      subst after
      exact ⟨bound, SourceCurrentRequiredNumericReplay.NodeReady.ordinary nonempty rowGraph rfl ready⟩
  | recursive _ recursive _ _ => cases value <;> cases recursive <;> cases ordinary

/-- The initial Needed level and anchored support bound the same actual node graph and every demanded Head. -/
theorem node (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (level : Nat) (needed : Needed)
    (valid : SourceEqualityNeeded.Valid needed)
    (nonnegative : SourceEqualityNeededNonnegative.Nonnegative needed)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (growth : Grows anchor before)
    (support : NodeSupport unconstrained anchor needed value) (profile : Profile)
    (fits : HeapFits profile before) (small : sizeOf needed ≤ level) :
    HeapFits (planProfile level profile) after ∧ Replay.NodeReady (readFuel (planProfile level profile)) actual := by
  cases level with
  | zero => cases needed; simp only [Needed.node.sizeOf_spec] at small; omega
  | succ level =>
      cases needed with
      | node entries =>
          have validEntries : SourceEqualityNeededMap.Ascending entries ∧
              ∀ index child, (index, child) ∈ entries → SourceEqualityNeeded.Valid child := by
            simpa only [SourceEqualityNeeded.Valid] using valid
          have nonnegativeEntries : ∀ index child, (index, child) ∈ entries →
              0 ≤ index ∧ SourceEqualityNeededNonnegative.Nonnegative child := by
            simpa only [SourceEqualityNeededNonnegative.Nonnegative] using nonnegative
          have validEntries : SourceEqualityNeededMap.Ascending entries ∧
      ∀ index child, (index, child) ∈ entries → SourceEqualityNeeded.Valid child := by
    simpa only [SourceEqualityNeeded.Valid] using valid
  have nonnegativeEntries : ∀ index child, (index, child) ∈ entries →
      0 ≤ index ∧ SourceEqualityNeededNonnegative.Nonnegative child := by
    simpa only [SourceEqualityNeededNonnegative.Nonnegative] using nonnegative
  have child : SourceCurrentConstrainedCapRequiredScanResources.ChildBound unconstrained anchor entries level := by
            intro index child member value result before after actual _ semantic costs available growth support profile fits
            have smaller := List.sizeOf_lt_of_mem member
            simp only [Prod.mk.sizeOf_spec] at smaller
            have childSize : sizeOf child ≤ level := by simp only [Needed.node.sizeOf_spec] at small; omega
            exact node unconstrained anchor anchorSemantic level child
              (validEntries.2 index child member) ((nonnegativeEntries index child member).2)
              actual semantic costs available growth support profile fits childSize
          by_cases inputOrdinary : Ordinary value
          · exact ordinary unconstrained anchor anchorSemantic level entries child profile actual inputOrdinary
              semantic costs available growth (ordinary_support inputOrdinary support anchorSemantic semantic available)
              (fits.mono (stage_ge profile))
          · cases actual with
            | identity => exact ⟨fits.mono (plan_ge (level + 1) profile), SourceCurrentRequiredNumericReplay.NodeReady.identity _ _ _⟩
            | empty => exact False.elim (inputOrdinary True.intro)
            | ordinary => exact False.elim (inputOrdinary True.intro)
            | recursive nonempty recursive head body =>
                obtain ⟨path, tip⟩ := SourceCurrentRequiredSupport.tip_exists (.node entries) valid nonnegative
                have nonroot : path ≠ [] := by intro equal; subst path; cases tip; exact nonempty rfl
                have warm := SourceCurrentSecondaryProjectionSupport.support_warm_head
                  (support path tip nonroot) anchorSemantic before growth
                have first := SourceCurrentConstrainedCapRequiredResources.head profile head semantic costs available warm fits
                have effects := SourceEqualityProjectionCosts.head_effects head semantic costs available
                have rows := SourceCurrentRequiredSupport.head_rows support anchorSemantic semantic available growth head
                have result := ordinary unconstrained anchor anchorSemantic level entries child profile body
                  first.2.ordinary effects.2.1 effects.2.2.1 effects.2.2.2
                  (grows_trans growth effects.1.growth) rows (first.1.mono (stage_head_profile profile))
                have headReady := first.2.mono (SourceCurrentConstrainedCapRequiredResources.readFuel_mono
                  ((stage_head_profile profile).trans (plan_stage (level + 1) profile)))
                exact ⟨result.1, SourceCurrentRequiredNumericReplay.NodeReady.recursive nonempty recursive head body headReady result.2⟩
termination_by level

/-- The literal initial trie size provides its own numeric level. -/
theorem at_size (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (needed : Needed)
    (valid : SourceEqualityNeeded.Valid needed)
    (nonnegative : SourceEqualityNeededNonnegative.Nonnegative needed)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (growth : Grows anchor before)
    (support : NodeSupport unconstrained anchor needed value) (profile : Profile) (fits : HeapFits profile before) :
    HeapFits (planProfile (sizeOf needed) profile) after ∧
      Replay.NodeReady (readFuel (planProfile (sizeOf needed) profile)) actual :=
  node unconstrained anchor anchorSemantic (sizeOf needed) needed valid nonnegative actual semantic costs available
    growth support profile fits (Nat.le_refl _)


/-- An original forest scan uses the same finite level at every selected position. -/
theorem children (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (level : Nat) (entries : List (Int × Needed))
    (valid : SourceEqualityNeeded.Valid (.node entries))
    (nonnegative : SourceEqualityNeededNonnegative.Nonnegative (.node entries))
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries 0 values before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (growth : Grows anchor before)
    (support : SourceCurrentRequiredSupport.ForestSupport unconstrained anchor (.node entries) values)
    (profile : Profile) (fits : HeapFits profile before) (small : sizeOf (Needed.node entries) ≤ level) :
    HeapFits (scan (planProfile level) values.length profile) after ∧
      Replay.ChildrenReady (readFuel (scan (planProfile level) values.length profile)) actual := by
  have child : SourceCurrentConstrainedCapRequiredScanResources.ChildBound unconstrained anchor entries level := by
    intro index needed member value result before after actual _ semantic costs available growth support profile fits
    have smaller := List.sizeOf_lt_of_mem member
    simp only [Prod.mk.sizeOf_spec] at smaller
    have childSize : sizeOf needed ≤ level := by simp only [Needed.node.sizeOf_spec] at small; omega
    exact node unconstrained anchor anchorSemantic level needed (validEntries.2 index needed member)
      ((nonnegativeEntries index needed member).2) actual semantic costs available growth support profile fits childSize
  exact SourceCurrentConstrainedCapRequiredScanResources.children unconstrained anchor entries level child actual
    anchorSemantic semantic costs available growth
    (by simpa only [SourceCurrentConstrainedCapRequiredScanResources.ChildrenSupport,
      SourceCurrentRequiredSupport.ForestSupport, Nat.zero_add] using support) profile fits

end MicroCFTA.SourceCurrentConstrainedCapRequiredNumeric
