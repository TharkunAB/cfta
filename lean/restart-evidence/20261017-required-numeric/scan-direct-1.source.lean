import MicroCFTA.SourceCurrentConstrainedCapRequiredResources
import MicroCFTA.SourceCurrentRequiredNumericReplay
import MicroCFTA.SourceCurrentRequiredSupport

/-!
# Numeric scans through actual selected Required graphs

The caller proves the numeric law for strict child requirements. These
helpers compose that law through original ordered child and row lists.
Rejected rows perform no work. Kept rows rebuild their literal raw guard.
Each return carries exact replay at the final profile's reader ceiling.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapRequiredScanResources
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredGraph SourceEqualityRequiredCache
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentConstrainedCapRequiredResources (HeapFits readFuel readFuel_mono)
open SourceCurrentConstrainedCapRequiredForecast
  (scalar planProfile rowStep plan_ge plan_mono rowStep_ge rowStep_mono stage_ge stage_constructor_profile
   scan scan_ge scan_mono scan_count_mono)
open SourceCurrentRequiredSupport (NodeSupport RowsSupport)
open SourceCurrentRequiredNumericReplay (NodeReady ChildrenReady RowsReady)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- The main induction supplies numeric execution only for stored child requirements. -/
def ChildBound (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (entries : List (Int × Needed)) (level : Nat) : Prop :=
  ∀ index needed, (index, needed) ∈ entries →
    ∀ {value result : Value Symbol Guard} {before after : State Symbol Guard}
      (actual : RequireNode needed value before result after),
      SemanticReady anchor → SemanticReady before → CostHeap before → Available before value →
      Grows anchor before → NodeSupport unconstrained anchor needed value →
      ∀ profile, HeapFits profile before →
        HeapFits (planProfile level profile) after ∧ NodeReady (readFuel (planProfile level profile)) actual

/-- Original child support follows its exact offset within an ordered suffix. -/
def ChildrenSupport (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (entries : List (Int × Needed)) (offset : Nat) (values : List (Value Symbol Guard)) : Prop :=
  ∀ index needed, SourceEqualityNeededMap.lookup (Int.ofNat (offset + index)) entries = some needed →
    ∀ value, values[index]? = some value → NodeSupport unconstrained anchor needed value

/-- Original child count controls the complete ordered resource scan and read replay. -/
theorem children (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (entries : List (Int × Needed)) (level : Nat) (child : ChildBound unconstrained anchor entries level)
    {index : Nat} {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireChildren entries index values before results after)
    (anchorSemantic : SemanticReady anchor) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (growth : Grows anchor before)
    (support : ChildrenSupport unconstrained anchor entries index values)
    (profile : Profile) (fits : HeapFits profile before) :
    HeapFits (scan (planProfile level) values.length profile) after ∧
      ChildrenReady (readFuel (scan (planProfile level) values.length profile)) actual := by
  induction values generalizing index results before after profile with
  | nil =>
      cases actual
      exact ⟨fits, ChildrenReady.nil _ _ _ _⟩
  | cons value values ih =>
      have tailSupport : ChildrenSupport unconstrained anchor entries (index + 1) values := by
        intro position needed found selected present
        exact support (position + 1) needed
          (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found)
          selected (by simpa only [List.getElem?_cons_succ] using present)
      cases actual with
      | unselected index absent rest =>
          have remaining := ih rest semantic costs
            (fun input member => available input (List.mem_cons_of_mem _ member)) growth tailSupport
            (planProfile level profile) (fits.mono (plan_ge level profile))
          exact ⟨remaining.1, ChildrenReady.unselected absent rest remaining.2⟩
      | selected index found first rest =>
          have firstSupport := support 0 _ (by simpa only [Nat.add_zero] using found) value (by rfl)
          have firstBound := child _ _ (SourceEqualityNeededMap.lookup_mem _ _ _ found) first
            anchorSemantic semantic costs (available value List.mem_cons_self) growth firstSupport profile fits
          have effects := SourceCurrentRequiredHeapEffects.node (fun _ => True) first semantic costs
            (by intro _ _ _; trivial) (available value List.mem_cons_self)
          have remaining := ih rest effects.2.1 effects.2.2.1
            (fun input member => effects.1.available input (available input (List.mem_cons_of_mem _ member)))
            (grows_trans growth effects.1.growth) tailSupport (planProfile level profile) firstBound.1
          have firstReady := firstBound.2.mono
            (readFuel_mono (scan_ge _ (plan_ge level) values.length (planProfile level profile)))
          exact ⟨remaining.1, ChildrenReady.selected found first rest firstReady remaining.2⟩

/-- Rejection can remove rows, while reconstruction retains one result for every kept row. -/
theorem rows_length {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} (actual : RequireRows entries edges before results after) :
    results.length ≤ edges.length := by
  induction edges generalizing results before after with
  | nil => cases actual; exact Nat.le_refl _
  | cons edge edges ih =>
      cases actual with
      | rejected rejected rest => exact Nat.le_trans (ih rest) (Nat.le_succ _)
      | kept fits child built rest => exact Nat.succ_le_succ (ih rest)

/-- Fixed original arities and row count control exact row resources and all nested reads. -/
theorem rows (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (entries : List (Int × Needed)) (level width : Nat) (child : ChildBound unconstrained anchor entries level)
    {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireRows entries edges before results after)
    (anchorSemantic : SemanticReady anchor) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (growth : Grows anchor before)
    (support : RowsSupport unconstrained anchor (.node entries) edges)
    (widths : ∀ edge ∈ edges, edge.children.length ≤ width)
    (profile : Profile) (widthFits : width ≤ scalar profile) (fits : HeapFits profile before) :
    HeapFits (scan (rowStep level width) edges.length profile) after ∧
      RowsReady (readFuel (scan (rowStep level width) edges.length profile)) actual := by
  induction edges generalizing results before after profile with
  | nil => cases actual; exact ⟨fits, RowsReady.nil _ _ _⟩
  | cons edge edges ih =>
      have tailSupport : RowsSupport unconstrained anchor (.node entries) edges :=
        fun original member => support original (List.mem_cons_of_mem _ member)
      have tailWidths : ∀ original ∈ edges, original.children.length ≤ width :=
        fun original member => widths original (List.mem_cons_of_mem _ member)
      cases actual with
      | rejected rejected rest =>
          have remaining := ih rest semantic costs
            (fun original member => resident original (List.mem_cons_of_mem _ member)) growth tailSupport tailWidths
            (rowStep level width profile)
            (Nat.le_trans widthFits (SourceCurrentConstrainedCapEditForecast.scalar_mono (rowStep_ge _ _ _)))
            (fits.mono (rowStep_ge _ _ _))
          exact ⟨remaining.1, RowsReady.rejected rejected rest remaining.2⟩
      | kept accepted selected built rest =>
          have available : Values before edge.children := semantic.ready.semantic.1.normal.facts.cached.edges
            edge.entry.key edge (resident edge List.mem_cons_self)
          have originalSupport : ChildrenSupport unconstrained anchor entries 0 edge.children := by
            simpa only [ChildrenSupport, SourceCurrentRequiredSupport.ForestSupport, Nat.zero_add] using
              support edge List.mem_cons_self
          have first := children unconstrained anchor entries level child selected anchorSemantic semantic costs
            available growth originalSupport profile fits
          have effects := SourceCurrentRequiredHeapEffects.children (fun _ => True) selected semantic costs
            (by intro _ _ _; trivial) available
          let scanned := scan (planProfile level) width profile
          have scanBelow : Le (scan (planProfile level) edge.children.length profile) scanned :=
            scan_count_mono _ (plan_ge level) (widths edge List.mem_cons_self) profile
          have middleFits : HeapFits scanned _ := first.1.mono scanBelow
          have widthScanned : width ≤ scalar scanned := Nat.le_trans widthFits
            (SourceCurrentConstrainedCapEditForecast.scalar_mono (scan_ge _ (plan_ge level) width profile))
          have edgeBound := SourceCurrentConstrainedCapRequiredResources.edge scanned width
            edge.entry.key.symbol edge.entry.key.constraint _ _ middleFits effects.2.2.2.2
            (by rw [selected.length]; exact widths edge List.mem_cons_self)
          have afterFits : HeapFits (rowStep level width profile) _ := by
            have padded := edgeBound.mono (stage_constructor_profile scanned widthScanned)
            simpa only [rowStep, scanned, built] using padded
          have constructor := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint _ _
            effects.2.1.ready effects.2.2.2.2
          have kept : Keeps _ _ := by simpa only [built] using constructor.1
          have afterSemantic : SemanticReady _ := by
            simpa only [built] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol
              edge.entry.key.constraint _ _ effects.2.1 effects.2.2.2.2
          have afterCosts : CostHeap _ := by
            have unchanged : CostHeap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint _) _).2 := effects.2.2.1
            simpa only [built] using unchanged
          have total := effects.1.trans kept
          have remaining := ih rest afterSemantic afterCosts
            (fun original member => InternedEdgeResidency.edge_grows before _ total.growth original
              (resident original (List.mem_cons_of_mem _ member)))
            (grows_trans growth total.growth) tailSupport tailWidths (rowStep level width profile)
            (Nat.le_trans widthFits (SourceCurrentConstrainedCapEditForecast.scalar_mono (rowStep_ge _ _ _))) afterFits
          have firstBelow : Le (scan (planProfile level) edge.children.length profile)
              (scan (rowStep level width) edges.length (rowStep level width profile)) :=
            scanBelow.trans ((stage_ge scanned).trans (scan_ge _ (rowStep_ge level width) edges.length _))
          exact ⟨remaining.1, RowsReady.kept accepted selected built rest
            (first.2.mono (readFuel_mono firstBelow)) remaining.2⟩

end MicroCFTA.SourceCurrentConstrainedCapRequiredScanResources
