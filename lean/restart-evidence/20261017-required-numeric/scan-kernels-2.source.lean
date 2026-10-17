import MicroCFTA.SourceCurrentConstrainedCapRequiredScanResources

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace MicroCFTA.RequiredScanIntegration
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredGraph SourceEqualityRequiredCache
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapRequiredResources (HeapFits readFuel)
open SourceCurrentConstrainedCapRequiredForecast (planProfile rowStep plan_ge scan scalar)
open SourceCurrentConstrainedCapRequiredScanResources (ChildBound ChildrenSupport)
open SourceCurrentRequiredNumericReplay (NodeReady)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

private theorem identity_child (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (key : Int) (level : Nat) : ChildBound unconstrained anchor [(key, .node [])] level := by
  intro index needed member value result before after actual anchorSemantic semantic costs available growth support profile fits
  have same := List.mem_singleton.mp member
  cases same
  cases actual with
  | identity => exact ⟨fits.mono (plan_ge level profile), NodeReady.identity _ _ _⟩
  | empty nonempty => exact False.elim (nonempty rfl)
  | ordinary nonempty => exact False.elim (nonempty rfl)
  | recursive nonempty => exact False.elim (nonempty rfl)

/-- A selected original child and a rejected row construct their own exact numeric scan. -/
theorem constructed_rows (unconstrained : Value Symbol Guard → Bool)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (profile : Profile) (fits : HeapFits profile before) (width : 1 ≤ scalar profile)
    (kept rejected : EdgeValue Symbol Guard) (value : Value Symbol Guard)
    (keptChildren : kept.children = [value]) (rejectedChildren : rejected.children = [])
    (resident : Edges before [kept, rejected]) :
    let made := run (makeEdge kept.entry.key.symbol kept.entry.key.constraint kept.children) before
    ∃ actual : RequireRows [(0, Needed.node [])] [kept, rejected] before [made.1] made.2,
      HeapFits (scan (rowStep 0 1) 2 profile) made.2 ∧
      SourceCurrentRequiredNumericReplay.RowsReady (readFuel (scan (rowStep 0 1) 2 profile)) actual ∧
      ∀ worker reader, 2 * sizeOf (Needed.node [(0, Needed.node [])]) - 1 ≤ worker →
        readFuel (scan (rowStep 0 1) 2 profile) ≤ reader →
        SourceEqualityRequiredWorker.rows (SourceEqualityRequiredWorker.require worker reader)
          [(0, Needed.node [])] [kept, rejected] before = .done [made.1] made.2 := by
  let entries : List (Int × Needed) := [(0, .node [])]
  have children : RequireChildren entries 0 kept.children before kept.children before := by
    rw [keptChildren]
    exact .selected 0 rfl .identity (.nil (index := 1))
  let made := run (makeEdge kept.entry.key.symbol kept.entry.key.constraint kept.children) before
  have actual : RequireRows entries [kept, rejected] before [made.1] made.2 :=
    .kept (by rw [keptChildren]; rfl) children rfl
      (.rejected (by rw [rejectedChildren]; rfl) .nil)
  have support : SourceCurrentRequiredSupport.RowsSupport unconstrained before (.node entries) [kept, rejected] := by
    intro edge member index needed found selected present
    have only : needed = .node [] := congrArg Prod.snd
      (List.mem_singleton.mp (SourceEqualityNeededMap.lookup_mem _ _ _ found))
    subst needed
    exact SourceCurrentRequiredSupport.empty_support unconstrained before selected
  have widths : ∀ edge ∈ [kept, rejected], edge.children.length ≤ 1 := by
    intro edge member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [keptChildren, List.length_singleton, Nat.le_refl]
    · have same := List.mem_singleton.mp member
      subst edge
      simp only [rejectedChildren, List.length_nil, Nat.zero_le]
  have checked := SourceCurrentConstrainedCapRequiredScanResources.rows unconstrained before entries 0 1
    (identity_child unconstrained before 0 0) actual semantic semantic costs resident (grows_refl _) support widths profile width fits
  exact ⟨actual, checked.1, checked.2, checked.2⟩

/-- Offset lookup retains an open unselected sibling before an identity-selected child. -/
theorem offset_children (unconstrained : Value Symbol Guard → Bool) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (profile : Profile) (fits : HeapFits profile before)
    (openValue value : Value Symbol Guard) (available : Values before [openValue, value]) :
    ∃ actual : RequireChildren [(2, Needed.node [])] 1 [openValue, value] before [openValue, value] before,
      HeapFits (scan (planProfile 0) 2 profile) before ∧
      SourceCurrentRequiredNumericReplay.ChildrenReady (readFuel (scan (planProfile 0) 2 profile)) actual := by
  have actual : RequireChildren [(2, Needed.node [])] 1 [openValue, value] before [openValue, value] before :=
    .unselected 1 rfl (.selected 2 rfl .identity (.nil (index := 3)))
  have support : ChildrenSupport unconstrained before [(2, Needed.node [])] 1 [openValue, value] := by
    intro index needed found selected present
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have same : needed = .node [] := congrArg Prod.snd (List.mem_singleton.mp member)
    subst needed
    exact SourceCurrentRequiredSupport.empty_support unconstrained before selected
  have checked := SourceCurrentConstrainedCapRequiredScanResources.children unconstrained before [(2, Needed.node [])] 0
    (identity_child unconstrained before 2 0) actual semantic semantic costs available (grows_refl _) support profile fits
  exact ⟨actual, checked⟩

end MicroCFTA.RequiredScanIntegration
#print axioms MicroCFTA.RequiredScanIntegration.constructed_rows
#check @MicroCFTA.RequiredScanIntegration.constructed_rows
#print axioms MicroCFTA.RequiredScanIntegration.offset_children
#check @MicroCFTA.RequiredScanIntegration.offset_children
