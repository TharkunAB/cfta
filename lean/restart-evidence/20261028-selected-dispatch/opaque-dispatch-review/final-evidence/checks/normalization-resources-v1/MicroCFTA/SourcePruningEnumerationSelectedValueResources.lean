import MicroCFTA.SourcePruningEnumerationSelectedValueCaller
import MicroCFTA.SourceCurrentProjectionUnionResources
import MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources

/-!
# Original resource bounds for selected native preparation

One Mu branch charges its actual stored unfolding. One Union branch charges
its actual row read and final node. The domain bound stays unchanged.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedValue
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentAllocatedRecursiveMassTrace (charge ceiling)
variable {Symbol Guard : Type}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- One original scalar covers either selected preparation branch. -/
def resourceBound (bound : Nat) : Nat :=
  max (bound + charge bound)
    (max (ceiling bound) (SourceCurrentProjectionUnionResources.headGrowth bound))

private theorem resourceBound_ge (bound : Nat) : bound ≤ resourceBound bound := by
  unfold resourceBound
  omega

/-- An actual successful preparation derives its heap and result bounds. -/
theorem run_resources (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard)
    (bound : Nat) (semantic : SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Available before value) (closed : value.free = [])
    (fits : Fits bound before) (observed : run fuel value before = .done result after) :
    Fits (resourceBound bound) after ∧ InternedValueMass.value result ≤ resourceBound bound := by
  cases value with
  | empty | reference | node =>
      cases observed
      exact ⟨fits.mono (resourceBound_ge bound),
        Nat.le_trans (InternedValueMassHeap.available before fits.stored _ available)
          (resourceBound_ge bound)⟩
  | mu entry body depth ordinary =>
      have numeric := SourceCurrentAllocatedProjectionResources.unfold_bound
        (.mu entry body depth ordinary) before bound fits.stored available
      cases unfolded : InternedFreshOrdinaryStoredSubstitution.unfold
          (.mu entry body depth ordinary) before with
      | pending key middle =>
          simp only [run, unfolded] at observed
          cases observed
      | done produced middle =>
          have same : produced = result ∧ middle = after := by
            simpa only [run, unfolded, MergedSourceComparison.Result.done.injEq] using observed
          rcases same with ⟨rfl, rfl⟩
          have stored : InternedValueMassHeap.Stored (ceiling bound) middle := by
            simpa only [unfolded, InternedNestedConstruction.Outcome.state] using numeric.1
          have nodes : middle.nodes.next ≤ before.nodes.next + charge bound := by
            simpa only [unfolded, InternedNestedConstruction.Outcome.state] using numeric.2.1
          have edges : middle.edges.next ≤ before.edges.next + charge bound := by
            simpa only [unfolded, InternedNestedConstruction.Outcome.state] using numeric.2.2.1
          have mass := numeric.2.2.2 produced middle unfolded
          have originalNodes := fits.nodes
          have originalEdges := fits.edges
          refine ⟨⟨stored.mono ?_, ?_, ?_, Nat.zero_le _⟩, ?_⟩
          all_goals change _ ≤ resourceBound bound
          all_goals unfold resourceBound
          all_goals omega
  | union entry members depth free =>
      cases exposed : MergedFreshOrdinaryExposure.nodeEdges fuel
          (.union entry members depth free) before with
      | unresolved | pending | exhausted =>
          simp only [run, exposed] at observed
          cases observed
      | done rows middle =>
          have same :
              (InternedConstructorTemplates.run (makeNode rows) middle).1 = result ∧
                (InternedConstructorTemplates.run (makeNode rows) middle).2 = after := by
            simpa only [run, exposed, MergedSourceComparison.Result.done.injEq] using observed
          rcases same with ⟨rfl, rfl⟩
          have head : SourceEqualityRequiredHead.Head (.union entry members depth free) before
              (InternedConstructorTemplates.run (makeNode rows) middle).1
              (InternedConstructorTemplates.run (makeNode rows) middle).2 :=
            .read fuel rows middle exposed rfl
          have numeric := SourceCurrentProjectionUnionResources.head head bound semantic costs
            available closed fits
          have mass := InternedValueMassHeap.available _ numeric.2.1.stored _ numeric.2.2.1
          have increase : SourceCurrentProjectionUnionResources.headGrowth bound ≤ resourceBound bound := by
            unfold resourceBound
            omega
          exact ⟨numeric.2.1.mono increase, Nat.le_trans mass increase⟩

end MicroCFTA.SourcePruningEnumerationSelectedValue

namespace MicroCFTA.SourcePruningEnumerationSelectedValueCaller
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Fits" => SourceCurrentConstrainedCapGeneratedQueryResources.Fits
variable {width : Nat}

/-- The original profile pays native preparation without a domain operation. -/
def normalizationProfile (profile : Profile) : Profile :=
  let bound := SourceCurrentMemoMergeResourceControl.initialBound profile.nodes profile.edges profile.mass
  let prepared := SourcePruningEnumerationSelectedValue.resourceBound bound
  ⟨prepared, prepared, profile.domains, prepared⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Original counters and stored mass bound the same actual advanced caller. -/
theorem fits_after (profile : Profile) (before : Caller width) (fuel : Nat)
    (value result : Node) (heap : State Symbol Guard)
    (semantic : SemanticReady before.checked.native.machine.heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap before.checked.native.machine.heap)
    (available : Available before.checked.native.machine.heap value) (closed : value.free = [])
    (fits : Fits profile before.checked)
    (observed : SourcePruningEnumerationSelectedValue.run fuel value
      before.checked.native.machine.heap = .done result heap) :
    Fits (normalizationProfile profile) (advance before heap).checked ∧
      InternedValueMass.value result ≤ (normalizationProfile profile).mass := by
  let bound := SourceCurrentMemoMergeResourceControl.initialBound profile.nodes profile.edges profile.mass
  have massLe : profile.mass ≤ bound := by dsimp [bound, SourceCurrentMemoMergeResourceControl.initialBound]; omega
  have nodeLe : profile.nodes ≤ bound := by dsimp [bound, SourceCurrentMemoMergeResourceControl.initialBound]; omega
  have edgeLe : profile.edges ≤ bound := by dsimp [bound, SourceCurrentMemoMergeResourceControl.initialBound]; omega
  have original : SourceCurrentMemoMergeResourceControl.Fits bound before.checked.native.machine.heap :=
    ⟨fits.stored.mono massLe, Nat.le_trans fits.nodes nodeLe, Nat.le_trans fits.edges edgeLe, Nat.zero_le _⟩
  have numeric := SourcePruningEnumerationSelectedValue.run_resources fuel value
    before.checked.native.machine.heap result heap bound semantic costs available closed original observed
  exact ⟨⟨numeric.1.nodes, numeric.1.edges, fits.domains, numeric.1.stored⟩, numeric.2⟩

/-- One original caller producer retains its full result and derives its forecast. -/
theorem complete_resources (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos) (value : Node)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap value)
    (closed : value.free = []) (fits : Fits profile before.checked) :
    ∃ bound result heap,
      (((∀ extra, SourcePruningEnumerationSelectedValue.run (bound + extra) value
            before.checked.native.machine.heap = .done result heap) ∧
          Keeps before.checked.native.machine.heap heap ∧ SemanticReady heap ∧
          Available heap result ∧ result.free = [] ∧
          ∀ holds ambient term,
            InternedGuardedLanguage.meaning holds ambient result term ↔
              InternedGuardedLanguage.meaning holds ambient value term) ∧
        Post formulas solver inventory before (advance before heap) memos) ∧
      Fits (normalizationProfile profile) (advance before heap).checked ∧
      InternedValueMass.value result ≤ (normalizationProfile profile).mass := by
  obtain ⟨bound, result, heap, packet, post⟩ :=
    complete formulas solver inventory before memos value initial available closed
  have observed : SourcePruningEnumerationSelectedValue.run bound value
      before.checked.native.machine.heap = .done result heap := by
    simpa only [Nat.add_zero] using packet.1 0
  have numeric := fits_after profile before bound value result heap initial.ready.semantic
    initial.ready.costs available closed fits observed
  exact ⟨bound, result, heap, ⟨packet, post⟩, numeric⟩

end MicroCFTA.SourcePruningEnumerationSelectedValueCaller
