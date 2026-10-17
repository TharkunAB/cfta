import MicroCFTA.SourceCurrentAllocatedPartialConditionalDomain

/-!
# Busy exclusion for plain requests among mixed active owners

Only evaluating owners in the existing plain Region contribute a bound.
Complete physical key agreement identifies the demanded owner's value.
This module does not prove that general constrained calls retain the bound.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialConditionalActive
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialActiveOrder (nodeRank edgeRank)
open SourceCurrentAllocatedPartialConditionalDomain (OwnEmpty)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Region" => SourceEqualityPartialPlainRegion.Region

/-- A traversed plain edge has empty own equalities and only plain child Regions. -/
def PlainEdge (edge : EdgeValue Symbol Guard) : Prop :=
  OwnEmpty edge ∧ SourceEqualityPartialPlainRegion.Children edge.children

/-- Only evaluating plain owners need to exceed the current ordinary rank. -/
structure ActiveAbove (bound : Nat) (state : Caller width) : Prop where
  nodes : ∀ handle owner, state.nodeResults.cells handle = some ⟨owner, .evaluating⟩ →
    Region owner.value → bound < nodeRank owner
  edges : ∀ handle owner, state.edgeResults.cells handle = some ⟨owner, .evaluating⟩ →
    PlainEdge owner.value → bound < edgeRank owner

/-- Empty outer tables admit every filtered bound over arbitrary lower warm state. -/
theorem initial_above (bound : Nat) (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) :
    ActiveAbove bound (initial checked merge fourth) := by
  constructor <;> intros <;> contradiction

/-- The earlier all-owner bound supplies the filtered bound. -/
theorem ActiveAbove.of_unconditional {bound : Nat} {before : Caller width}
    (active : SourceCurrentAllocatedPartialActiveOrder.ActiveAbove bound before) : ActiveAbove bound before :=
  ⟨fun handle owner present _ => active.nodes handle owner (by simp) present,
    fun handle owner present _ => active.edges handle owner (by simp) present⟩

/-- Lower execution retains the exact two outer active tables. -/
theorem ActiveAbove.advance {bound : Nat} {before : Caller width} (active : ActiveAbove bound before)
    (checked : SourceEqualityNativeDemand.State width) (fourth : SourceCurrentEmptinessMemo.Memo)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) :
    ActiveAbove bound (advance before checked fourth merge) := active

variable {width : Nat}

/-- A plain node request cannot demand an unrelated constrained evaluating owner. -/
theorem node_begin_safe (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (request : NodeRequest) (before : Caller width)
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (available : Available before.checked.native.machine.heap request.value)
    (region : Region request.value) (active : ActiveAbove (nodeRank request) before) :
    (∃ value, (beginNode request before).2.1 = .ready value) ∨
      ∃ owner, (beginNode request before).2.1 = .evaluate owner := by
  cases published : before.nodeResults.table request.key with
  | none =>
      exact Or.inr ⟨request, by simp [beginNode, FlatMemoThunk.lookupOrInsert, published, FlatMemoThunk.demand, put]⟩
  | some handle =>
      obtain ⟨⟨owner, phase⟩, present, linked⟩ := sound.valid.nodes.linked request.key handle published
      cases phase with
      | suspended => exact Or.inr ⟨owner, by simp only [beginNode, FlatMemoThunk.lookup_hit _ _ _ _ published,
          FlatMemoThunk.demand, present]⟩
      | returned value => exact Or.inl ⟨value, by simp only [beginNode, FlatMemoThunk.lookup_hit _ _ _ _ published,
          FlatMemoThunk.demand, present]⟩
      | evaluating =>
          have values := SourceEqualityPartialKeyTransport.available_reference_eq _ coherent _ _
            (sound.nodes handle _ present).input available (congrArg Prod.snd linked.2)
          have above := active.nodes handle owner present (values.symm ▸ region)
          have same := SourceCurrentAllocatedPartialActiveOrder.nodeRank_of_key _ coherent owner request
            (sound.nodes handle _ present).input available linked.2
          rw [same] at above
          exact False.elim ((Nat.lt_irrefl _) above)

/-- The separate resident edge family also excludes busy and absent demand below its owners. -/
theorem edge_begin_safe (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (request : EdgeRequest) (before : Caller width)
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (plain : PlainEdge request.value) (active : ActiveAbove (edgeRank request) before) :
    (∃ value, (beginEdge request before).2.1 = .ready value) ∨
      ∃ owner, (beginEdge request before).2.1 = .evaluate owner := by
  cases published : before.edgeResults.table request.key with
  | none =>
      exact Or.inr ⟨request, by simp [beginEdge, FlatMemoThunk.lookupOrInsert, published, FlatMemoThunk.demand, put]⟩
  | some handle =>
      obtain ⟨⟨owner, phase⟩, present, linked⟩ := sound.valid.edges.linked request.key handle published
      cases phase with
      | suspended => exact Or.inr ⟨owner, by simp only [beginEdge, FlatMemoThunk.lookup_hit _ _ _ _ published,
          FlatMemoThunk.demand, present]⟩
      | returned value => exact Or.inl ⟨value, by simp only [beginEdge, FlatMemoThunk.lookup_hit _ _ _ _ published,
          FlatMemoThunk.demand, present]⟩
      | evaluating =>
          have values := InternedEdgeResidency.edge_identity_unique _ coherent _ _
            (sound.edges handle _ present).input resident (congrArg Prod.snd linked.2)
          have above := active.edges handle owner present (values.symm ▸ plain)
          have same := SourceCurrentAllocatedPartialActiveOrder.edgeRank_of_key _ coherent owner request
            (sound.edges handle _ present).input resident linked.2
          rw [same] at above
          exact False.elim ((Nat.lt_irrefl _) above)

end MicroCFTA.SourceCurrentAllocatedPartialConditionalActive
