import MicroCFTA.SourceCurrentAllocatedProjectionResources
import MicroCFTA.MergedFreshOrdinaryColdTermination

/-!
# Local resource control for actual recursive collection

Each step matches one successor of the repaired collector. The current
heap and pending work determine one numeric envelope. Actual Mu unfolding
derives its next envelope. No future collector fuel or returned-store law
is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedReaderControl
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedProvenance (Values)
open InternedBinderProtocol (NodeKey)
open MergedColdReaderClosedInputs (ClosedValues)
open MergedColdReaderTermination (weight workWeight workWeight_append weight_positive)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open InternedMuDepthInventory (Bounded)
open SourceCurrentAllocatedRecursiveMassTrace (charge ceiling)
local notation "Stored" => InternedValueMassHeap.Stored
variable {Symbol Guard : Type}

/-- The actual collector state keeps its heap, visited identities, and pending values. -/
structure Config (Symbol Guard : Type) where
  /-- The complete current constructor heap. -/
  heap : State Symbol Guard
  /-- Identities already visited by this collector. -/
  seen : List Nat
  /-- Values still processed in literal source order. -/
  pending : List (Value Symbol Guard)

/-- A successor is one literal collector branch. Empty pending lists have no successor. -/
inductive Step [DecidableEq (EdgeKey Symbol Guard)] : Config Symbol Guard → Config Symbol Guard → Prop where
  /-- Empty values add no rows and leave the remaining work. -/
  | empty : Step ⟨heap, seen, .empty :: rest⟩ ⟨heap, seen, rest⟩
  /-- An ordinary node emits its rows and leaves the remaining work. -/
  | node : Step ⟨heap, seen, .node entry rows depth free :: rest⟩ ⟨heap, seen, rest⟩
  /-- A visited union needs no further traversal. -/
  | union_seen (visited : entry.identity ∈ seen) :
      Step ⟨heap, seen, .union entry members depth free :: rest⟩ ⟨heap, seen, rest⟩
  /-- An unvisited union prepends its actual members. -/
  | union_fresh {heap : State Symbol Guard} {seen : List Nat} {entry : Interned NodeKey}
      {members : List (Value Symbol Guard)} {depth : Nat} {free : List InternedBinderProtocol.Reference}
      {rest : List (Value Symbol Guard)} (unvisited : entry.identity ∉ seen) :
      Step ⟨heap, seen, .union entry members depth free :: rest⟩ ⟨heap, entry.identity :: seen, members ++ rest⟩
  /-- A visited Mu needs no further unfolding. -/
  | mu_seen (visited : entry.identity ∈ seen) :
      Step ⟨heap, seen, .mu entry body depth ordinary :: rest⟩ ⟨heap, seen, rest⟩
  /-- A fresh Mu prepends the result of its actual repaired unfolding. -/
  | mu_fresh {heap after : State Symbol Guard} {seen : List Nat} {entry : Interned NodeKey}
      {body depth ordinary result : Value Symbol Guard} {rest : List (Value Symbol Guard)}
      (unvisited : entry.identity ∉ seen)
      (actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) heap = .done result after) :
      Step ⟨heap, seen, .mu entry body depth ordinary :: rest⟩ ⟨after, entry.identity :: seen, result :: rest⟩

/-- Physical source facts support every actual closed recursive collector branch. -/
structure Good (limit : Nat) (config : Config Symbol Guard) : Prop where
  /-- Actual stored plans retain their semantic readback. -/
  semantic : SemanticHeap config.heap
  /-- Every free reference has its actual source binding. -/
  covered : Covered [] config.heap
  /-- Stored open-body degrees retain their physical readback. -/
  depth : InternedOpenDepthReadback.Heap config.heap
  /-- Every completed Mu lies within the fixed degree vector. -/
  bounded : Bounded config.heap limit
  /-- Each pending value is available in this exact heap. -/
  available : Values config.heap config.pending
  /-- Pending values have no unresolved free references. -/
  closed : ClosedValues config.pending

/-- One current numeric bound covers payloads, both supplies, and pending work. -/
structure Fits (bound : Nat) (config : Config Symbol Guard) : Prop where
  /-- Complete stored payloads fit the same causal bound. -/
  stored : Stored bound config.heap
  /-- The current issued node counter fits the bound. -/
  nodes : config.heap.nodes.next ≤ bound
  /-- The current issued edge counter fits the bound. -/
  edges : config.heap.edges.next ≤ bound
  /-- The literal pending work fits the bound. -/
  work : workWeight config.pending ≤ bound

/-- The existing Mu-degree vector gains a lowest pending-work coordinate. -/
def measure (limit : Nat) (config : Config Symbol Guard) : Fin (limit + 1) → Nat :=
  MergedFreshOrdinaryColdTermination.measure limit config.heap config.seen config.pending

/-- One strict growth step covers actual unfolding and replacement of the pending head. -/
def g (bound : Nat) : Nat := bound + charge bound + ceiling bound + 1

/-- The controlled resource bound strictly increases at every scheduled step. -/
theorem g_strict (bound : Nat) : bound < g bound := by unfold g; omega

/-- Larger initial resources retain the next controlled bound. -/
theorem g_mono {first last : Nat} (enough : first ≤ last) : g first ≤ g last :=
  Nat.add_le_add_right (Nat.add_le_add
    (Nat.add_le_add enough (SourceCurrentAllocatedRecursiveMassMonotone.charge_mono enough))
    (SourceCurrentAllocatedRecursiveMassMonotone.ceiling_mono enough)) 1

mutual
/-- Structural collector weight is bounded by complete payload mass. -/
theorem weight_le_mass (value : Value Symbol Guard) : weight value ≤ InternedValueMass.value value := by
  cases value with
  | union entry members depth free =>
      have small := workWeight_le_mass members
      simp only [weight, InternedValueMass.value]
      omega
  | empty | reference | node | mu =>
      simp only [weight, InternedValueMass.value]
      omega
termination_by sizeOf value

/-- The mass of the literal pending list bounds all structural work. -/
theorem workWeight_le_mass (values : List (Value Symbol Guard)) : workWeight values ≤ InternedValueMass.values values := by
  cases values with
  | nil => simp only [workWeight, InternedValueMass.values, Nat.le_refl]
  | cons first rest =>
      have own := weight_le_mass first
      have tail := workWeight_le_mass rest
      simp only [workWeight, InternedValueMass.values]
      omega
termination_by sizeOf values
end

/-- A larger resource envelope retains the same exact collector state. -/
theorem Fits.mono {first last : Nat} {config : Config Symbol Guard} (known : Fits first config)
    (enough : first ≤ last) : Fits last config :=
  ⟨known.stored.mono enough, Nat.le_trans known.nodes enough, Nat.le_trans known.edges enough,
    Nat.le_trans known.work enough⟩

/-- A literal initial list needs only its length and causal payload bound. -/
def initialBound (bound : Nat) (heap : State Symbol Guard) (pending : List (Value Symbol Guard)) : Nat :=
  max (max heap.nodes.next heap.edges.next) (max bound (pending.length * bound))

/-- Initial physical values establish all controlled numeric bounds. -/
theorem initial_fits (heap : State Symbol Guard) (seen : List Nat) (pending : List (Value Symbol Guard))
    (bound : Nat) (stored : Stored bound heap) (available : Values heap pending) :
    Fits (initialBound bound heap pending) ⟨heap, seen, pending⟩ := by
  have work : workWeight pending ≤ pending.length * bound := by
    induction pending with
    | nil => simp only [workWeight, List.length_nil, Nat.zero_mul, Nat.le_refl]
    | cons value rest ih =>
        have own := Nat.le_trans (weight_le_mass value) (InternedValueMassHeap.available heap stored value (available _ List.mem_cons_self))
        have tail := ih (fun value member => available value (List.mem_cons_of_mem _ member))
        simp only [workWeight, List.length_cons, Nat.succ_mul]
        omega
  refine ⟨stored.mono ?_, ?_, ?_, ?_⟩ <;> dsimp only [initialBound] <;> omega

/-- Every coordinate of the actual degree vector fits the current resource bound. -/
theorem measure_le {limit bound : Nat} {config : Config Symbol Guard} (known : Fits bound config)
    (index : Fin (limit + 1)) : measure limit config index ≤ bound := by
  obtain ⟨index, inside⟩ := index
  cases index with
  | zero => exact known.work
  | succ degree =>
      change InternedMuDepthInventory.count config.heap config.seen degree ≤ bound
      have small := List.countP_le_length (l := List.range config.heap.nodes.next)
        (p := InternedMuDepthInventory.unseenAt config.heap config.seen degree)
      simp only [List.length_range] at small
      exact Nat.le_trans small known.nodes

private theorem pop_good {limit : Nat} {heap : State Symbol Guard} {seen laterSeen : List Nat}
    {value : Value Symbol Guard} {rest : List (Value Symbol Guard)}
    (good : Good limit ⟨heap, seen, value :: rest⟩) : Good limit ⟨heap, laterSeen, rest⟩ :=
  ⟨good.semantic, good.covered, good.depth, good.bounded,
    fun value member => good.available value (List.mem_cons_of_mem _ member),
    fun value member => good.closed value (List.mem_cons_of_mem _ member)⟩

/-- A literal successful step derives all physical premises for its next state. -/
theorem Step.good [DecidableEq (EdgeKey Symbol Guard)] {limit : Nat} {before after : Config Symbol Guard}
    (step : Step before after) (good : Good limit before) : Good limit after := by
  cases step with
  | empty | node | union_seen | mu_seen => exact pop_good good
  | @union_fresh heap seen entry members depth free rest unvisited =>
      have available := good.available _ List.mem_cons_self
      refine ⟨good.semantic, good.covered, good.depth, good.bounded, ?_, ?_⟩
      · intro value member
        rcases List.mem_append.mp member with head | tail
        · exact available.children value head
        · exact good.available value (List.mem_cons_of_mem _ tail)
      · intro value member
        rcases List.mem_append.mp member with head | tail
        · exact MergedColdReaderClosed.union_members_closed heap good.semantic.1.normal.facts entry members depth free available
            (good.closed _ List.mem_cons_self) value head
        · exact good.closed value (List.mem_cons_of_mem _ tail)
  | @mu_fresh heap after seen entry body depth ordinary result rest unvisited actual =>
      have available := good.available _ List.mem_cons_self
      obtain ⟨produced, middle, done, context, cached, covered, output, growth, history⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          heap good.semantic.1 available good.semantic.2 good.covered
      obtain ⟨rfl, rfl⟩ := InternedNestedConstruction.Outcome.done.inj (done.symm.trans actual)
      have afterDepth : InternedOpenDepthReadback.Heap middle := by
        simpa only [done, InternedNestedConstruction.Outcome.state] using
          InternedStoredPlanBinderDepthProgress.unfold_heap (.mu entry body depth ordinary) heap
            good.semantic.1 good.semantic.2 good.depth available
      have lower : InternedStoredPlanBinderDepthProgress.Lower heap (InternedStoredPlanBinderDepth.valueDepth body) middle := by
        simpa only [done, InternedNestedConstruction.Outcome.state, InternedStoredPlanBinderDepth.bodyDepth] using
          InternedStoredPlanBinderDepthProgress.unfold_new_lower (.mu entry body depth ordinary) heap
            good.semantic.1 good.semantic.2 good.depth available (good.closed _ List.mem_cons_self)
      refine ⟨⟨context, cached⟩, covered, afterDepth,
        InternedMuDepthInventory.bounded_after heap middle limit _ good.bounded
          (good.bounded entry.key entry body depth ordinary (available.resident entry rfl)) lower, ?_, ?_⟩
      · intro value member
        rcases List.mem_cons.mp member with rfl | tail
        · exact output
        · exact (good.available value (List.mem_cons_of_mem _ tail)).grows heap middle growth history
      · intro value member
        rcases List.mem_cons.mp member with rfl | tail
        · exact InternedFreshOrdinaryStoredSubstitution.unfold_closed (.mu entry body depth ordinary)
            heap good.semantic.1 available (good.closed _ List.mem_cons_self) _ middle done
        · exact good.closed value (List.mem_cons_of_mem _ tail)

private theorem pop_fits {bound : Nat} {heap : State Symbol Guard} {seen laterSeen : List Nat}
    {value : Value Symbol Guard} {rest : List (Value Symbol Guard)} (fits : Fits bound ⟨heap, seen, value :: rest⟩) :
    Fits bound ⟨heap, laterSeen, rest⟩ := by
  refine ⟨fits.stored, fits.nodes, fits.edges, ?_⟩
  have own := fits.work
  change workWeight rest ≤ bound
  simp only [workWeight] at own
  omega

/-- One exact step controls the next heap and pending work from current resources alone. -/
theorem Step.fits [DecidableEq (EdgeKey Symbol Guard)] {limit bound : Nat} {before after : Config Symbol Guard}
    (step : Step before after) (good : Good limit before) (fits : Fits bound before) : Fits (g bound) after := by
  cases step with
  | empty | node | union_seen | mu_seen => exact (pop_fits fits).mono (Nat.le_of_lt (g_strict bound))
  | @union_fresh heap seen entry members depth free rest unvisited =>
      refine (show Fits bound ⟨heap, entry.identity :: seen, members ++ rest⟩ from ⟨fits.stored, fits.nodes, fits.edges, ?_⟩).mono (Nat.le_of_lt (g_strict bound))
      have own := fits.work
      simp only [workWeight, weight, workWeight_append] at own ⊢
      omega
  | @mu_fresh heap after seen entry body depth ordinary result rest unvisited actual =>
      obtain ⟨stored, nodes, edges, output⟩ := SourceCurrentAllocatedProjectionResources.unfold_bound
        (.mu entry body depth ordinary) heap bound fits.stored (good.available _ List.mem_cons_self)
      simp only [actual, InternedNestedConstruction.Outcome.state] at stored nodes edges
      have resultMass := output result after actual
      have small := weight_le_mass result
      have oldNodes := fits.nodes
      have oldEdges := fits.edges
      have oldWork := fits.work
      simp only [workWeight] at oldWork ⊢
      refine ⟨stored.mono (by unfold g; omega), ?_, ?_, ?_⟩
      all_goals dsimp only [Config.heap, Config.pending] at oldNodes oldEdges oldWork ⊢
      all_goals try simp only [workWeight] at oldWork ⊢
      all_goals unfold g; omega

private theorem pop_decreases {limit : Nat} {heap : State Symbol Guard} {seen : List Nat}
    {value : Value Symbol Guard} {rest : List (Value Symbol Guard)}
    (good : Good limit ⟨heap, seen, value :: rest⟩) :
    HeightOrder.VectorBelow (limit + 1) (measure limit ⟨heap, seen, rest⟩)
      (measure limit ⟨heap, seen, value :: rest⟩) := by
  apply MergedFreshOrdinaryColdTermination.ordinary_step limit heap good.semantic.1.normal.facts.coherent
    seen seen (value :: rest) rest (fun _ member => member)
  have positive := weight_positive value
  simp only [workWeight]
  omega

/-- Each exact step strictly decreases the existing finite Mu-degree vector. -/
theorem Step.decreases [DecidableEq (EdgeKey Symbol Guard)] {limit : Nat} {before after : Config Symbol Guard}
    (step : Step before after) (good : Good limit before) :
    HeightOrder.VectorBelow (limit + 1) (measure limit after) (measure limit before) := by
  cases step with
  | empty | node | union_seen | mu_seen => exact pop_decreases good
  | union_fresh =>
      apply MergedFreshOrdinaryColdTermination.ordinary_step limit _ good.semantic.1.normal.facts.coherent
        _ _ _ _ (fun _ member => List.mem_cons_of_mem _ member)
      simp only [workWeight, weight, workWeight_append]
      omega
  | @mu_fresh heap after seen entry body depth ordinary result rest unvisited actual =>
      have available := good.available _ List.mem_cons_self
      have lower : InternedStoredPlanBinderDepthProgress.Lower heap (InternedStoredPlanBinderDepth.valueDepth body) after := by
        simpa only [actual, InternedNestedConstruction.Outcome.state, InternedStoredPlanBinderDepth.bodyDepth] using
          InternedStoredPlanBinderDepthProgress.unfold_new_lower (.mu entry body depth ordinary) heap
            good.semantic.1 good.semantic.2 good.depth available (good.closed _ List.mem_cons_self)
      have finalGood := (Step.mu_fresh unvisited actual).good good
      exact MergedFreshOrdinaryColdTermination.mu_step limit heap after good.semantic.1.normal.facts.coherent
        finalGood.semantic.1.normal.facts.coherent good.bounded seen entry body depth ordinary
        (available.resident entry rfl) unvisited lower _ _

end MicroCFTA.SourceCurrentAllocatedReaderControl
