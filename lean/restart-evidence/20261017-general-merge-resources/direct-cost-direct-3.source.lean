import MicroCFTA.SourceCurrentMemoMergeRequestBounds
import MicroCFTA.InternedValueMass

/-!
# Direct instruction costs for actual completed merge bodies

Each recursive request costs one direct instruction. Its completed Call
remains in the receipt, but its nested body cost is separate. Bind counts
both actual branches and one sequencing instruction. All heaps, result
tables, and ordered request occurrences remain exact.
-/
namespace MicroCFTA.SourceCurrentMemoMergeDirectCost
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeRequestBounds (Occurrence Reached)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- Literal instructions retain their exact direct request list and instruction count. -/
inductive Counted [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard) :
    {Output : Type} → Code Symbol Guard Output → State Symbol Guard → Memo Symbol Guard →
      Output → State Symbol Guard → Memo Symbol Guard → List (Occurrence Symbol Guard) → Nat → Prop where
  /-- A direct return costs one instruction. -/
  | pure (value : Output) (heap : State Symbol Guard) (memo : Memo Symbol Guard) :
      Counted clear top (.pure value) heap memo value heap memo [] 1
  /-- A complete constructor job costs one direct instruction. -/
  | work (job : Work Symbol Guard Output) (heap : State Symbol Guard) (memo : Memo Symbol Guard) :
      Counted clear top (.work job) heap memo (run job heap).1 (run job heap).2 memo [] 1
  /-- Actual selection retains its own comparison fuel and costs one direct instruction. -/
  | select (fuel : Nat) (done : SourceMergedSelection.select clear fuel inputs before = .done values after) :
      Counted clear top (.select inputs) before memo values after memo [] 1
  /-- A direct request retains its actual Call and leaves its nested cost separate. -/
  | request (actual : Call clear top input before memo output after saved) :
      Counted clear top (.request input) before memo output after saved [⟨input, before, memo, output, after, saved⟩] 1
  /-- Sequencing adds both actual direct costs and one bind instruction. -/
  | bind (first : Counted clear top code before memo value middle current earlier firstCost)
      (later : Counted clear top (next value) middle current output after saved following laterCost) :
      Counted clear top (.bind code next) before memo output after saved (earlier ++ following) (firstCost + laterCost + 1)

section CountedFacts
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A counted body retains the complete earlier direct-request receipt. -/
theorem Counted.erase {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    {events : List (Occurrence Symbol Guard)} {cost : Nat}
    (actual : Counted clear top code before memo output after saved events cost) :
    SourceCurrentMemoMergeRequestBounds.Direct clear top code before memo output after saved events := by
  induction actual with
  | pure => exact .pure _ _ _
  | work => exact .work _ _ _
  | select fuel done => exact .select fuel done
  | request actual => exact .request actual
  | bind _ _ first later => exact .bind first later

/-- Erasure preserves the complete actual graph and every intermediate heap and table. -/
theorem Counted.graph {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    {events : List (Occurrence Symbol Guard)} {cost : Nat}
    (actual : Counted clear top code before memo output after saved events cost) :
    Run clear top code before memo output after saved := actual.erase.graph

/-- Every direct receipt derives its count from the literal executed instructions. -/
theorem of_direct {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    {events : List (Occurrence Symbol Guard)}
    (actual : SourceCurrentMemoMergeRequestBounds.Direct clear top code before memo output after saved events) :
    ∃ cost, Counted clear top code before memo output after saved events cost := by
  induction actual with
  | pure => exact ⟨1, .pure _ _ _⟩
  | work => exact ⟨1, .work _ _ _⟩
  | select fuel done => exact ⟨1, .select fuel done⟩
  | request actual => exact ⟨1, .request actual⟩
  | bind _ _ first later =>
      obtain ⟨_, first⟩ := first
      obtain ⟨_, later⟩ := later
      exact ⟨_, .bind first later⟩

/-- Every actual completed graph has a count without inspecting nested request bodies. -/
theorem of_run {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∃ events cost, Counted clear top code before memo output after saved events cost := by
  obtain ⟨events, receipt⟩ := SourceCurrentMemoMergeRequestBounds.direct_exists actual
  obtain ⟨cost, counted⟩ := of_direct receipt
  exact ⟨events, cost, counted⟩

/-- The number of opaque direct calls is at most the actual instruction count. -/
theorem Counted.requests_le {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    {events : List (Occurrence Symbol Guard)} {cost : Nat}
    (actual : Counted clear top code before memo output after saved events cost) : events.length ≤ cost := by
  induction actual with
  | pure | work | select | request => simp
  | bind _ _ first later => simp only [List.length_append]; omega

private def Projection {Output : Type} (code : Code Symbol Guard Output) (output : Output) (cost : Nat) : Prop :=
  match code with
  | .pure value => output = value ∧ cost = 1
  | .work _ | .select _ | .request _ => cost = 1
  | .bind _ _ => True

private theorem Counted.projection {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    {events : List (Occurrence Symbol Guard)} {cost : Nat}
    (actual : Counted clear top code before memo output after saved events cost) : Projection code output cost := by
  induction actual with
  | pure => exact ⟨rfl, rfl⟩
  | work | select | request => exact rfl
  | bind => trivial

private theorem bind_cases {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard First}
    {next : First → Code Symbol Guard Output} {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    {output : Output} {events : List (Occurrence Symbol Guard)} {cost : Nat}
    (actual : Counted clear top (.bind code next) before memo output after saved events cost) :
    ∃ value middle current earlier following firstCost laterCost,
      Counted clear top code before memo value middle current earlier firstCost ∧
      Counted clear top (next value) middle current output after saved following laterCost ∧
      cost = firstCost + laterCost + 1 := by
  cases actual with
  | bind first later => exact ⟨_, _, _, _, _, _, _, first, later, rfl⟩

/-- Ordered traversal adds every local direct cost and its literal bind and pure instructions. -/
theorem map_cost {Input Output : Type} (clear : Guard → Bool) (top : Guard)
    (call : Input → Code Symbol Guard Output) (inputs : List Input) (localCost : Input → Nat)
    (known : ∀ input ∈ inputs, ∀ before memo output after saved events cost,
      Counted clear top (call input) before memo output after saved events cost → cost ≤ localCost input)
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {outputs : List Output}
    {events : List (Occurrence Symbol Guard)} {cost : Nat}
    (actual : Counted clear top (SourceCurrentMemoMergeGraph.map call inputs) before memo outputs after saved events cost) :
    outputs.length = inputs.length ∧ cost ≤ (inputs.map localCost).sum + 3 * inputs.length + 1 := by
  induction inputs generalizing before memo outputs after saved events cost with
  | nil =>
      have parts := actual.projection
      change outputs = [] ∧ cost = 1 at parts
      obtain ⟨rfl, rfl⟩ := parts
      exact ⟨rfl, by simp⟩
  | cons input rest ih =>
      obtain ⟨value, middle, current, earlier, following, firstCost, laterCost, first, later, total⟩ := bind_cases actual
      obtain ⟨values, final, returned, tailEvents, pureEvents, tailCost, pureCost, tail, pure, laterTotal⟩ := bind_cases later
      have own := known input List.mem_cons_self _ _ _ _ _ _ _ first
      have remaining := ih (fun input member => known input (List.mem_cons_of_mem _ member)) tail
      have parts := pure.projection
      change outputs = value :: values ∧ pureCost = 1 at parts
      obtain ⟨rfl, rfl⟩ := parts
      simp only [List.length_cons, List.map_cons, List.sum_cons] at *
      exact ⟨by omega, by omega⟩

private theorem sum_constant {Input : Type} (inputs : List Input) (cost : Nat) :
    (inputs.map (fun _ => cost)).sum = inputs.length * cost := by
  induction inputs with
  | nil => simp
  | cons first rest ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]; omega

private theorem retained_cost {clear : Guard → Bool} {top : Guard} (inputs : List (Value Symbol Guard))
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Value Symbol Guard}
    {events : List (Occurrence Symbol Guard)} {cost : Nat}
    (actual : Counted clear top (retainedColumn inputs) before memo output after saved events cost) : cost ≤ 3 := by
  unfold retainedColumn at actual
  split at actual
  · have one := actual.projection; simp only [Projection] at one; omega
  · split at actual
    · have one := actual.projection; simp only [Projection] at one; omega
    · obtain ⟨_, _, _, _, _, _, _, work, request, total⟩ := bind_cases actual
      have workCost := work.projection
      have requestCost := request.projection
      simp only [Projection] at workCost requestCost
      omega

private theorem column_cost {clear : Guard → Bool} {top : Guard} (inputs : List (Value Symbol Guard))
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Value Symbol Guard}
    {events : List (Occurrence Symbol Guard)} {cost : Nat}
    (actual : Counted clear top (column inputs) before memo output after saved events cost) : cost ≤ 5 := by
  obtain ⟨values, _, _, _, _, _, _, selected, retained, total⟩ := bind_cases actual
  have small := retained_cost values retained
  have selectedCost := selected.projection
  simp only [Projection] at selectedCost
  omega

private theorem small_cost {clear : Guard → Bool} {top : Guard} (edge : EdgeValue Symbol Guard)
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : EdgeValue Symbol Guard}
    {events : List (Occurrence Symbol Guard)} {cost : Nat}
    (actual : Counted clear top (small edge) before memo output after saved events cost) :
    cost ≤ 4 * edge.children.length + 3 := by
  obtain ⟨values, _, _, _, _, _, _, requested, rebuilt, total⟩ := bind_cases actual
  have collected := map_cost clear top Code.request edge.children (fun _ => 1)
    (by intro input _ before memo output after saved events cost actual; have one := actual.projection; exact Nat.le_of_eq one) requested
  rw [sum_constant] at collected
  have rebuiltCost := rebuilt.projection
  simp only [Projection] at rebuiltCost
  omega

private theorem large_cost {clear : Guard → Bool} {top : Guard} (first : EdgeValue Symbol Guard)
    (rest : List (EdgeValue Symbol Guard)) {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    {output : EdgeValue Symbol Guard} {events : List (Occurrence Symbol Guard)} {cost : Nat}
    (actual : Counted clear top (large top first rest) before memo output after saved events cost) :
    cost ≤ 8 * first.children.length + 3 := by
  obtain ⟨values, _, _, _, _, _, _, requested, rebuilt, total⟩ := bind_cases actual
  have collected := map_cost clear top column _ (fun _ => 5)
    (by intro input _ before memo output after saved events cost actual; exact column_cost input actual) requested
  rw [sum_constant, MergedPhysicalGroupEdges.columns_length] at collected
  have rebuiltCost := rebuilt.projection
  simp only [Projection] at rebuiltCost
  omega

end CountedFacts

/-- One input payload bound determines a conservative direct body instruction count. -/
def bodyBudget (bound : Nat) : Nat := 100 * (bound + 1) ^ 3

private theorem length_values (values : List (Value Symbol Guard)) : values.length ≤ InternedValueMass.values values := by
  have exactMass := InternedValueMass.values_eq_length_sum values
  omega

private theorem length_edges (rows : List (EdgeValue Symbol Guard)) : rows.length ≤ InternedValueMass.edges rows := by
  have exactMass := InternedValueMass.edges_eq_length_sum rows
  omega

private theorem square_ge (bound : Nat) : bound + 1 ≤ (bound + 1) ^ 2 := by
  simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using
    Nat.mul_le_mul_left (bound + 1) (by omega : 1 ≤ bound + 1)

private theorem cube_ge (bound : Nat) : bound + 1 ≤ (bound + 1) ^ 3 := by
  have squared := square_ge bound
  have next := Nat.mul_le_mul_left ((bound + 1) ^ 2) (by omega : 1 ≤ bound + 1)
  simp only [Nat.mul_one] at next
  simpa only [Nat.pow_succ] using Nat.le_trans squared next

private theorem nonempty_groups_length {Input : Type} (groups : List (List Input))
    (known : ∀ group ∈ groups, group ≠ []) : groups.length ≤ groups.flatten.length := by
  induction groups with
  | nil => simp
  | cons first rest ih =>
      have positive := List.length_pos.mpr (known first List.mem_cons_self)
      have tail := ih (fun group member => known group (List.mem_cons_of_mem _ member))
      simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega

section Body
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem group_cost {clear : Guard → Bool} {top : Guard} (rows : List (EdgeValue Symbol Guard))
    (bound : Nat) (rowCount : rows.length ≤ bound) (widths : ∀ row ∈ rows, row.children.length ≤ bound)
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {outputs : List (EdgeValue Symbol Guard)}
    {events : List (Occurrence Symbol Guard)} {cost : Nat}
    (actual : Counted clear top (group top rows) before memo outputs after saved events cost) :
    cost ≤ 10 * (bound + 1) ^ 2 := by
  unfold group at actual
  split at actual
  · have collected := map_cost clear top small rows (fun _ => 4 * bound + 3)
      (by
        intro row member before memo output after saved events cost actual
        have small := small_cost row actual
        have width := widths row member
        omega) actual
    rw [sum_constant] at collected
    have multiplied := Nat.mul_le_mul_right (4 * bound + 3) rowCount
    have leading : bound * (4 * bound + 3) ≤ 7 * (bound + 1) ^ 2 := by
      have upper := Nat.mul_le_mul (by omega : bound ≤ bound + 1) (by omega : 4 * bound + 3 ≤ 7 * (bound + 1))
      simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using upper
    have linear := Nat.mul_le_mul_left 3 (square_ge bound)
    omega
  · cases rows with
    | nil => simp_all
    | cons first rest =>
        obtain ⟨_, _, _, _, _, _, _, large, returned, total⟩ := bind_cases actual
        have requested := large_cost first rest large
        have returnedCost := returned.projection
        simp only [Projection] at returnedCost
        have width := widths first List.mem_cons_self
        have larger := Nat.mul_le_mul_left 10 (square_ge bound)
        omega

/-- Every literal body has a static direct cost from its original complete payload mass. -/
theorem body_cost {clear : Guard → Bool} {top : Guard} (input : Value Symbol Guard) (bound : Nat)
    (mass : InternedValueMass.value input ≤ bound)
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Value Symbol Guard}
    {events : List (Occurrence Symbol Guard)} {cost : Nat}
    (actual : Counted clear top (body top input) before memo output after saved events cost) : cost ≤ bodyBudget bound := by
  have positive := cube_ge bound
  cases input with
  | node entry rows depth free =>
      unfold body at actual
      split at actual
      · have rowCount : rows.length ≤ bound := by
          have rowsMass := length_edges rows
          simp only [InternedValueMass.value] at mass
          omega
        have widths : ∀ row ∈ rows, row.children.length ≤ bound := by
          intro row member
          have rowMass := InternedValueMass.edge_mem_lt row rows member
          rw [InternedValueMass.edge_children] at rowMass
          have children := length_values row.children
          simp only [InternedValueMass.value] at mass
          omega
        have grouping := MergedSourceGrouping.groups_correct rows
        have groupCount : (MergedSourceGrouping.groups rows).length ≤ bound := by
          have included := nonempty_groups_length (MergedSourceGrouping.groups rows) (by
            intro group member
            obtain ⟨first, rest, same, _⟩ := grouping.exact group member
            simp only [same, ne_eq, List.cons_ne_self, not_false_eq_true])
          rw [grouping.partition.length_eq] at included
          omega
        obtain ⟨collected, _, _, _, _, _, _, groups, rebuilt, total⟩ := bind_cases actual
        have mapped := map_cost clear top (SourceCurrentMemoMergeGraph.group top)
          (MergedSourceGrouping.groups rows) (fun _ => 10 * (bound + 1) ^ 2)
          (by
            intro group member before memo output after saved events cost actual
            have groupRows : group.length ≤ bound := by
              obtain ⟨first, rest, same, exactGroup⟩ := grouping.exact group member
              rw [exactGroup]
              exact Nat.le_trans (List.length_filter_le _ _) rowCount
            apply group_cost group bound groupRows _ actual
            intro row included
            exact widths row (grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, included⟩))) groups
        rw [sum_constant] at mapped
        have rebuiltCost := rebuilt.projection
        simp only [Projection] at rebuiltCost
        have leading : (MergedSourceGrouping.groups rows).length * (10 * (bound + 1) ^ 2) ≤ 10 * (bound + 1) ^ 3 := by
          have upper := Nat.mul_le_mul_right (10 * (bound + 1) ^ 2) (by omega : (MergedSourceGrouping.groups rows).length ≤ bound + 1)
          simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using upper
        have linear := Nat.mul_le_mul_left 3 positive
        unfold bodyBudget
        omega
      · have returned := actual.projection
        simp only [Projection] at returned
        unfold bodyBudget
        omega
  | empty | reference | mu | union =>
      have returned := actual.projection
      simp only [body, Projection] at returned
      unfold bodyBudget
      omega

/-- An actual body derives its direct count and every strictly smaller captured request. -/
theorem body_bound {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Run clear top (body top input) before memo output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : PhysicalStored before memo)
    (available : Available before input) (bound : Nat) (mass : InternedValueMass.value input ≤ bound) :
    ∃ events cost, Counted clear top (body top input) before memo output after saved events cost ∧
      cost ≤ bodyBudget bound ∧ ∀ event ∈ events, Reached (MergedOrdinaryHeight.height input) before event := by
  obtain ⟨events, cost, counted⟩ := of_run actual
  have checked := counted.erase.bounded (MergedOrdinaryHeight.height input) _ semantic costs stored
    (SourceCurrentMemoMergeRequestBounds.body_bounded clear top input before semantic costs available)
  exact ⟨events, cost, counted, body_cost input bound mass counted, checked.2.2.2⟩

end Body
end MicroCFTA.SourceCurrentMemoMergeDirectCost
