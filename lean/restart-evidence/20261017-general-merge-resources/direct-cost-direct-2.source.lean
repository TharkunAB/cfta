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

end MicroCFTA.SourceCurrentMemoMergeDirectCost
