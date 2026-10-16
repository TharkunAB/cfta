import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace

/-!
# Local constructor request budgets for current Merge code

Budgets retain an actual ordered Work trace between exact heaps.
Each recursive request uses its own initial heap and original input.
Ordered maps add variable request costs through actual intermediate heaps.
A budget is not an annotation that can grow without recording more Work.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetCode
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Effect ValueReady EdgeReady)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests observe)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open MergedOrdinaryHeight (height)
namespace Numbers
export SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers (nodeBudget edgeBudget)
end Numbers
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual Work trace has at most the two supplied constructor request counts. -/
def Budget (before after : State Symbol Guard) (nodes edges : Nat) : Prop :=
  ∃ requests, Trace before after requests ∧ nodeRequests requests ≤ nodes ∧ edgeRequests requests ≤ edges

/-- An unchanged heap needs no constructor request. -/
theorem Budget.refl (state : State Symbol Guard) : Budget state state 0 0 :=
  ⟨[], .refl state, Nat.le_refl _, Nat.le_refl _⟩

/-- Increasing request limits retains the same actual Work trace. -/
theorem Budget.mono {before after : State Symbol Guard} {nodes edges moreNodes moreEdges : Nat}
    (actual : Budget before after nodes edges) (nodeBound : nodes ≤ moreNodes) (edgeBound : edges ≤ moreEdges) :
    Budget before after moreNodes moreEdges := by
  obtain ⟨requests, trace, nodes, edges⟩ := actual
  exact ⟨requests, trace, Nat.le_trans nodes nodeBound, Nat.le_trans edges edgeBound⟩

/-- Sequential budgets concatenate Work at the exact intermediate heap. -/
theorem Budget.trans {before middle after : State Symbol Guard} {firstNodes firstEdges lastNodes lastEdges : Nat}
    (first : Budget before middle firstNodes firstEdges) (last : Budget middle after lastNodes lastEdges) :
    Budget before after (firstNodes + lastNodes) (firstEdges + lastEdges) := by
  obtain ⟨earlier, firstTrace, firstNodeBound, firstEdgeBound⟩ := first
  obtain ⟨later, lastTrace, lastNodeBound, lastEdgeBound⟩ := last
  refine ⟨earlier ++ later, .trans firstTrace lastTrace, ?_, ?_⟩
  · rw [SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace.nodeRequests_append]
    exact Nat.add_le_add firstNodeBound lastNodeBound
  · rw [SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace.edgeRequests_append]
    exact Nat.add_le_add firstEdgeBound lastEdgeBound

/-- Actual requests bound both constructor supplies without defining counts from differences. -/
theorem Budget.next_le {before after : State Symbol Guard} {nodes edges : Nat}
    (actual : Budget before after nodes edges) :
    after.nodes.next ≤ before.nodes.next + nodes ∧ after.edges.next ≤ before.edges.next + edges := by
  obtain ⟨requests, trace, nodeBound, edgeBound⟩ := actual
  have counted := trace.next_le
  constructor <;> omega

/-- Literal node Work makes at most one node request and no edge request. -/
theorem node_work (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) :
    Budget before (run (makeNode edges) before).2 1 0 := by
  have counts := SourceCurrentAllocatedFiniteOrdinaryReservations.makeNode_requests edges before
  refine ⟨observe (makeNode edges) before, .work before (makeNode edges), ?_, ?_⟩
  · rw [counts.1]
    split <;> omega
  · exact Nat.le_of_eq counts.2

/-- Literal edge Work makes one edge request and no node request. -/
theorem edge_work (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (before : State Symbol Guard) :
    Budget before (run (makeEdge symbol guard values) before).2 0 1 := by
  refine ⟨observe (makeEdge symbol guard values) before, .work before (makeEdge symbol guard values), ?_, ?_⟩ <;>
    simp [SourceCurrentAllocatedFiniteOrdinaryReservations.makeEdge_observe, nodeRequests, edgeRequests]

/-- Every supported original profile bounds the requests between the same exact heaps. -/
def Certificate (input : Value Symbol Guard) (before after : State Symbol Guard) : Prop :=
  ∀ rows arity bound, NodeShape rows arity input → height input ≤ bound →
    Budget before after (Numbers.nodeBudget rows arity bound) (Numbers.edgeBudget rows arity bound)

/-- Recursive requests retain physical facts, output profiles, and actual Work budgets. -/
def Contract (input : Value Symbol Guard) (before : State Symbol Guard)
    (output : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode.Contract input before output after ∧ Certificate input before after

/-- Local instructions use the stronger request contract at their actual returned heaps. -/
abbrev Certified [DecidableEq Symbol] (clear : Guard → Bool) (code : Code Symbol Guard Output)
    (before : State Symbol Guard) (post : State Symbol Guard → Output → Prop) : Prop :=
  SourceCurrentMemoMergeEffects.Certified Contract clear code before post

variable [DecidableEq Symbol]

/-- A stronger recursive budget contract retains each proved profile continuation. -/
theorem lift_certified (clear : Guard → Bool) (code : Code Symbol Guard Output)
    (before : State Symbol Guard) (post : State Symbol Guard → Output → Prop)
    (checked : SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode.Certified clear code before post) :
    Certified clear code before post := by
  induction code generalizing before with
  | pure value => exact checked
  | work job => exact checked
  | select inputs => exact checked
  | request input => exact ⟨checked.1, fun output after effect returned => checked.2 output after effect returned.1⟩
  | bind first next ihFirst ihNext =>
      obtain ⟨intermediate, firstChecked, later⟩ := checked
      exact ⟨intermediate, ihFirst _ _ firstChecked,
        fun value middle effect valid => ihNext value _ _ (later value middle effect valid)⟩

/-- Physical certificates also remain valid under the complete recursive budget contract. -/
theorem lift_physical (clear : Guard → Bool) (code : Code Symbol Guard Output)
    (before : State Symbol Guard) (post : State Symbol Guard → Output → Prop)
    (checked : SourceCurrentMemoMergeEffects.Certified SourceCurrentMemoMergeEffects.Contract clear code before post) :
    Certified clear code before post :=
  lift_certified clear code before post
    (SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode.lift_certified clear code before post checked)

/-- Bind retains the exact intermediate heap used by both local certificates. -/
theorem bind_certified (clear : Guard → Bool) (first : Code Symbol Guard First)
    (next : First → Code Symbol Guard Output) (before : State Symbol Guard)
    (intermediate : State Symbol Guard → First → Prop) (post : State Symbol Guard → Output → Prop)
    (checked : Certified clear first before intermediate)
    (later : ∀ value middle, Effect before middle → intermediate middle value → Certified clear (next value) middle post) :
    Certified clear (.bind first next) before post := ⟨intermediate, checked, later⟩

/-- Ordered maps add each request's own variable costs at its actual initial heap. -/
theorem map_certified (clear : Guard → Bool) (call : Request → Code Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop) (relation : State Symbol Guard → Request → Output → Prop)
    (preGrows : ∀ before after, Effect before after → ∀ request, pre before request → pre after request)
    (relationGrows : ∀ before after, Effect before after → ∀ request value,
      relation before request value → relation after request value)
    (nodeCost edgeCost : Request → Nat) (requests : List Request)
    (checked : ∀ request ∈ requests, ∀ before, SemanticReady before → CostHeap before → pre before request →
      Certified clear (call request) before (fun after value =>
        Budget before after (nodeCost request) (edgeCost request) ∧ relation after request value))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : ∀ request ∈ requests, pre before request) :
    Certified clear (map call requests) before (fun after values =>
      Budget before after (requests.map nodeCost).sum (requests.map edgeCost).sum ∧
        Language.All₂ (relation after) requests values) := by
  induction requests generalizing before with
  | nil => exact ⟨Budget.refl before, Language.All₂.nil⟩
  | cons first rest ih =>
      apply bind_certified clear _ _ before
        (fun middle value => Budget before middle (nodeCost first) (edgeCost first) ∧ relation middle first value) _
        (checked first List.mem_cons_self before semantic costs (inputs first List.mem_cons_self))
      intro value middle effect valid
      apply bind_certified clear _ _ middle
        (fun after values => Budget middle after (rest.map nodeCost).sum (rest.map edgeCost).sum ∧
          Language.All₂ (relation after) rest values) _
        (ih (fun request member => checked request (List.mem_cons_of_mem _ member)) middle effect.semantic effect.costs
          (fun request member => preGrows before middle effect request (inputs request (List.mem_cons_of_mem _ member))))
      intro values after later ready
      exact ⟨by simpa only [List.map_cons, List.sum_cons] using valid.1.trans ready.1,
        Language.All₂.cons (relationGrows middle after later first value valid.2) ready.2⟩

/-- A recursive request passes its complete actual result and budget contract to its continuation. -/
theorem request_certified (clear : Guard → Bool) (input : Value Symbol Guard) (before : State Symbol Guard)
    (available : Available before input) :
    Certified clear (.request input) before (fun after output => Contract input before output after) :=
  ⟨available, fun _ _ _ returned => returned⟩

/-- Edge constructor certificates retain the literal Work budget and physical result. -/
theorem edge_certified (clear : Guard → Bool) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) (closed : MergedColdReaderClosedInputs.ClosedValues values) :
    Certified clear (.work (makeEdge symbol guard values)) before
      (fun after edge => Budget before after 0 1 ∧ EdgeReady after edge) := by
  have checked := SourceCurrentMemoMergeEffects.edge_certified clear symbol guard values before semantic costs available closed
  exact ⟨checked.1, edge_work symbol guard values before, checked.2⟩

/-- Node constructor certificates retain the literal Work budget and physical result. -/
theorem node_certified (clear : Guard → Bool) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (closed : MergedColdReaderClosedInputs.ClosedEdges edges) :
    Certified clear (.work (makeNode edges)) before
      (fun after value => Budget before after 1 0 ∧ ValueReady after value) := by
  have checked := SourceCurrentMemoMergeEffects.node_certified clear edges before semantic costs resident closed
  exact ⟨checked.1, node_work edges before, checked.2⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetCode
