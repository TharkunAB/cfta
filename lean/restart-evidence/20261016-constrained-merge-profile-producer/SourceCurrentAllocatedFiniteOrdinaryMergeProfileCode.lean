import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache

/-!
# Local profile certificates for current merge code

Recursive requests retain their complete physical and profile contracts.
Ordered maps relate each returned occurrence to its own input occurrence.
Constructor certificates use literal Work outputs, including cache hits.
These certificates do not supply recursive execution or a body result law.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Effect ValueReady EdgeReady)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- A request retains both physical facts and its universal original-relative profile. -/
def Contract (input : Value Symbol Guard) (before : State Symbol Guard)
    (output : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  SourceCurrentMemoMergeEffects.Contract input before output after ∧
    SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Certificate input output

/-- Local instructions use the stronger contract at each actual recursive request. -/
abbrev Certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (code : Code Symbol Guard Output) (before : State Symbol Guard)
    (post : State Symbol Guard → Output → Prop) : Prop :=
  SourceCurrentMemoMergeEffects.Certified Contract clear code before post

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A stronger recursive result contract retains each previously proved continuation. -/
theorem lift_certified (clear : Guard → Bool) (code : Code Symbol Guard Output)
    (before : State Symbol Guard) (post : State Symbol Guard → Output → Prop)
    (checked : SourceCurrentMemoMergeEffects.Certified SourceCurrentMemoMergeEffects.Contract clear code before post) :
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

/-- Bind checks its continuation at the same actual returned heap. -/
theorem bind_certified (clear : Guard → Bool) (first : Code Symbol Guard First)
    (next : First → Code Symbol Guard Output) (before : State Symbol Guard)
    (intermediate : State Symbol Guard → First → Prop) (post : State Symbol Guard → Output → Prop)
    (checked : Certified clear first before intermediate)
    (later : ∀ value middle, Effect before middle → intermediate middle value → Certified clear (next value) middle post) :
    Certified clear (.bind first next) before post := ⟨intermediate, checked, later⟩

/-- Ordered maps preserve the input/result relation at every literal list position. -/
theorem map_certified (clear : Guard → Bool) (call : Request → Code Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop) (relation : State Symbol Guard → Request → Output → Prop)
    (preGrows : ∀ before after, Effect before after → ∀ request, pre before request → pre after request)
    (relationGrows : ∀ before after, Effect before after → ∀ request value,
      relation before request value → relation after request value)
    (requests : List Request)
    (checked : ∀ request ∈ requests, ∀ before, SemanticReady before → CostHeap before → pre before request →
      Certified clear (call request) before (fun after value => relation after request value))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : ∀ request ∈ requests, pre before request) :
    Certified clear (map call requests) before (fun after values => Language.All₂ (relation after) requests values) := by
  induction requests generalizing before with
  | nil => exact Language.All₂.nil
  | cons first rest ih =>
      apply bind_certified clear _ _ before (fun after value => relation after first value) _
        (checked first List.mem_cons_self before semantic costs (inputs first List.mem_cons_self))
      intro value middle effect valid
      apply bind_certified clear _ _ middle (fun after values => Language.All₂ (relation after) rest values) _
        (ih (fun request member => checked request (List.mem_cons_of_mem _ member)) middle effect.semantic effect.costs
          (fun request member => preGrows before middle effect request (inputs request (List.mem_cons_of_mem _ member))))
      intro values after later ready
      exact Language.All₂.cons (relationGrows middle after later first value valid) ready

/-- An available request passes its complete returned contract to the local continuation. -/
theorem request_certified (clear : Guard → Bool) (input : Value Symbol Guard) (before : State Symbol Guard)
    (available : Available before input) :
    Certified clear (.request input) before (fun after output => Contract input before output after) :=
  ⟨available, fun _ _ _ returned => returned⟩

/-- Actual edge work retains closed resident children, their profile, and their maximum height. -/
theorem edge_certified (clear : Guard → Bool) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (rows arity bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ arity) (heightBound : childrenHeight values ≤ bound) :
    Certified clear (.work (makeEdge symbol guard values)) before
      (fun after edge => EdgeReady after edge ∧ EdgeShape rows arity edge ∧ edgeHeight edge ≤ bound) := by
  have facts := semantic.ready.semantic.1.normal.facts
  have closed : MergedColdReaderClosedInputs.ClosedValues values := fun value member =>
    SourceCurrentAllocatedFiniteOrdinaryFinite.closed before facts.coherent value (available value member)
      (NodeShape.domain value (ChildrenShape.member values profile value member))
  have checked := SourceCurrentMemoMergeEffects.edge_certified clear symbol guard values before semantic costs available closed
  refine ⟨checked.1, checked.2, ?_, ?_⟩
  · exact SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeEdge symbol guard values before
      facts.coherent facts.cached available profile lengthBound
  · have same := InternedShallowValues.makeEdge_children symbol guard values before facts.coherent facts.cached available
    have identity : edgeHeight (run (makeEdge symbol guard values) before).1 =
        childrenHeight (run (makeEdge symbol guard values) before).1.children := by
      cases (run (makeEdge symbol guard values) before).1
      rfl
    rw [identity, same]
    exact heightBound

/-- Actual node work derives closed availability, bounded rows, and the supplied layer ceiling. -/
theorem node_certified (clear : Guard → Bool) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (rows arity bound : Nat) (profile : RowsShape rows arity edges)
    (lengthBound : edges.length ≤ rows) (heightBound : ∀ edge ∈ edges, edgeHeight edge + 1 ≤ bound) :
    Certified clear (.work (makeNode edges)) before
      (fun after value => ValueReady after value ∧ NodeShape rows arity value ∧ height value ≤ bound) := by
  have facts := semantic.ready.semantic.1.normal.facts
  have closed : MergedColdReaderClosedInputs.ClosedEdges edges := fun edge member value included =>
    SourceCurrentAllocatedFiniteOrdinaryFinite.closed before facts.coherent value
      (facts.cached.edges edge.entry.key edge (resident edge member) value included)
      (NodeShape.domain value (ChildrenShape.member edge.children
        (EdgeShape.children edge (RowsShape.member edges profile edge member)) value included))
  have checked := SourceCurrentMemoMergeEffects.node_certified clear edges before semantic costs resident closed
  exact ⟨checked.1, checked.2,
    SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeNode edges before facts.coherent facts.linked resident profile lengthBound,
    MergedOrdinaryHeight.makeNode_bound edges before facts.coherent facts.linked resident bound heightBound⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode
