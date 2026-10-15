import MicroCFTA.SourceMergedSelectionCompletion
import MicroCFTA.SourceMergedContracts

/-!
# Stable general merge effects

Stable finite action bounds retain actual final caches and local result
invariants. Ordered composition combines these bounds. It supplies no
whole-comparison or whole-merger completion premise.
-/
namespace MicroCFTA.SourceMergedCompleteEffects
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceMergedComparisonEffects
open MergedSourceComparison (Result)
open MergedColdMerge (Action pure bind work map)

/-- One finite bound gives the identical successful result and full cache at every larger comparison bound. -/
def Complete (action : Nat → Action Symbol Guard Output) (before : State Symbol Guard)
    (post : State Symbol Guard → Output → Prop) : Prop :=
  ∃ bound result after, (∀ fuel, bound ≤ fuel → action fuel before = .done result after) ∧ Effect before after ∧ post after result

/-- Existing closed available records retain their local constructor invariants. -/
def ValueReady (state : State Symbol Guard) (value : Value Symbol Guard) : Prop := Available state value ∧ value.free = []

/-- Existing resident rows retain closed actual child payloads. -/
def EdgeReady (state : State Symbol Guard) (edge : EdgeValue Symbol Guard) : Prop :=
  InternedEdgeResidency.EdgeResident state edge ∧ MergedColdReaderClosedInputs.ClosedValues edge.children

/-- Actual later effects retain a closed available value. -/
theorem value_grows (before after : State Symbol Guard) (effects : Effect before after) (value : Value Symbol Guard)
    (ready : ValueReady before value) : ValueReady after value := ⟨effects.1.available value ready.1, ready.2⟩

/-- Actual later effects retain a resident row and its closed child list. -/
theorem edge_grows (before after : State Symbol Guard) (effects : Effect before after) (edge : EdgeValue Symbol Guard)
    (ready : EdgeReady before edge) : EdgeReady after edge :=
  ⟨InternedEdgeResidency.edge_grows before after effects.1.growth edge ready.1, ready.2⟩

/-- A no-effect result has a stable bound of zero. -/
theorem pure_complete (value : Output) (before : State Symbol Guard) (semantic : SemanticReady before)
    (post : State Symbol Guard → Output → Prop) (checked : post before value) : Complete (fun _ => pure value) before post :=
  ⟨0, value, before, (fun _ _ => rfl), ⟨pure_keeps _ semantic.ready, semantic⟩, checked⟩

/-- Ordered stable actions retain their exact intermediate cache and combine finite bounds. -/
theorem bind_complete (first : Nat → Action Symbol Guard First) (next : Nat → First → Action Symbol Guard Output)
    (before : State Symbol Guard) (pre : State Symbol Guard → First → Prop) (post : State Symbol Guard → Output → Prop)
    (complete : Complete first before pre)
    (continues : ∀ value middle, Effect before middle → pre middle value → Complete (fun fuel => next fuel value) middle post) :
    Complete (fun fuel => bind (first fuel) (next fuel)) before post := by
  obtain ⟨bound, value, middle, done, effects, valid⟩ := complete
  obtain ⟨later, result, after, nextDone, nextEffects, checked⟩ := continues value middle effects valid
  refine ⟨max bound later, result, after, ?_, effects.trans nextEffects, checked⟩
  intro fuel enough
  simp only [MergedColdMerge.bind, done fuel (Nat.le_trans (Nat.le_max_left _ _) enough), Result.bind,
    nextDone fuel (Nat.le_trans (Nat.le_max_right _ _) enough)]

/-- A literal constructor has the same actual result and cache at every proof bound. -/
theorem work_complete [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Output) (before : State Symbol Guard)
    (post : State Symbol Guard → Output → Prop) (effects : Effect before (run computation before).2) (checked : post (run computation before).2 (run computation before).1) :
    Complete (fun _ => work computation) before post := ⟨0, _, _, (fun _ _ => rfl), effects, checked⟩

/-- Literal edge construction returns a resident edge with its original closed child payload. -/
theorem edge_complete [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (ready : ∀ value ∈ values, ValueReady before value) :
    Complete (fun _ => work (makeEdge symbol guard values)) before EdgeReady := by
  have available : InternedNestedProvenance.Values before values := fun value member => (ready value member).1
  have checked := SourceEqualityRequiredCache.edge symbol guard values before semantic.ready available
  apply work_complete _ before EdgeReady ⟨checked.1, SourceEqualityRequiredSemanticCache.edge _ _ _ before semantic available⟩
  refine ⟨checked.2.1, ?_⟩
  rw [checked.2.2]
  exact fun value member => (ready value member).2

/-- Literal node construction returns a closed available value after all actual row effects. -/
theorem node_complete [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (ready : ∀ edge ∈ edges, EdgeReady before edge) :
    Complete (fun _ => work (makeNode edges)) before ValueReady := by
  have resident : InternedNestedProvenance.Edges before edges := fun edge member => (ready edge member).1
  have closed : MergedColdReaderClosedInputs.ClosedEdges edges := fun edge member => (ready edge member).2
  have checked := SourceEqualityRequiredCache.node edges before semantic.ready resident closed
  exact work_complete _ before ValueReady ⟨checked.1, SourceEqualityRequiredSemanticCache.node edges before semantic resident closed⟩
    ⟨checked.2.1, checked.2.2.1⟩

/-- Ordered finite request lists combine all local stable bounds at their actual returned states. -/
theorem map_complete (call : Nat → Request → Action Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop) (post : State Symbol Guard → Output → Prop)
    (preGrows : ∀ before after, Effect before after → ∀ request, pre before request → pre after request)
    (postGrows : ∀ before after, Effect before after → ∀ value, post before value → post after value)
    (requests : List Request)
    (complete : ∀ request ∈ requests, ∀ before, SemanticReady before → pre before request → Complete (fun fuel => call fuel request) before post)
    (before : State Symbol Guard) (semantic : SemanticReady before) (inputs : ∀ request ∈ requests, pre before request) :
    Complete (fun fuel => map (call fuel) requests) before (fun after values => ∀ value ∈ values, post after value) := by
  induction requests generalizing before with
  | nil => exact pure_complete [] before semantic _ (by simp)
  | cons first rest ih =>
      apply bind_complete _ _ before post _ (complete first List.mem_cons_self before semantic (inputs first List.mem_cons_self))
      intro value middle effects valid
      apply bind_complete _ _ middle _ _
        (ih (fun request member => complete request (List.mem_cons_of_mem _ member)) middle effects.2
          (fun request member => preGrows before middle effects request (inputs request (List.mem_cons_of_mem _ member))))
      intro values after later checked
      apply pure_complete (value :: values) after later.2
      intro result member
      rcases List.mem_cons.mp member with rfl | member
      · exact postGrows middle after later _ valid
      · exact checked result member

end MicroCFTA.SourceMergedCompleteEffects
