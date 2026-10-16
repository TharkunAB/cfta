import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode

namespace MicroCFTA.MergeProfileCodeKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeEffects (Effect ValueReady EdgeReady)
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds (envelope)
open MergedOrdinaryHeight (height edgeHeight childrenHeight)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The ordered request certificate retains each input's height and exact multiplicity. -/
theorem ordered_requests (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (rows arity bound : Nat)
    (ready : ∀ input ∈ inputs, ValueReady before input ∧ NodeShape rows arity input ∧ height input ≤ bound) :
    Certified clear (map Code.request inputs) before (fun after values =>
      Language.All₂ (fun input output => ValueReady after output ∧
        NodeShape (envelope rows bound) arity output ∧ height output ≤ height input) inputs values ∧
      values.length = inputs.length) := by
  have ordered := map_certified clear Code.request
    (fun heap input => ValueReady heap input ∧ NodeShape rows arity input ∧ height input ≤ bound)
    (fun heap input output => ValueReady heap output ∧
      NodeShape (envelope rows bound) arity output ∧ height output ≤ height input)
    (fun _ _ effect input valid => ⟨SourceCurrentMemoMergeEffects.value_grows effect input valid.1, valid.2⟩)
    (fun _ _ effect _ output valid => ⟨SourceCurrentMemoMergeEffects.value_grows effect output valid.1, valid.2⟩)
    inputs (fun input _ heap _ _ valid => ?_) before semantic costs ready
  · exact ordered.mono (fun _ _ results => ⟨results, results.length_eq.symm⟩)
  · apply (request_certified clear input heap valid.1.1).mono
    intro after output returned
    have profiled := returned.2 rows arity bound valid.2.1 valid.2.2
    exact ⟨⟨returned.1.1, returned.1.2 valid.1.2⟩, profiled⟩

/-- Literal edge work feeds two copies of its own actual row into node construction. -/
theorem nullary_duplicate_constructor (clear : Guard → Bool) (symbol : Symbol) (guard : Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before) :
    Certified clear (.bind (.work (makeEdge symbol guard []))
      (fun edge => .work (makeNode [edge, edge]))) before
      (fun after value => ValueReady after value ∧ NodeShape 2 0 value ∧ height value ≤ 1) := by
  apply bind_certified clear _ _ before
    (fun after edge => EdgeReady after edge ∧ EdgeShape 2 0 edge ∧ edgeHeight edge ≤ 0) _
    (edge_certified clear symbol guard [] before semantic costs (by intro value member; cases member) 2 0 0 True.intro (by simp) (Nat.le_refl _))
  intro edge middle effect valid
  exact node_certified clear [edge, edge] middle effect.semantic effect.costs
    (by intro other member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> exact valid.1.1)
    2 0 1 ⟨valid.2.1, valid.2.1, True.intro⟩ (by simp)
    (by intro other member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> omega)

/-- The stronger contract also certifies the complete physical body at its exact code. -/
theorem lifted_physical_body (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before input) (closed : input.free = []) :
    Certified clear (body top input) before ValueReady :=
  (lift_certified clear (body top input) before
    (fun after output => SourceCurrentMemoMergeEffects.Contract input before output after)
    (SourceCurrentMemoMergeEffects.body_certified clear top input before semantic costs available)).mono
      (fun _ _ returned => ⟨returned.1, returned.2 closed⟩)

/-- Warm constructor work retains its exact complete output and whole returned heap. -/
theorem warm_node_work (clear : Guard → Bool) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : InternedNestedProvenance.Edges before edges) (rows arity bound : Nat)
    (profile : RowsShape rows arity edges) (lengthBound : edges.length ≤ rows)
    (heightBound : ∀ edge ∈ edges, edgeHeight edge + 1 ≤ bound) :
    let built := run (makeNode edges) before
    run (makeNode edges) built.2 = (built.1, built.2) ∧
      Certified clear (.work (makeNode edges)) built.2
        (fun after value => ValueReady after value ∧ NodeShape rows arity value ∧ height value ≤ bound) := by
  dsimp only
  have checked := node_certified clear edges before semantic costs resident rows arity bound profile lengthBound heightBound
  have afterEffect : Effect before (run (makeNode edges) before).2 := checked.1
  have replayed := replay (makeNode edges) before (run (makeNode edges) before).2
    semantic.ready.semantic.1.normal.facts.coherent.valid (grows_refl _)
  refine ⟨replayed, ?_⟩
  have afterResident : InternedNestedProvenance.Edges (run (makeNode edges) before).2 edges :=
    fun edge member => InternedEdgeResidency.edge_grows before _ afterEffect.keeps.growth edge (resident edge member)
  exact node_certified clear edges _ afterEffect.semantic afterEffect.costs afterResident rows arity bound profile lengthBound heightBound

#print axioms ordered_requests
#check @ordered_requests
#print axioms nullary_duplicate_constructor
#check @nullary_duplicate_constructor
#print axioms lifted_physical_body
#check @lifted_physical_body
#print axioms warm_node_work
#check @warm_node_work
end MicroCFTA.MergeProfileCodeKernels
