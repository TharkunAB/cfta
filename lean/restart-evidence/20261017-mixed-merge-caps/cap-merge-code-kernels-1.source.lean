import MicroCFTA.SourceCurrentConstrainedCapMemoMergeCode

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

namespace MicroCFTA.CapMergeCodeIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeGraph
open SourceCurrentConstrainedCapMemoMergeCode
open SourceCurrentConstrainedCap (Cap)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- Five rows use the literal column branch at the source threshold. -/
theorem five_rows (top : Guard) (edge : EdgeValue Symbol Guard) :
    group top [edge, edge, edge, edge, edge] =
      .bind (large top edge [edge, edge, edge, edge]) (fun result => .pure [result]) := by
  simp [group]

/-- Literal nullary columns derive an actual Top row with no recursive call or returned cap input. -/
theorem five_nullary_actual [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (top : Guard) (topValid : valid top)
    (entry : Interned (EdgeKey Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : InternedEdgeResidency.EdgeResident before (.mk entry [])) :
    let built := run (makeEdge entry.key.symbol top []) before
    SourceCurrentMemoMergeEffects.Effect before built.2 ∧
      EdgePost valid 1 built.2 built.1 ∧
      Run clear top (group top [.mk entry [], .mk entry [], .mk entry [], .mk entry [], .mk entry []])
        before empty [built.1] built.2 empty := by
  have bounded := large_certified valid 1 clear top topValid (.mk entry [])
    [.mk entry [], .mk entry [], .mk entry [], .mk entry []] before semantic costs
    (by intro edge member; simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member; subst edge; exact resident)
    (by intro edge member; simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member; subst edge; intro value absent; cases absent)
    (by intro edge member; simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member; subst edge; intro value absent; cases absent)
  change Certified valid clear (.bind (.pure []) (fun values => .work (makeEdge entry.key.symbol top values)))
    before (EdgePost valid 1) at bounded
  obtain ⟨intermediate, pureChecked, later⟩ := bounded
  have work := later [] before (SourceCurrentMemoMergeEffects.effect_refl before semantic costs) pureChecked
  refine ⟨work.1, work.2, ?_⟩
  rw [five_rows]
  exact .bind (.bind (.pure [] before empty) (.work _ before empty)) (.pure _ _ empty)

/-- A Mu and a nonhereditary ordinary cap take the actual retained boundary union branch. -/
theorem mixed_retained_actual [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool)
    (muEntry nodeEntry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard) (edge : EdgeValue Symbol Guard) (level : Nat)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before [.mu muEntry body depth ordinary, .node nodeEntry [edge] level []])
    (closed : ClosedValues [.mu muEntry body depth ordinary, .node nodeEntry [edge] level []])
    (annotated : SourceEqualityAnnotationLanguage.Annotated valid body)
    (children : edge.children = []) (outside : ¬valid edge.entry.key.constraint) :
    let inputs := [Value.mu muEntry body depth ordinary, .node nodeEntry [edge] level []]
    let built := run (makeUnion inputs) before
    ¬SourceEqualityAnnotationLanguage.Annotated valid (.node nodeEntry [edge] level []) ∧
      SourceCurrentMemoMergeEffects.Effect before built.2 ∧ ValuePost valid 1 built.2 built.1 ∧
      Run clear edge.entry.key.constraint (retainedColumn inputs) before empty built.1 built.2 empty := by
  have cap : Cap valid 1 (.node nodeEntry [edge] level []) := by
    apply Cap.node 0
    intro value member
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, children, List.not_mem_nil] at member
  have checked := retained_certified valid 1 clear [.mu muEntry body depth ordinary, .node nodeEntry [edge] level []]
    before semantic costs available closed (by
      intro value member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .plain 1 (.mu muEntry body depth ordinary annotated)
      · exact cap)
  change Certified valid clear (.work (makeUnion [.mu muEntry body depth ordinary, .node nodeEntry [edge] level []]))
    before (ValuePost valid 1) at checked
  refine ⟨?_, checked.1, checked.2, ?_⟩
  · intro supposed
    exact outside (SourceCurrentHereditaryConstructors.node_edge supposed edge List.mem_cons_self).1
  · exact .work _ before empty

#print axioms five_rows
#check @five_rows
#print axioms five_nullary_actual
#check @five_nullary_actual
#print axioms mixed_retained_actual
#check @mixed_retained_actual
end MicroCFTA.CapMergeCodeIntegration
