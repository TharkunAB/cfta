import MicroCFTA.SourceCurrentConstrainedCapKernelJointEffects
import MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceCompile

/-!
# Joint laws through literal native rows and union calls

Ordered recursive calls produce their own joint return context. Actual
constructor work retains caps, source-ranked occurrences, and pair scope.
The recursive call contracts are induction inputs. They do not assert
completion of the enclosing source execution.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapKernelJointRows
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel
open SourceCurrentConstrainedCap (Cap Edge)
open SourceCurrentConstrainedCapNativeOccurrenceCache (OriginalBindings NodeInputs EdgeInputs edgeBudget)
open SourceCurrentConstrainedCapNonplainRank (pairRank)
open SourceCurrentConstrainedCapPairOccurrences (Classified FreeLE FreeBelow sourceWeight)
open SourceRecursiveIntersectionResultScope (Scope EdgeScope)
open SourceCurrentConstrainedCapKernelJoint (Context)
local notation "JointChecked" => SourceCurrentConstrainedCapKernelJoint.Checked
local notation "JointCalls" => SourceCurrentConstrainedCapKernelJoint.Calls
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
variable (annotation : Guard → Prop) (source : State Symbol Guard)

private theorem edge_work (depth bound : Nat) (domain : Interned DomainKey) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (state : Machine Symbol Guard) (context : Context annotation source state)
    (available : ∀ value ∈ values, Available state.heap value) (guardValid : depth = 0 → annotation guard)
    (bounded : ∀ value ∈ values, Cap annotation (depth - 1) value)
    (free : ∀ value ∈ values, FreeLE (sourceWeight annotation source) bound value)
    (scopes : ∀ value ∈ values, Scope domain.key.seen value) :
    JointChecked annotation source (work (makeEdge symbol guard values) state)
      (fun after edge => EdgeResident after.heap edge ∧ Edge annotation depth edge ∧
        (∀ child ∈ edge.children, FreeLE (sourceWeight annotation source) bound child) ∧ EdgeScope domain.key.seen edge) := by
  intro edge after done
  obtain ⟨rfl, rfl⟩ := work_done _ state edge after done
  refine ⟨context.edge symbol guard values available,
    (InternedNestedFacts.edge_verified symbol guard values state.heap context.valid.1 available).result _ _ rfl,
    SourceCurrentConstrainedCap.makeEdge annotation depth symbol guard values state.heap
      context.valid.1.coherent context.valid.1.cached available guardValid bounded, ?_, ?_⟩
  · rw [InternedShallowValues.makeEdge_children symbol guard values state.heap context.valid.1.coherent context.valid.1.cached available]
    exact free
  · exact SourceRecursiveIntersectionResultScope.edge domain.key.seen symbol guard values state.heap context.valid.1 available scopes

private theorem node_work (depth bound : Nat) (domain : Interned DomainKey) (edges : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (context : Context annotation source state)
    (resident : ∀ edge ∈ edges, EdgeResident state.heap edge) (bounded : ∀ edge ∈ edges, Edge annotation depth edge)
    (free : ∀ edge ∈ edges, ∀ value ∈ edge.children,
      FreeLE (sourceWeight annotation source) bound value ∧ FreeBelow (sourceWeight annotation source) bound value)
    (scopes : ∀ edge ∈ edges, EdgeScope domain.key.seen edge) :
    JointChecked annotation source (work (makeNode edges) state)
      (fun after value => Available after.heap value ∧ Cap annotation depth value ∧
        Classified (sourceWeight annotation source) bound value ∧ Scope domain.key.seen value) := by
  intro value after done
  obtain ⟨rfl, rfl⟩ := work_done _ state value after done
  exact ⟨context.node edges resident,
    (InternedNestedFacts.node_verified edges state.heap context.valid.1 resident).result _ _ rfl,
    SourceCurrentConstrainedCap.makeNode annotation depth edges state.heap context.valid.1.coherent context.valid.1.linked resident bounded,
    SourceCurrentConstrainedCapPairOccurrences.makeNode _ bound edges state.heap context.valid.1 resident free,
    SourceRecursiveIntersectionResultScope.node domain.key.seen edges state.heap context.valid.1 resident scopes⟩

private theorem union_work (depth bound : Nat) (domain : Interned DomainKey) (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) (context : Context annotation source state)
    (available : ∀ value ∈ values, Available state.heap value) (bounded : ∀ value ∈ values, Cap annotation depth value)
    (classified : ∀ value ∈ values, Classified (sourceWeight annotation source) bound value)
    (scopes : ∀ value ∈ values, Scope domain.key.seen value) :
    JointChecked annotation source (work (makeUnion values) state)
      (fun after value => Available after.heap value ∧ Cap annotation depth value ∧
        Classified (sourceWeight annotation source) bound value ∧ Scope domain.key.seen value) := by
  intro value after done
  obtain ⟨rfl, rfl⟩ := work_done _ state value after done
  exact ⟨context.union values available,
    (InternedNestedFacts.union_verified values state.heap context.valid.1 available).result _ _ rfl,
    SourceCurrentConstrainedCap.makeUnion annotation depth values state.heap context.valid.1 available bounded,
    SourceCurrentConstrainedCapPairOccurrences.makeUnion _ bound values state.heap context.semantic.1.normal available classified,
    SourceRecursiveIntersectionResultScope.union domain.key.seen values state.heap context.semantic.1.normal available scopes⟩

variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
  (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
  (physical : SourceRecursiveIntersectionKernel.Calls call) (joint : JointCalls annotation source call)
  (emptyValid : annotation emptyGuard)
  (conjoinValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second))

include physical joint emptyValid conjoinValid

/-- Actual edge execution retains both local laws and scope at its literal zip budget. -/
theorem edge_joint (depth : Nat) (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard)
    (state : Machine Symbol Guard) (context : Context annotation source state) (known : Domain state domain)
    (bindings : OriginalBindings annotation source domain.key) (inputs : EdgeInputs source ⟨domain, left, right⟩)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (leftCap : Edge annotation depth left) (rightCap : Edge annotation depth right) :
    JointChecked annotation source (edge emptyGuard conjoin (call domain) left right state)
      (fun after result => EdgeResident after.heap result ∧ Edge annotation depth result ∧
        (∀ value ∈ result.children, FreeLE (sourceWeight annotation source) (edgeBudget annotation ⟨domain, left, right⟩) value) ∧
        EdgeScope domain.key.seen result) := by
  unfold edge
  split
  · let input := fun (current : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
      Domain current domain ∧ Available current.heap pair.1 ∧ Available current.heap pair.2 ∧
        Cap annotation (depth - 1) pair.1 ∧ Cap annotation (depth - 1) pair.2 ∧ NodeInputs source ⟨domain, pair.1, pair.2⟩
    let output := fun (after : Machine Symbol Guard) (value : Value Symbol Guard) =>
      Available after.heap value ∧ Cap annotation (depth - 1) value ∧
        FreeLE (sourceWeight annotation source) (edgeBudget annotation ⟨domain, left, right⟩) value ∧ Scope domain.key.seen value
    have walked := SourceCurrentConstrainedCapKernelJoint.walk annotation source (fun pair => call domain pair.1 pair.2)
      (left.children.zip right.children) input output
      (by intro before after growth pair known; exact ⟨known.1.grows _ growth, growth.available _ known.2.1,
        growth.available _ known.2.2.1, known.2.2.2⟩)
      (by intro before after growth value result; exact ⟨growth.available _ result.1, result.2⟩)
      (by
        intro pair _ current valid currentInputs
        have checked := physical domain pair.1 pair.2 current valid currentInputs.1 currentInputs.2.1 currentInputs.2.2.1
        exact ⟨checked.valid, checked.extension, by intro _ _ _; trivial⟩)
      (by
        intro pair member current currentContext currentInputs
        apply SourceCurrentConstrainedCapKernelJoint.map annotation source _ _ _
          (joint (depth - 1) domain pair.1 pair.2 current currentContext currentInputs.1 bindings
            currentInputs.2.2.2.2.2 currentInputs.2.2.2.1 currentInputs.2.2.2.2.1)
        intro value after _ result
        exact ⟨result.1, result.2.1, fun name named => Nat.le_trans (result.2.2.1.free name named)
          (SourceCurrentConstrainedCapNativeOccurrenceCache.childBudget_member annotation _ pair member), result.2.2.2⟩)
      state context (by
        intro pair member
        have inside := List.of_mem_zip member
        have first := inputs.1 pair.1 inside.1
        have second := inputs.2 pair.2 inside.2
        have capped : Cap annotation (depth - 1) pair.1 ∧ Cap annotation (depth - 1) pair.2 := by
          cases depth with
          | zero => exact ⟨.plain 0 (leftCap.2 pair.1 inside.1), .plain 0 (rightCap.2 pair.2 inside.2)⟩
          | succ depth => exact ⟨leftCap pair.1 inside.1, rightCap pair.2 inside.2⟩
        exact ⟨known, context.valid.1.cached.edges _ _ leftResident pair.1 inside.1,
          context.valid.1.cached.edges _ _ rightResident pair.2 inside.2, capped.1, capped.2,
          first.1, second.1, first.2.1, second.2.1, first.2.2, second.2.2⟩)
    apply SourceCurrentConstrainedCapKernelJoint.bind annotation source _ _ _ _ walked
    intro values after _ afterContext results
    apply edge_work annotation source depth (edgeBudget annotation ⟨domain, left, right⟩) domain left.entry.key.symbol
      (conjoin left.entry.key.constraint right.entry.key.constraint) values after afterContext
      (fun value member => (results value member).1) ?_
      (fun value member => (results value member).2.1) (fun value member => (results value member).2.2.1)
      (fun value member => (results value member).2.2.2)
    intro zero
    subst depth
    exact conjoinValid _ _ leftCap.1 rightCap.1
  · apply edge_work annotation source depth (edgeBudget annotation ⟨domain, left, right⟩) domain left.entry.key.symbol
      emptyGuard [.empty] state context
    · intro value member; cases List.mem_singleton.mp member; exact empty_available _
    · intro _; exact emptyValid
    · intro value member; cases List.mem_singleton.mp member; exact .plain _ .empty
    · intro value member; cases List.mem_singleton.mp member; exact fun _ impossible => by cases impossible
    · intro value member; cases List.mem_singleton.mp member; exact SourceRecursiveIntersectionResultScope.closed _ _ rfl

/-- Literal row order retains strict child bounds at every positive enclosing rank. -/
theorem rows_joint [DecidableEq Symbol] (depth : Nat) (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (facts : Facts source) (state : Machine Symbol Guard) (context : Context annotation source state)
    (known : Domain state domain) (bindings : OriginalBindings annotation source domain.key)
    (inputs : NodeInputs source ⟨domain, left, right⟩) (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right) :
    JointChecked annotation source
      (walk (fun pair => edge emptyGuard conjoin (call domain) pair.1 pair.2) (pairs (nodeEdges left) (nodeEdges right)) state)
      (fun after edges => ∀ edge ∈ edges, EdgeResident after.heap edge ∧ Edge annotation depth edge ∧
        (∀ value ∈ edge.children, FreeLE (sourceWeight annotation source) (pairRank annotation left right) value ∧
          FreeBelow (sourceWeight annotation source) (pairRank annotation left right) value) ∧ EdgeScope domain.key.seen edge) := by
  let input := fun (current : Machine Symbol Guard) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Domain current domain ∧ EdgeResident current.heap pair.1 ∧ EdgeResident current.heap pair.2 ∧
      Edge annotation depth pair.1 ∧ Edge annotation depth pair.2 ∧ EdgeInputs source ⟨domain, pair.1, pair.2⟩
  let output := fun (after : Machine Symbol Guard) (edge : EdgeValue Symbol Guard) =>
    EdgeResident after.heap edge ∧ Edge annotation depth edge ∧
      (∀ value ∈ edge.children, FreeLE (sourceWeight annotation source) (pairRank annotation left right) value ∧
        FreeBelow (sourceWeight annotation source) (pairRank annotation left right) value) ∧ EdgeScope domain.key.seen edge
  apply SourceCurrentConstrainedCapKernelJoint.walk annotation source _ _ input output
  · intro before after growth pair known
    exact ⟨known.1.grows _ growth, edge_grows _ _ growth.heap _ known.2.1,
      edge_grows _ _ growth.heap _ known.2.2.1, known.2.2.2⟩
  · intro before after growth edge result
    exact ⟨edge_grows _ _ growth.heap _ result.1, result.2⟩
  · intro pair _ current valid currentInputs
    have checked := edge_checked emptyGuard conjoin call physical domain pair.1 pair.2 current valid
      currentInputs.1 currentInputs.2.1 currentInputs.2.2.1
    exact ⟨checked.valid, checked.extension, by intro _ _ _; trivial⟩
  · intro pair member current currentContext currentInputs
    have inside := (pairs_member _ _ pair).mp member
    have bounds := SourceCurrentConstrainedCapNativeOccurrenceCompile.row_budget annotation domain left right pair.1 pair.2 inside.1 inside.2.1
    apply SourceCurrentConstrainedCapKernelJoint.map annotation source _ _ _
      (edge_joint annotation source emptyGuard conjoin call physical joint emptyValid conjoinValid depth domain pair.1 pair.2
        current currentContext currentInputs.1 bindings currentInputs.2.2.2.2.2 currentInputs.2.1 currentInputs.2.2.1
        currentInputs.2.2.2.1 currentInputs.2.2.2.2.1)
    intro edge after _ result
    refine ⟨result.1, result.2.1, ?_, result.2.2.2⟩
    intro value included
    have free := result.2.2.1 value included
    refine ⟨fun name named => Nat.le_trans (free name named) bounds.1, ?_⟩
    intro name named
    rcases bounds.2 with smaller | zero
    · exact .inl (Nat.lt_of_le_of_lt (free name named) smaller)
    · exact .inr zero
  · exact context
  · intro pair member
    have inside := (pairs_member _ _ pair).mp member
    have original := SourceCurrentConstrainedCapOriginalSupport.rows_input source facts domain left right inputs pair.1 pair.2 inside.1 inside.2.1
    exact ⟨known, resident_edges state.heap context.valid.1.linked left
        (inputs.2.2.1.grows source state.heap context.growth context.history).resident pair.1 inside.1,
      resident_edges state.heap context.valid.1.linked right
        (inputs.2.2.2.1.grows source state.heap context.growth context.history).resident pair.2 inside.2.1,
      SourceCurrentConstrainedCap.node_edge leftCap pair.1 inside.1,
      SourceCurrentConstrainedCap.node_edge rightCap pair.2 inside.2.1, original⟩

/-- Actual ordered rows and node normalization derive all four local result laws. -/
theorem node_joint [DecidableEq Symbol] (depth : Nat) (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (facts : Facts source) (state : Machine Symbol Guard) (context : Context annotation source state)
    (known : Domain state domain) (bindings : OriginalBindings annotation source domain.key)
    (inputs : NodeInputs source ⟨domain, left, right⟩) (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right) :
    JointChecked annotation source (node emptyGuard conjoin (call domain) (nodeEdges left) (nodeEdges right) state)
      (fun after value => Available after.heap value ∧ Cap annotation depth value ∧
        Classified (sourceWeight annotation source) (pairRank annotation left right) value ∧ Scope domain.key.seen value) := by
  unfold node
  apply SourceCurrentConstrainedCapKernelJoint.bind annotation source _ _ _ _
    (rows_joint annotation source emptyGuard conjoin call physical joint emptyValid conjoinValid depth domain left right facts state context known bindings inputs leftCap rightCap)
  intro edges after _ afterContext results
  exact node_work annotation source depth (pairRank annotation left right) domain edges after afterContext
    (fun edge member => (results edge member).1) (fun edge member => (results edge member).2.1)
    (fun edge member => (results edge member).2.2.1) (fun edge member => (results edge member).2.2.2)

end MicroCFTA.SourceCurrentConstrainedCapKernelJointRows
