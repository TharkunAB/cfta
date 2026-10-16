import MicroCFTA.SourceCurrentAllocatedNativeMuSource
import MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning

/-!
# Admission of actual recursive source operands

The fixed source view supplies ordered rows, union members, and stored Mu
bodies. Parent input admission therefore derives admission of each exact
child request. Actual later binder reads retain the original source record.
No child result or conditional result law supplies input membership.
These local facts do not yet establish an execution-wide cache invariant.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeRequestAdmission
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance
open InternedNestedFacts InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceCurrentAllocatedNativeContextCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- A domain change does not change either admitted operand. -/
theorem node_domain (view : View Symbol) (model : InputMeaning view)
    (request : NodeRequest Symbol Guard) (domain : Interned DomainKey)
    (inputs : NodeInputs view model request) : NodeInputs view model ⟨domain, request.left, request.right⟩ := inputs

/-- A source swap retains admission in its literal reversed operand order. -/
theorem node_swap (view : View Symbol) (model : InputMeaning view)
    (request : NodeRequest Symbol Guard) (inputs : NodeInputs view model request) :
    NodeInputs view model ⟨request.domain, request.right, request.left⟩ :=
  ⟨inputs.2.1, inputs.1, inputs.2.2.2, inputs.2.2.1⟩

/-- The actual empty-domain reset retains source scope and input admission. -/
theorem reset (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Term Symbol → Bool) (model : InputMeaning (view source holds))
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (inputs : NodeInputs (view source holds) model request) :
    NodeScope source ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.right⟩ ∧
      NodeInputs (view source holds) model ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.right⟩ :=
  ⟨scope.reset source request.domain request.left request.right, inputs⟩

/-- Literal source union readback admits each member in the fixed input model. -/
theorem union_member (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : InputMeaning (view source holds))
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (available : Available source (.union entry members depth free))
    (valid : model.valid (inputOf (.union entry members depth free)))
    (child : Value Symbol Guard) (member : child ∈ members) : model.valid (inputOf child) := by
  apply model.union_valid entry.identity valid (inputOf child)
  rw [members_readback source facts holds entry members depth free available]
  exact List.mem_map.mpr ⟨child, member, rfl⟩

/-- A left union child retains the exact source operand order and original scope. -/
theorem left_union (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : InputMeaning (view source holds))
    (domain : Interned DomainKey) (entry : Interned NodeKey) (members : List (Value Symbol Guard))
    (depth : Nat) (free : List Reference) (right : Value Symbol Guard)
    (scope : NodeScope source ⟨domain, .union entry members depth free, right⟩)
    (inputs : NodeInputs (view source holds) model ⟨domain, .union entry members depth free, right⟩)
    (child : Value Symbol Guard) (member : child ∈ members) :
    NodeScope source ⟨domain, child, right⟩ ∧ NodeInputs (view source holds) model ⟨domain, child, right⟩ := by
  have childScope := scope.leftUnion source domain entry members depth free right child member
  exact ⟨childScope, childScope.left, inputs.2.1,
    union_member source facts holds model entry members depth free scope.leftAvailable inputs.2.2.1 child member,
    inputs.2.2.2⟩

/-- A right union child retains the exact source operand order and original scope. -/
theorem right_union (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : InputMeaning (view source holds))
    (domain : Interned DomainKey) (left : Value Symbol Guard) (entry : Interned NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (scope : NodeScope source ⟨domain, left, .union entry members depth free⟩)
    (inputs : NodeInputs (view source holds) model ⟨domain, left, .union entry members depth free⟩)
    (child : Value Symbol Guard) (member : child ∈ members) :
    NodeScope source ⟨domain, left, child⟩ ∧ NodeInputs (view source holds) model ⟨domain, left, child⟩ := by
  have childScope := scope.rightUnion source domain left entry members depth free child member
  exact ⟨childScope, inputs.1, childScope.right, inputs.2.2.1,
    union_member source facts holds model entry members depth free scope.rightAvailable inputs.2.2.2 child member⟩

/-- Every literal hash-joined row pair has admitted ordered children in source scope. -/
theorem rows [DecidableEq Symbol]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : InputMeaning (view source holds))
    (domain : Interned DomainKey)
    (first : Interned NodeKey) (left : List (EdgeValue Symbol Guard)) (leftDepth : Nat) (leftFree : List Reference)
    (second : Interned NodeKey) (right : List (EdgeValue Symbol Guard)) (rightDepth : Nat) (rightFree : List Reference)
    (scope : NodeScope source ⟨domain, .node first left leftDepth leftFree, .node second right rightDepth rightFree⟩)
    (inputs : NodeInputs (view source holds) model
      ⟨domain, .node first left leftDepth leftFree, .node second right rightDepth rightFree⟩)
    (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) (member : pair ∈ pairs left right) :
    EdgeScope source ⟨domain, pair.1, pair.2⟩ ∧ EdgeInputs (view source holds) model ⟨domain, pair.1, pair.2⟩ := by
  have inside := (pairs_member left right pair).mp member
  exact ⟨scope.rows source facts domain first left leftDepth leftFree second right rightDepth rightFree
      pair.1 pair.2 inside.1 inside.2.1,
    SourceCurrentAllocatedNativeNodeRowsMeaning.joined_inputs source facts holds model domain
      first left leftDepth leftFree second right rightDepth rightFree scope.leftAvailable scope.rightAvailable inputs pair member⟩

/-- Each actual ordered child zip derives admission before any child result exists. -/
theorem child_inputs (view : View Symbol) (model : InputMeaning view) (request : EdgeRequest Symbol Guard)
    (inputs : EdgeInputs view model request) (pair : Value Symbol Guard × Value Symbol Guard)
    (member : pair ∈ request.left.children.zip request.right.children) :
    NodeInputs view model ⟨request.domain, pair.1, pair.2⟩ := by
  have inside := List.of_mem_zip member
  have left := inputs.1 pair.1 inside.1
  have right := inputs.2 pair.2 inside.2
  exact ⟨left.1, right.1, left.2, right.2⟩

/-- The checked accepted-child list retains both original scope and input membership. -/
theorem child (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : InputMeaning (view source holds))
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request)
    (inputs : EdgeInputs (view source holds) model request) (pair : Value Symbol Guard × Value Symbol Guard)
    (member : pair ∈ request.left.children.zip request.right.children) :
    NodeScope source ⟨request.domain, pair.1, pair.2⟩ ∧
      NodeInputs (view source holds) model ⟨request.domain, pair.1, pair.2⟩ :=
  ⟨scope.child source facts request pair member, child_inputs (view source holds) model request inputs pair member⟩

/-- Literal body readback derives the exact entered child's original model membership. -/
theorem body_inputs (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : InputMeaning (view source holds))
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (inputs : NodeInputs (view source holds) model request) (entered : Interned DomainKey) :
    NodeInputs (view source holds) model ⟨entered, SourceRecursiveIntersectionKernel.body request.left,
      SourceRecursiveIntersectionKernel.body request.right⟩ := by
  have left := body_encoded source facts holds request.left inputs.1 scope.leftAvailable
  have right := body_encoded source facts holds request.right inputs.2.1 scope.rightAvailable
  change inputOf (SourceRecursiveIntersectionKernel.body request.left) =
    SourceCurrentAllocatedNativeMuMeaning.unfolded (view source holds) (inputOf request.left) at left
  change inputOf (SourceRecursiveIntersectionKernel.body request.right) =
    SourceCurrentAllocatedNativeMuMeaning.unfolded (view source holds) (inputOf request.right) at right
  refine ⟨SourceRecursiveIntersectionCode.body_original request.left inputs.1,
    SourceRecursiveIntersectionCode.body_original request.right inputs.2.1, ?_, ?_⟩
  · rw [left]
    exact SourceCurrentAllocatedNativeMuSource.unfolded_valid _ model _ inputs.2.2.1
  · rw [right]
    exact SourceCurrentAllocatedNativeMuSource.unfolded_valid _ model _ inputs.2.2.2

/-- Actual canonical entry supplies the source scope and admission of the body request. -/
theorem entered (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : InputMeaning (view source holds))
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (inputs : NodeInputs (view source holds) model request)
    (cache : Cache.State DomainKey) (valid : Cache.Valid cache) (first second : Nat) :
    let domain := (SourceRecursiveIntersectionEnvironment.enter cache request.domain.key request.left request.right first second).1
    NodeScope source ⟨domain, SourceRecursiveIntersectionKernel.body request.left, SourceRecursiveIntersectionKernel.body request.right⟩ ∧
      NodeInputs (view source holds) model
        ⟨domain, SourceRecursiveIntersectionKernel.body request.left, SourceRecursiveIntersectionKernel.body request.right⟩ := by
  exact ⟨scope.mu source request.domain _ request.left request.right first second
      (SourceRecursiveIntersectionSchedule.entered_key cache valid _ _ _ first second),
    body_inputs source facts holds model request scope inputs _⟩

/-- An actual grown-heap binder read preserves its original record and admitted Mu input. -/
theorem resolved (source current : InternedConstructorTemplates.State Symbol Guard) (facts : Facts current)
    (growth : Grows source current) (history : Extends source.nodes.issued current.nodes.issued)
    (holds : Guard → Term Symbol → Bool) (model : InputMeaning (view source holds))
    (domain : DomainKey) (bindings : OriginalBindings source domain) (name : Nat)
    (member : name ∈ SourceRecursiveIntersectionDomain.names domain)
    (valid : model.valid (.ref name)) (bound : Value Symbol Guard)
    (found : SourcePreparedSharedRows.read current name = some bound) :
    Original bound ∧ Available source bound ∧ model.valid (inputOf bound) := by
  obtain ⟨value, actual, original, available, encoded⟩ :=
    bindings.read source current facts growth history domain name member
  have same : value = bound := Option.some.inj (actual.symm.trans found)
  subst value
  refine ⟨original, available, ?_⟩
  rw [encoded]
  exact model.reference_valid name valid

/-- A reached left-reference callback admits the exact physical record read at that point. -/
theorem left_reference (source current : InternedConstructorTemplates.State Symbol Guard) (facts : Facts current)
    (growth : Grows source current) (history : Extends source.nodes.issued current.nodes.issued)
    (holds : Guard → Term Symbol → Bool) (model : InputMeaning (view source holds))
    (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard)
    (scope : NodeScope source ⟨domain, .reference (.interned name), other⟩)
    (inputs : NodeInputs (view source holds) model ⟨domain, .reference (.interned name), other⟩)
    (member : name ∈ SourceRecursiveIntersectionDomain.names domain.key) (bound : Value Symbol Guard)
    (found : SourcePreparedSharedRows.read current name = some bound) :
    NodeScope source ⟨domain, bound, other⟩ ∧ NodeInputs (view source holds) model ⟨domain, bound, other⟩ := by
  have admitted := resolved source current facts growth history holds model domain.key scope.bindings name member inputs.2.2.1 bound found
  exact ⟨⟨admitted.1, scope.right, admitted.2.1, scope.rightAvailable, scope.bindings⟩,
    admitted.1, inputs.2.1, admitted.2.2, inputs.2.2.2⟩

/-- A reached right-reference callback preserves the parent's literal left-right order. -/
theorem right_reference (source current : InternedConstructorTemplates.State Symbol Guard) (facts : Facts current)
    (growth : Grows source current) (history : Extends source.nodes.issued current.nodes.issued)
    (holds : Guard → Term Symbol → Bool) (model : InputMeaning (view source holds))
    (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard)
    (scope : NodeScope source ⟨domain, other, .reference (.interned name)⟩)
    (inputs : NodeInputs (view source holds) model ⟨domain, other, .reference (.interned name)⟩)
    (member : name ∈ SourceRecursiveIntersectionDomain.names domain.key) (bound : Value Symbol Guard)
    (found : SourcePreparedSharedRows.read current name = some bound) :
    NodeScope source ⟨domain, other, bound⟩ ∧ NodeInputs (view source holds) model ⟨domain, other, bound⟩ := by
  have admitted := resolved source current facts growth history holds model domain.key scope.bindings name member inputs.2.2.2 bound found
  exact ⟨⟨scope.left, admitted.1, scope.leftAvailable, admitted.2.1, scope.bindings⟩,
    inputs.1, admitted.1, inputs.2.2.1, admitted.2.2⟩

end MicroCFTA.SourceCurrentAllocatedNativeRequestAdmission
