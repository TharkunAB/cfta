import MicroCFTA.SourceCurrentAllocatedNativeScopedCertificates
open MicroCFTA Language Cache InternedBinderProtocol
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativeScopedCode
open SourceRecursiveIntersectionResultScope (Scope EdgeScope)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
#print axioms SourceCurrentAllocatedNativeScopedCertificates.node_walk_certified
#print axioms SourceCurrentAllocatedNativeScopedCertificates.edge_walk_certified
#print axioms SourceCurrentAllocatedNativeScopedCertificates.compileRows_certified
#print axioms SourceCurrentAllocatedNativeScopedCertificates.left_union_certified
#print axioms SourceCurrentAllocatedNativeScopedCertificates.right_union_certified
#print axioms SourceCurrentAllocatedNativeScopedCertificates.children_certified
#print axioms SourceCurrentAllocatedNativeScopedCertificates.sentinel_certified
#print axioms SourceCurrentAllocatedNativeScopedCertificates.empty_certified
#print axioms SourceCurrentAllocatedNativeScopedCertificates.reset_certified
#print axioms SourceCurrentAllocatedNativeScopedCertificates.swap_certified
#print axioms SourceCurrentAllocatedNativeScopedCertificates.self_certified
#print axioms SourceCurrentAllocatedNativeScopedCertificates.repeated_certified
#print axioms SourceCurrentAllocatedNativeScopedCertificates.prefix_certified
#check @SourceCurrentAllocatedNativeScopedCertificates.node_walk_certified
#check @SourceCurrentAllocatedNativeScopedCertificates.edge_walk_certified
#check @SourceCurrentAllocatedNativeScopedCertificates.compileRows_certified
#check @SourceCurrentAllocatedNativeScopedCertificates.left_union_certified
#check @SourceCurrentAllocatedNativeScopedCertificates.right_union_certified
#check @SourceCurrentAllocatedNativeScopedCertificates.children_certified
#check @SourceCurrentAllocatedNativeScopedCertificates.sentinel_certified
#check @SourceCurrentAllocatedNativeScopedCertificates.empty_certified
#check @SourceCurrentAllocatedNativeScopedCertificates.reset_certified
#check @SourceCurrentAllocatedNativeScopedCertificates.swap_certified
#check @SourceCurrentAllocatedNativeScopedCertificates.self_certified
#check @SourceCurrentAllocatedNativeScopedCertificates.repeated_certified
#check @SourceCurrentAllocatedNativeScopedCertificates.prefix_certified

noncomputable section
local instance : DecidableEq Symbol := Classical.typeDecidableEq _
local instance : DecidableEq (EdgeKey Symbol Guard) := Classical.typeDecidableEq _

private def emptyRequest : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, .empty, .empty⟩
private def repeatedDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey := ⟨0, ⟨[], [(0, 1)]⟩⟩
private def repeatedRequest : NodeRequest Symbol Guard :=
  ⟨repeatedDomain, .reference (.interned 0), .reference (.interned 1)⟩
private def raw (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard)) : EdgeValue Symbol Guard :=
  .mk ⟨0, ⟨symbol, children.map Value.referenceOf, guard⟩⟩ children
variable (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
  (semantic : SourceEqualityRequiredSemanticCache.SemanticReady state.heap)

example : Scope [] (.empty : Value Symbol Guard) := SourceRecursiveIntersectionResultScope.closed _ _ rfl
example : Certified (.pure (.empty : Value Symbol Guard)) state (fun _ result => Scope [] result) :=
  SourceCurrentAllocatedNativeScopedCertificates.empty_certified IntersectionEmptyDomain.emptyDomain state

example : SourceRecursiveIntersectionControl.decision repeatedDomain.key repeatedRequest.left repeatedRequest.right = .repeated (0, 1) := by cbv
example : Certified (.pure (.reference (.intersection 0 1) : Value Symbol Guard)) state
    (fun _ result => Scope repeatedDomain.key.seen result) := by
  exact SourceCurrentAllocatedNativeScopedCertificates.repeated_certified repeatedRequest (0, 1) state (by cbv)
example : ¬ Scope [] (.reference (.intersection 0 1) : Value Symbol Guard) := by
  intro scope
  obtain ⟨pair, impossible, _⟩ := scope (.intersection 0 1) (by simp [Value.free])
  cases impossible

example : Certified (requestNode IntersectionEmptyDomain.emptyDomain emptyRequest.left emptyRequest.right) state
    (fun _ result => Scope emptyRequest.domain.key.seen result) :=
  SourceCurrentAllocatedNativeScopedCertificates.reset_certified emptyRequest state
example : Certified (requestNode emptyRequest.domain emptyRequest.right emptyRequest.left) state
    (fun _ result => Scope emptyRequest.domain.key.seen result) :=
  SourceCurrentAllocatedNativeScopedCertificates.swap_certified emptyRequest state

example : Certified (SourceRecursiveIntersectionCode.walk (fun (_ : Nat) => requestNode repeatedDomain (.empty : Value Symbol Guard) .empty) [4, 4]) state
    (fun after values => InternedNestedProvenance.Values after.heap values ∧ ∀ value ∈ values, Scope repeatedDomain.key.seen value) :=
  SourceCurrentAllocatedNativeScopedCertificates.node_walk_certified repeatedDomain (fun (_ : Nat) => (.empty, .empty)) [4, 4] state valid semantic

-- Scope does not require matching symbols in the independent row requests.
example (first second : Symbol) :
    Certified (SourceRecursiveIntersectionCode.walk (fun (_ : Unit) => requestEdge repeatedDomain
      (raw first SourceEqualityConstraintConstructors.top []) (raw second SourceEqualityConstraintConstructors.top [])) [()]) state
      (fun after values => InternedNestedProvenance.Edges after.heap values ∧ ∀ value ∈ values, EdgeScope repeatedDomain.key.seen value) :=
  SourceCurrentAllocatedNativeScopedCertificates.edge_walk_certified repeatedDomain
    (fun (_ : Unit) => (raw first SourceEqualityConstraintConstructors.top [], raw second SourceEqualityConstraintConstructors.top [])) [()] state valid semantic

example : Certified (compileRows repeatedDomain [] []) state (fun _ result => Scope repeatedDomain.key.seen result) :=
  SourceCurrentAllocatedNativeScopedCertificates.compileRows_certified repeatedDomain [] [] state valid semantic

example (symbol : Symbol) :
    Certified (SourceEqualityNativeCheckedCode.sentinel (raw symbol SourceEqualityConstraintConstructors.top [])) state
      (fun _ result => EdgeScope repeatedDomain.key.seen result) :=
  SourceCurrentAllocatedNativeScopedCertificates.sentinel_certified
    ⟨repeatedDomain, raw symbol SourceEqualityConstraintConstructors.top [], raw symbol SourceEqualityConstraintConstructors.top []⟩ state valid

-- An actual early mismatch prefix requires no original-field lookup or future scope.
example (before : SourceEqualityNativeDemand.State 8) (symbol : Symbol)
    (currentValid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (currentSemantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap) :
    let impossible : Guard := ⟨none, .top⟩
    let request : EdgeRequest Symbol Guard := ⟨repeatedDomain, raw symbol impossible [], raw symbol impossible [.empty]⟩
    Certified (SourceEqualityNativeCheckedCode.sentinel request.left) before.native.machine
      (fun _ result => EdgeScope request.domain.key.seen result) := by
  apply SourceCurrentAllocatedNativeScopedCertificates.prefix_certified _ before _
    (SourceEqualityMkEdgeAllocation.emptyField before.operations) currentValid currentSemantic
  rfl

example : SourceRecursiveIntersectionCode.walk (fun (_ : Nat) => requestNode repeatedDomain (.empty : Value Symbol Guard) .empty) [4, 4] =
    .node ⟨repeatedDomain, .empty, .empty⟩ (fun first => .node ⟨repeatedDomain, .empty, .empty⟩ (fun second => .pure [first, second])) := rfl
