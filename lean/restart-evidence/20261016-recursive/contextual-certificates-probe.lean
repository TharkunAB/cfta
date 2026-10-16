import MicroCFTA.SourceCurrentAllocatedNativeContextualCertificates
open MicroCFTA Language BinderLanguage Cache InternedBinderProtocol
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativeContextCache SourceCurrentAllocatedNativeContextualCode
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
#print axioms SourceCurrentAllocatedNativeContextualCertificates.node_walk_certified
#print axioms SourceCurrentAllocatedNativeContextualCertificates.edge_walk_certified
#print axioms SourceCurrentAllocatedNativeContextualCertificates.compileRows_certified
#print axioms SourceCurrentAllocatedNativeContextualCertificates.left_union_certified
#print axioms SourceCurrentAllocatedNativeContextualCertificates.right_union_certified
#print axioms SourceCurrentAllocatedNativeContextualCertificates.children_certified
#print axioms SourceCurrentAllocatedNativeContextualCertificates.sentinel_certified
#print axioms SourceCurrentAllocatedNativeContextualCertificates.empty_certified
#print axioms SourceCurrentAllocatedNativeContextualCertificates.reset_certified
#print axioms SourceCurrentAllocatedNativeContextualCertificates.swap_certified
#print axioms SourceCurrentAllocatedNativeContextualCertificates.repeated_certified
#print axioms SourceCurrentAllocatedNativeContextualCertificates.self_certified
#print axioms SourceCurrentAllocatedNativeContextualCertificates.children_source_certified
#print axioms SourceCurrentAllocatedNativeContextualCertificates.mismatch_certified
#print axioms SourceCurrentAllocatedNativeContextualCertificates.rejected_certified
#print axioms SourceCurrentAllocatedNativeContextualCertificates.prefix_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.node_walk_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.edge_walk_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.compileRows_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.left_union_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.right_union_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.children_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.sentinel_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.empty_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.reset_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.swap_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.repeated_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.self_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.children_source_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.mismatch_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.rejected_certified
#check @SourceCurrentAllocatedNativeContextualCertificates.prefix_certified

noncomputable section
local instance : DecidableEq Symbol := Classical.typeDecidableEq _
local instance : DecidableEq (EdgeKey Symbol Guard) := Classical.typeDecidableEq _
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private def emptyRequest : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, .empty, .empty⟩
private def raw (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard)) : EdgeValue Symbol Guard :=
  .mk ⟨0, ⟨symbol, children.map Value.referenceOf, guard⟩⟩ children

variable (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
  (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
  (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
  (semantic : SourceEqualityRequiredSemanticCache.SemanticReady state.heap)

-- Empty and duplicate request lists retain their literal ordered occurrences.
example : Certified view model ranked holds
    (SourceRecursiveIntersectionCode.walk (fun (_ : Nat) => .node emptyRequest .pure) []) state
    (fun after values => InternedNestedProvenance.Values after.heap values ∧
      All₂ (fun (_ : Nat) value => NodeLaw view model ranked holds emptyRequest value) [] values) :=
  SourceCurrentAllocatedNativeContextualCertificates.node_walk_certified view model ranked holds
    (fun (_ : Nat) => emptyRequest) [] state valid semantic

example : Certified view model ranked holds
    (SourceRecursiveIntersectionCode.walk (fun (_ : Nat) => .node emptyRequest .pure) [7, 7]) state
    (fun after values => InternedNestedProvenance.Values after.heap values ∧
      All₂ (fun (_ : Nat) value => NodeLaw view model ranked holds emptyRequest value) [7, 7] values) :=
  SourceCurrentAllocatedNativeContextualCertificates.node_walk_certified view model ranked holds
    (fun (_ : Nat) => emptyRequest) [7, 7] state valid semantic

example : Certified view model ranked holds (.pure (.empty : Value Symbol Guard)) state
    (fun _ result => NodeLaw view model ranked holds emptyRequest result) :=
  SourceCurrentAllocatedNativeContextualCertificates.empty_certified view model ranked holds emptyRequest (.inl rfl) state

example : Certified view model ranked holds
    (requestNode IntersectionEmptyDomain.emptyDomain emptyRequest.left emptyRequest.right) state
    (fun _ result => NodeLaw view model ranked holds emptyRequest result) :=
  SourceCurrentAllocatedNativeContextualCertificates.reset_certified view model ranked holds emptyRequest state

example : Certified view model ranked holds
    (requestNode emptyRequest.domain emptyRequest.right emptyRequest.left) state
    (fun _ result => NodeLaw view model ranked holds emptyRequest result) :=
  SourceCurrentAllocatedNativeContextualCertificates.swap_certified view model ranked holds emptyRequest state

-- A literal arity mismatch needs no child result or recursive semantic premise.
example (symbol : Symbol) :
    let request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,
      raw symbol SourceEqualityConstraintConstructors.top [], raw symbol SourceEqualityConstraintConstructors.top [.empty]⟩
    Certified view model ranked holds (SourceEqualityNativeCheckedCode.sentinel request.left) state
      (fun _ result => EdgeLaw view model ranked holds request result) := by
  exact SourceCurrentAllocatedNativeContextualCertificates.mismatch_certified view model ranked holds _
    (by change 0 ≠ 1; decide) state valid

-- Contradictory raw fields derive source rejection and the sentinel certificate.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (symbol : Symbol) :
    let impossible : Guard := ⟨none, .top⟩
    let request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, raw symbol impossible [], raw symbol impossible []⟩
    Certified view model ranked (SourceEqualityPCSGuard.holds formulas solver)
      (SourceEqualityNativeCheckedCode.sentinel request.left) state
      (fun _ result => EdgeLaw view model ranked (SourceEqualityPCSGuard.holds formulas solver) request result) := by
  have cached : SourceEqualityGuardReadback.Cached (none : Option EqualityNormalize.Constraints) := by
    intro classes equal
    cases equal
  exact SourceCurrentAllocatedNativeContextualCertificates.rejected_certified view model ranked formulas solver _
    cached cached rfl state valid

-- The repeated walk is a nested source request, in the same order, before the final pure list.
example : SourceRecursiveIntersectionCode.walk (fun (_ : Nat) => .node emptyRequest .pure) [7, 7] =
    .node emptyRequest (fun first => .node emptyRequest (fun second => .pure [first, second])) := rfl

-- An actual yielded prefix supplies the certificate without a future semantic plan.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (before : SourceEqualityNativeDemand.State 8)
    (code : Code Symbol Guard (EdgeValue Symbol Guard)) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (currentSemantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (ready : EdgeReady before.native.machine request)
    (matching : request.left.entry.key.symbol = request.right.entry.key.symbol)
    (one : SourceEqualityNativeDemand.step (.edgeBody request .pure) before =
      .yielded (.code code) {before with operations := operations}) :
    Certified view model ranked (SourceEqualityPCSGuard.holds formulas solver) code before.native.machine
      (fun _ result => EdgeLaw view model ranked (SourceEqualityPCSGuard.holds formulas solver) request result) :=
  SourceCurrentAllocatedNativeContextualCertificates.prefix_certified view model ranked formulas solver request
    before code operations good currentSemantic ready matching one
