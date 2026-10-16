import MicroCFTA.SourceCurrentAllocatedNativeRequestAdmission
import MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode
import MicroCFTA.SourceCurrentAllocatedNativePairAdmission
open MicroCFTA MicroCFTA.Cache MicroCFTA.Language MicroCFTA.IntersectSchedule
open MicroCFTA.InternedConstructorTemplates MicroCFTA.InternedProbeProvenance
open MicroCFTA.InternedBinderProtocol
open MicroCFTA.SourceRecursiveIntersectionKernel MicroCFTA.SourceRecursiveIntersectionThunks
open MicroCFTA.SourceRecursiveIntersectionCode MicroCFTA.SourceRecursiveIntersectionInputView
open MicroCFTA.SourceCurrentAllocatedNativeContextCache MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache
open MicroCFTA.SourceCurrentAllocatedNativeContextRebase
open MicroCFTA.SourceCurrentAllocatedNativeRequestAdmission
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

-- A literal joined row and then its ordered child pair need no result law.
example [DecidableEq Symbol] (source : State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Term Symbol → Bool) (model : InputMeaning (view source holds))
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (a b : Interned InternedBinderProtocol.NodeKey) (left right : List (EdgeValue Symbol Guard))
    (ld rd : Nat) (lf rf : List Reference)
    (scope : NodeScope source ⟨domain, .node a left ld lf, .node b right rd rf⟩)
    (inputs : NodeInputs (view source holds) model ⟨domain, .node a left ld lf, .node b right rd rf⟩)
    (row : EdgeValue Symbol Guard × EdgeValue Symbol Guard) (rowMember : row ∈ pairs left right)
    (pair : Value Symbol Guard × Value Symbol Guard) (childMember : pair ∈ row.1.children.zip row.2.children) :
    NodeScope source ⟨domain, pair.1, pair.2⟩ ∧ NodeInputs (view source holds) model ⟨domain, pair.1, pair.2⟩ := by
  have rowAdmission := rows source facts holds model domain a left ld lf b right rd rf scope inputs row rowMember
  exact child source facts holds model ⟨domain, row.1, row.2⟩ rowAdmission.1 rowAdmission.2 pair childMember

-- The exact grown-heap read supplies a child's published request certificate.
example [DecidableEq (EdgeKey Symbol Guard)]
    (source : State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (inputs : FiniteInput (view source holds)) (machine : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine) (growth : Grows source machine.heap)
    (history : Extends source.nodes.issued machine.heap.nodes.issued)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat) (other bound : Value Symbol Guard)
    (scope : NodeScope source ⟨domain, .reference (.interned name), other⟩)
    (known : NodeCovered inputs ⟨domain, .reference (.interned name), other⟩)
    (member : name ∈ SourceRecursiveIntersectionDomain.names domain.key)
    (read : SourcePreparedSharedRows.read machine.heap name = some bound) :
    SourceCurrentAllocatedNativeAdmissionCode.Certified source holds inputs (requestNode domain bound other) machine
      (fun after value => Available after.heap value) := by
  have next := left_reference source machine.heap valid.1 growth history holds _ domain name other scope known.1 member bound read
  exact SourceCurrentAllocatedNativeAdmissionCode.requestNode_certified source holds inputs _ machine next.1 ⟨next.2, known.2⟩

-- Literal entered domains combine admitted bodies with covered canonical pair names.
example (source : State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Term Symbol → Bool) (inputs : FiniteInput (view source holds))
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request) (known : NodeCovered inputs request)
    (cache : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (valid : Cache.Valid cache) (a b : Nat)
    (first : SourceRecursiveIntersectionControl.identity request.left = some a)
    (second : SourceRecursiveIntersectionControl.identity request.right = some b) :
    let domain := (SourceRecursiveIntersectionEnvironment.enter cache request.domain.key request.left request.right a b).1
    NodeScope source ⟨domain, body request.left, body request.right⟩ ∧
      NodeCovered inputs ⟨domain, body request.left, body request.right⟩ := by
  have admitted := entered source facts holds _ request scope known.1 cache valid a b
  exact ⟨admitted.1, admitted.2,
    SourceCurrentAllocatedNativePairAdmission.request_entered_seen inputs request cache valid known.2 known.1 a b first second⟩

-- Zip admission preserves a shared domain without a matching-arity premise.
example (view : View Symbol) (model : InputMeaning view) (request : EdgeRequest Symbol Guard)
    (known : EdgeInputs view model request) (pair : Value Symbol Guard × Value Symbol Guard)
    (inside : pair ∈ request.left.children.zip request.right.children) :
    model.valid (inputOf pair.1) ∧ model.valid (inputOf pair.2) := by
  have admitted := child_inputs view model request known pair inside
  exact ⟨admitted.2.2.1, admitted.2.2.2⟩
