import MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode
import MicroCFTA.SourceCurrentAllocatedNativeRequestAdmission
import MicroCFTA.SourceCurrentAllocatedNativePairAdmission

/-!
# Local admission certificates for actual source node code

The fixed source scope and parent admission derive every child request.
Ordered row and union traversals retain the literal child lists.
Actual domain entry and later binder reads retain the same input model.
Primitive returns supply physical result facts, not input membership.
The certificates do not assume successful recursive execution.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeAdmissionNodeCertificates
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceCurrentAllocatedNativeContextCache
open SourceCurrentAllocatedNativeAdmissionCache SourceCurrentAllocatedNativeAdmissionCode
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq (EdgeKey Symbol Guard)]

section Source
variable (source : InternedConstructorTemplates.State Symbol Guard)
  (holds : Guard → Term Symbol → Bool) (inputs : FiniteInput (view source holds))

private theorem work_certified (job : Work Symbol Guard A) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state)
    (property : InternedConstructorTemplates.State Symbol Guard → A → Prop)
    (verified : InternedNestedFacts.Verified state.heap (InternedNestedConstruction.work job state.heap) property) :
    Certified source holds inputs (.work job .pure) state (fun after value => property after.heap value) := by
  intro value after done _ _ _
  exact (safe_work job state valid property verified).2.2 value after done

private theorem node_walk_certified (request : A → NodeRequest Symbol Guard) (values : List A)
    (known : ∀ value ∈ values, NodeScope source (request value) ∧ NodeCovered inputs (request value))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified source holds inputs (SourceRecursiveIntersectionCode.walk
      (fun value => .node (request value) .pure) values) state (fun after outputs => Values after.heap outputs) := by
  exact walk_certified source holds inputs _ values
    (fun _ value => NodeScope source (request value) ∧ NodeCovered inputs (request value))
    (fun after value => Available after.heap value) (by intro _ _ _ _ known; exact known) available_stable
    (fun value _ current _ _ known =>
      requestNode_certified source holds inputs (request value) current known.1 known.2)
    state valid semantic known

private theorem edge_walk_certified (request : A → EdgeRequest Symbol Guard) (values : List A)
    (known : ∀ value ∈ values, EdgeScope source (request value) ∧ EdgeCovered inputs (request value))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified source holds inputs (SourceRecursiveIntersectionCode.walk
      (fun value => .edge (request value) .pure) values) state (fun after outputs => Edges after.heap outputs) := by
  exact walk_certified source holds inputs _ values
    (fun _ value => EdgeScope source (request value) ∧ EdgeCovered inputs (request value))
    (fun after value => EdgeResident after.heap value) (by intro _ _ _ _ known; exact known) edge_stable
    (fun value _ current _ _ known =>
      requestEdge_certified source holds inputs (request value) current known.1 known.2)
    state valid semantic known

/-- Literal hash-joined rows derive each child edge's source scope and model admission. -/
theorem rows_certified [DecidableEq Symbol] (facts : Facts source)
    (domain : Interned DomainKey)
    (first : Interned NodeKey) (left : List (EdgeValue Symbol Guard)) (leftDepth : Nat) (leftFree : List Reference)
    (second : Interned NodeKey) (right : List (EdgeValue Symbol Guard)) (rightDepth : Nat) (rightFree : List Reference)
    (scope : NodeScope source ⟨domain, .node first left leftDepth leftFree, .node second right rightDepth rightFree⟩)
    (known : NodeCovered inputs ⟨domain, .node first left leftDepth leftFree, .node second right rightDepth rightFree⟩)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified source holds inputs (compileRows domain left right) state (fun after value => Available after.heap value) := by
  unfold compileRows
  have calls : ∀ pair ∈ pairs left right, EdgeScope source ⟨domain, pair.1, pair.2⟩ ∧
      EdgeCovered inputs ⟨domain, pair.1, pair.2⟩ := by
    intro pair member
    have admitted := SourceCurrentAllocatedNativeRequestAdmission.rows source facts holds _ domain
      first left leftDepth leftFree second right rightDepth rightFree scope known.1 pair member
    exact ⟨admitted.1, admitted.2, known.2⟩
  apply certified_bind source holds inputs _ _ state valid semantic _ _
    (edge_walk_certified source holds inputs (fun pair => ⟨domain, pair.1, pair.2⟩) (pairs left right) calls state valid semantic)
  intro values middle middleValid _ _ children
  exact work_certified source holds inputs (makeNode values) middle middleValid Available
    (InternedNestedFacts.node_verified values middle.heap middleValid.1 children)

/-- Each left-union request uses its literal member and the original right operand. -/
theorem left_union_certified (facts : Facts source) (domain : Interned DomainKey)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (right : Value Symbol Guard) (scope : NodeScope source ⟨domain, .union entry members depth free, right⟩)
    (known : NodeCovered inputs ⟨domain, .union entry members depth free, right⟩)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified source holds inputs
      ((SourceRecursiveIntersectionCode.walk (fun member => requestNode domain member right) members).bind
        (fun values => .work (makeUnion values) .pure)) state (fun after value => Available after.heap value) := by
  have calls : ∀ member ∈ members, NodeScope source ⟨domain, member, right⟩ ∧
      NodeCovered inputs ⟨domain, member, right⟩ := by
    intro member present
    have admitted := SourceCurrentAllocatedNativeRequestAdmission.left_union source facts holds _
      domain entry members depth free right scope known.1 member present
    exact ⟨admitted.1, admitted.2, known.2⟩
  apply certified_bind source holds inputs _ _ state valid semantic _ _
    (node_walk_certified source holds inputs (fun member => ⟨domain, member, right⟩) members calls state valid semantic)
  intro values middle middleValid _ _ children
  exact work_certified source holds inputs (makeUnion values) middle middleValid Available
    (InternedNestedFacts.union_verified values middle.heap middleValid.1 children)

/-- Each right-union request retains the original left operand and literal member. -/
theorem right_union_certified (facts : Facts source) (domain : Interned DomainKey)
    (left : Value Symbol Guard) (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (scope : NodeScope source ⟨domain, left, .union entry members depth free⟩)
    (known : NodeCovered inputs ⟨domain, left, .union entry members depth free⟩)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified source holds inputs
      ((SourceRecursiveIntersectionCode.walk (fun member => requestNode domain left member) members).bind
        (fun values => .work (makeUnion values) .pure)) state (fun after value => Available after.heap value) := by
  have calls : ∀ member ∈ members, NodeScope source ⟨domain, left, member⟩ ∧
      NodeCovered inputs ⟨domain, left, member⟩ := by
    intro member present
    have admitted := SourceCurrentAllocatedNativeRequestAdmission.right_union source facts holds _
      domain left entry members depth free scope known.1 member present
    exact ⟨admitted.1, admitted.2, known.2⟩
  apply certified_bind source holds inputs _ _ state valid semantic _ _
    (node_walk_certified source holds inputs (fun member => ⟨domain, left, member⟩) members calls state valid semantic)
  intro values middle middleValid _ _ children
  exact work_certified source holds inputs (makeUnion values) middle middleValid Available
    (InternedNestedFacts.union_verified values middle.heap middleValid.1 children)

/-- Actual domain entry derives admitted bodies and covered names before the child call. -/
theorem mu_certified (facts : Facts source) (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (known : NodeCovered inputs request) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (ready : NodeReady state request) :
    Certified source holds inputs (compileMu request.domain request.left request.right) state
      (fun after value => Available after.heap value) := by
  cases first : SourceRecursiveIntersectionControl.identity request.left <;>
    cases second : SourceRecursiveIntersectionControl.identity request.right <;>
    simp only [compileMu, first, second]
  all_goals try trivial
  rename_i firstName secondName
  have entered := SourceRecursiveIntersectionKernel.entered state valid request.domain ready.1
    request.left request.right ready.2.1 ready.2.2 firstName secondName
  have child := SourceCurrentAllocatedNativeRequestAdmission.entered source facts holds _ request scope known.1
    state.domains valid.2 firstName secondName
  have seen := SourceCurrentAllocatedNativePairAdmission.request_entered_seen inputs request state.domains valid.2
    known.2 known.1 firstName secondName first second
  refine ⟨entered.1, entered.2.1, child.1, ⟨child.2, seen⟩, ?_⟩
  intro value after afterValid _ _ available result final done _ _ _
  exact (safe_optionalBinder _ value after afterValid available).2.2 result final done

/-- Literal left binder lookup derives the exact admitted bound request at the current heap. -/
theorem left_reference_certified (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard)
    (scope : NodeScope source ⟨domain, .reference (.interned name), other⟩)
    (known : NodeCovered inputs ⟨domain, .reference (.interned name), other⟩)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Certified source holds inputs (compileReference domain name other true) state
      (fun after value => Available after.heap value) := by
  unfold compileReference
  split
  · rename_i member
    simp only [Certified]
    cases found : SourcePreparedSharedRows.read state.heap name with
    | none => trivial
    | some bound =>
        have admitted := SourceCurrentAllocatedNativeRequestAdmission.left_reference source state.heap valid.1
          growth history holds _ domain name other scope known.1 member bound found
        exact requestNode_certified source holds inputs _ state admitted.1 ⟨admitted.2, known.2⟩
  · trivial

/-- Literal right binder lookup preserves operand order and the same original model. -/
theorem right_reference_certified (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard)
    (scope : NodeScope source ⟨domain, other, .reference (.interned name)⟩)
    (known : NodeCovered inputs ⟨domain, other, .reference (.interned name)⟩)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Certified source holds inputs (compileReference domain name other false) state
      (fun after value => Available after.heap value) := by
  unfold compileReference
  split
  · rename_i member
    simp only [Certified]
    cases found : SourcePreparedSharedRows.read state.heap name with
    | none => trivial
    | some bound =>
        have admitted := SourceCurrentAllocatedNativeRequestAdmission.right_reference source state.heap valid.1
          growth history holds _ domain name other scope known.1 member bound found
        exact requestNode_certified source holds inputs _ state admitted.1 ⟨admitted.2, known.2⟩
  · trivial

end Source

/-- Every actual node branch derives child admission without a completed callback or result law. -/
theorem node_certified [DecidableEq Symbol]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (inputs : FiniteInput (view source holds)) (request : NodeRequest Symbol Guard)
    (scope : NodeScope source request) (known : NodeCovered inputs request)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) (ready : NodeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Certified source holds inputs (compileNode request) state (fun after value => Available after.heap value) := by
  cases request with
  | mk domain left right =>
    cases selected : SourceRecursiveIntersectionControl.decision domain.key left right with
    | empty => simpa only [compileNode, selected, Certified] using empty_available state.heap
    | reset =>
        have admitted := SourceCurrentAllocatedNativeRequestAdmission.reset source holds _ ⟨domain, left, right⟩ scope known.1
        have seen := SourceCurrentAllocatedNativePairAdmission.empty_seen inputs
        simpa only [compileNode, selected] using requestNode_certified source holds inputs _ state admitted.1 ⟨admitted.2, seen⟩
    | self => simpa only [compileNode, selected, Certified] using ready.2.1
    | swap =>
        simpa only [compileNode, selected] using requestNode_certified source holds inputs _ state
          (scope.swap source domain left right)
          ⟨SourceCurrentAllocatedNativeRequestAdmission.node_swap _ _ ⟨domain, left, right⟩ known.1, known.2⟩
    | repeated key =>
        simp only [compileNode, selected, Certified]
        apply reference_available state.heap (.intersection key.1 key.2)
        intro name member
        simp [Value.free] at member
    | bothMu | leftMu | rightMu =>
        simpa only [compileNode, selected] using mu_certified source holds inputs facts ⟨domain, left, right⟩ scope known state valid ready
    | leftUnion =>
        simp only [compileNode, selected]
        cases left <;> try trivial
        exact left_union_certified source holds inputs facts _ _ _ _ _ _ scope known state valid semantic
    | rightUnion =>
        simp only [compileNode, selected]
        cases right <;> try trivial
        exact right_union_certified source holds inputs facts _ _ _ _ _ _ scope known state valid semantic
    | leftReference =>
        simp only [compileNode, selected]
        cases left <;> try trivial
        rename_i name
        cases name <;> first
          | exact left_reference_certified source holds inputs _ _ _ scope known state valid growth history
          | trivial
    | rightReference =>
        simp only [compileNode, selected]
        cases right <;> try trivial
        rename_i name
        cases name <;> first
          | exact right_reference_certified source holds inputs _ _ _ scope known state valid growth history
          | trivial
    | ordinary =>
        simp only [compileNode, selected]
        cases left <;> cases right <;> try trivial
        exact rows_certified source holds inputs facts _ _ _ _ _ _ _ _ _ scope known state valid semantic
    | unsupported => simp only [compileNode, selected, SourceRecursiveIntersectionCode.unsupported, Certified]
end MicroCFTA.SourceCurrentAllocatedNativeAdmissionNodeCertificates
