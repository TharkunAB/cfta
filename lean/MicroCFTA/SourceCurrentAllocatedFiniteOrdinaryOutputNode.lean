import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputCode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputConstructors
import MicroCFTA.SourceRecursiveIntersectionKernelReadback

/-!
# Output profiles for local ordinary node code

The ordered join retains one result profile per original row pair.
The final constructor filters and canonicalizes these resident rows.
All profile bounds come from the original operands and child certificates.
These local certificates do not assert completed execution.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputNode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedFiniteOrdinaryOutputCode SourceCurrentAllocatedFiniteOrdinaryOutputStored
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "RowsShape" => SourceCurrentAllocatedFiniteOrdinaryNativeProfile.RowsShape
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq Symbol] in
private theorem edge_walk
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (pairs : List (EdgeValue Symbol Guard × EdgeValue Symbol Guard))
    (known : ∀ pair ∈ pairs, EdgeInputs ⟨domain, pair.1, pair.2⟩)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified (SourceRecursiveIntersectionCode.walk (fun pair => requestEdge domain pair.1 pair.2) pairs) state
      (fun after values => InternedNestedProvenance.Edges after.heap values ∧
        Language.All₂ (fun pair value => EdgeCertificate ⟨domain, pair.1, pair.2⟩ value) pairs values) := by
  induction pairs generalizing state with
  | nil => exact ⟨(by intro value member; cases member), .nil⟩
  | cons first rest ih =>
      simp only [SourceRecursiveIntersectionCode.walk, requestEdge, Code.bind, Certified]
      refine ⟨known first List.mem_cons_self, ?_⟩
      intro value middle middleValid growth middleSemantic resident law
      apply certified_bind _ _ middle middleValid middleSemantic _ _
        (ih (fun pair member => known pair (List.mem_cons_of_mem _ member)) middle middleValid middleSemantic)
      intro values after _ later _ tail
      exact ⟨by intro edge member; cases member with
        | head => exact edge_grows _ _ later.heap value resident
        | tail _ member => exact tail.1 edge member, .cons law tail.2⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem paired_rows
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (seen : domain.key.seen = [])
    (rows arity : Nat) (left right : List (EdgeValue Symbol Guard))
    (leftShape : RowsShape rows arity left) (rightShape : RowsShape rows arity right)
    (pairs : List (EdgeValue Symbol Guard × EdgeValue Symbol Guard))
    (inside : ∀ pair ∈ pairs, pair.1 ∈ left ∧ pair.2 ∈ right)
    (values : List (EdgeValue Symbol Guard))
    (laws : Language.All₂ (fun pair value => EdgeCertificate ⟨domain, pair.1, pair.2⟩ value) pairs values) :
    RowsShape (rows * rows) (max arity 1) values := by
  induction laws with
  | nil => trivial
  | @cons pair value pairs values law tail ih =>
      have members := inside pair List.mem_cons_self
      exact ⟨law seen rows arity
        (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.RowsShape.member left leftShape _ members.1)
        (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.RowsShape.member right rightShape _ members.2),
        ih (fun pair member => inside pair (List.mem_cons_of_mem _ member))⟩

/-- The literal join and node constructor bound every output row and descendant arity. -/
theorem rows_certified
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (seen : domain.key.seen = [])
    (first : Interned InternedBinderProtocol.NodeKey) (left : List (EdgeValue Symbol Guard))
    (leftDepth : Nat) (leftFree : List InternedBinderProtocol.Reference)
    (second : Interned InternedBinderProtocol.NodeKey) (right : List (EdgeValue Symbol Guard))
    (rightDepth : Nat) (rightFree : List InternedBinderProtocol.Reference)
    (leftDomain : DRows left) (rightDomain : DRows right)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (semantic : SemanticReady state.heap) :
    Certified (compileRows domain left right) state
      (fun _ value => NodeCertificate
        ⟨domain, .node first left leftDepth leftFree, .node second right rightDepth rightFree⟩ value) := by
  unfold compileRows
  apply certified_bind _ _ state valid semantic _ _
    (edge_walk domain (pairs left right) (fun pair member => by
      have inside := (pairs_member left right pair).mp member
      exact ⟨seen, leftDomain.member pair.1 inside.1, rightDomain.member pair.2 inside.2.1⟩)
      state valid semantic)
  intro values middle middleValid _ _ paired
  intro value after done _inputs _afterValid _later _afterSemantic
  rw [(work_done _ middle value after done).1]
  intro _ rows arity leftShape rightShape
  apply SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeNode values middle.heap
    middleValid.1.coherent middleValid.1.linked paired.1
  · exact paired_rows domain seen rows arity left right leftShape.2 rightShape.2 (pairs left right)
      (fun pair member => by
        have inside := (pairs_member left right pair).mp member
        exact ⟨inside.1, inside.2.1⟩) values paired.2
  · rw [← paired.2.length_eq]
    exact Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.pairs_length_le left right)
      (Nat.mul_le_mul leftShape.1 rightShape.1)

/-- The actual dispatcher retains conditional output profiles for each source branch. -/
theorem node_certified
    (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (semantic : SemanticReady state.heap)
    (leftAvailable : Available state.heap request.left) (rightAvailable : Available state.heap request.right)
    (inputs : NodeInputs request) :
    Certified (compileNode request) state (fun _ value => NodeCertificate request value) := by
  rcases request with ⟨domain, left, right⟩
  rcases inputs with ⟨seen, leftDomain, rightDomain⟩
  change domain.key.seen = [] at seen
  by_cases emptyCase : SourceRecursiveIntersectionControl.hasEmpty left right = true
  · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, ite_true]
    exact fun _ _ _ _ _ => trivial
  · by_cases resetCase : SourceRecursiveIntersectionControl.reset domain.key left right = true
    · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, Bool.false_eq_true, ite_false, ite_true]
      refine ⟨⟨rfl, leftDomain, rightDomain⟩, ?_⟩
      intro value after _ _ _ _ law _ rows arity leftShape rightShape
      exact law rfl rows arity leftShape rightShape
    · by_cases selfCase : SourceRecursiveIntersectionControl.closedSelf left right = true
      · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, selfCase, Bool.false_eq_true, ite_false, ite_true]
        have same := SourceRecursiveIntersectionControl.self_record state.heap valid.1 left right
          leftAvailable rightAvailable selfCase
        intro _ rows arity _ rightShape
        rw [same]
        exact SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape.mono right rightShape
          (Nat.le_mul_self rows) (Nat.le_max_left _ _)
      · by_cases swapCase : SourceRecursiveIntersectionControl.greater left right = true
        · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, selfCase, swapCase, Bool.false_eq_true, ite_false, ite_true]
          refine ⟨⟨seen, rightDomain, leftDomain⟩, ?_⟩
          intro value after _ _ _ _ law seenEmpty rows arity leftShape rightShape
          exact law seenEmpty rows arity rightShape leftShape
        · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, selfCase, swapCase, Bool.false_eq_true, ite_false]
          cases leftDomain with
          | empty => simp only [SourceRecursiveIntersectionControl.identity, SourceRecursiveIntersectionCode.unsupported, Certified]
          | @ordinary left first leftDepth leftFree leftRows =>
            cases rightDomain with
            | empty => simp only [SourceRecursiveIntersectionControl.identity, SourceRecursiveIntersectionCode.unsupported, Certified]
            | @ordinary right second rightDepth rightFree rightRows =>
              simpa only [SourceRecursiveIntersectionControl.identity, seen, List.not_mem_nil,
                Bool.false_eq_true, ite_false, SourceRecursiveIntersectionControl.payload] using
                rows_certified domain seen first left leftDepth leftFree second right rightDepth rightFree
                  leftRows rightRows state valid semantic

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputNode
