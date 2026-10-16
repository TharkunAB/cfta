import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode
import MicroCFTA.SourceRecursiveIntersectionKernelReadback

/-!
# Local structural certificates for finite ordinary node code

The ordered row join retains one structural certificate per original pair.
Actual node construction preserves the domain and bounds the result by each
parent. The dispatcher follows its literal guard order. These certificates
do not assert recursive execution or completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedFiniteOrdinaryCode SourceCurrentAllocatedFiniteOrdinaryStored
open SourceEqualityRequiredSemanticCache (SemanticReady)
open MergedOrdinaryHeight (height edgeHeight edgesHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
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
    (left right : List (EdgeValue Symbol Guard)) (leftDomain : DRows left) (rightDomain : DRows right)
    (pairs : List (EdgeValue Symbol Guard × EdgeValue Symbol Guard))
    (inside : ∀ pair ∈ pairs, pair.1 ∈ left ∧ pair.2 ∈ right)
    (values : List (EdgeValue Symbol Guard))
    (laws : Language.All₂ (fun pair value => EdgeCertificate ⟨domain, pair.1, pair.2⟩ value) pairs values) :
    DRows values ∧ (∀ value ∈ values, edgeHeight value ≤ edgesHeight left ∧ edgeHeight value ≤ edgesHeight right) := by
  induction laws with
  | nil => exact ⟨.nil, by intro value member; cases member⟩
  | @cons pair value pairs values law tail ih =>
      have members := inside pair List.mem_cons_self
      have first := law seen (leftDomain.member pair.1 members.1) (rightDomain.member pair.2 members.2)
      have rest := ih (fun pair member => inside pair (List.mem_cons_of_mem _ member))
      refine ⟨.cons first.1 rest.1, ?_⟩
      intro output member
      rcases List.mem_cons.mp member with same | later
      · subst output
        exact ⟨Nat.le_trans first.2.1 ((MergedOrdinaryHeight.edgesHeight_le _ _).mp (Nat.le_refl _) _ members.1),
          Nat.le_trans first.2.2 ((MergedOrdinaryHeight.edgesHeight_le _ _).mp (Nat.le_refl _) _ members.2)⟩
      · exact rest.2 output later

/-- The literal row join and constructor produce an ordinary result bounded by each parent. -/
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
  have rows := paired_rows domain seen left right leftDomain rightDomain (pairs left right)
    (fun pair member => by
      have inside := (pairs_member left right pair).mp member
      exact ⟨inside.1, inside.2.1⟩) values paired.2
  intro _ _ _
  refine ⟨SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode values middle.heap
    middleValid.1.coherent middleValid.1.linked paired.1 rows.1, ?_, ?_⟩
  · exact SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode_bound values middle.heap
      middleValid.1.coherent middleValid.1.linked paired.1 (height (.node first left leftDepth leftFree))
      (fun edge member => Nat.add_le_add_right (rows.2 edge member).1 1)
  · exact SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode_bound values middle.heap
      middleValid.1.coherent middleValid.1.linked paired.1 (height (.node second right rightDepth rightFree))
      (fun edge member => Nat.add_le_add_right (rows.2 edge member).2 1)

/-- The current node dispatcher uses only exact smaller-result certificates in this domain. -/
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
    exact fun _ _ _ => ⟨.empty, Nat.zero_le _, Nat.zero_le _⟩
  · by_cases resetCase : SourceRecursiveIntersectionControl.reset domain.key left right = true
    · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, Bool.false_eq_true, ite_false, ite_true]
      refine ⟨⟨rfl, leftDomain, rightDomain⟩, ?_⟩
      intro value after _ _ _ _ law _ leftNode rightNode
      exact law rfl leftNode rightNode
    · by_cases selfCase : SourceRecursiveIntersectionControl.closedSelf left right = true
      · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, selfCase, Bool.false_eq_true, ite_false, ite_true]
        have same := SourceRecursiveIntersectionControl.self_record state.heap valid.1 left right
          leftAvailable rightAvailable selfCase
        exact fun _ leftNode _ => ⟨leftNode, Nat.le_refl _, by simpa only [same] using Nat.le_refl (height right)⟩
      · by_cases swapCase : SourceRecursiveIntersectionControl.greater left right = true
        · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, selfCase, swapCase, Bool.false_eq_true, ite_false, ite_true]
          refine ⟨⟨seen, rightDomain, leftDomain⟩, ?_⟩
          intro value after _ _ _ _ law seenEmpty leftNode rightNode
          have result := law seenEmpty rightNode leftNode
          exact ⟨result.1, result.2.2, result.2.1⟩
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

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNode
