import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryKeys
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdge

/-!
# Original operand key certificates in ordinary query code

Each recursive instruction retains safe original operand records.
Continuations permit arbitrary returned values. Constructors do not
introduce another recursive query on their newly constructed result.
Driver finish instructions retain the continuation certificate.
This static certificate alone asserts no physical state invariant.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryWordCode
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "KNode" => SourceCurrentAllocatedFiniteOrdinaryKeys.Node
local notation "KEdge" => SourceCurrentAllocatedFiniteOrdinaryKeys.Edge
local notation "KRows" => SourceCurrentAllocatedFiniteOrdinaryKeys.Rows
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain

/-- Node instructions retain the empty domain and both original recursive key bounds. -/
def NodeInputs (bits : Nat) (source : Machine Symbol Guard) (request : NodeRequest Symbol Guard) : Prop :=
  request.domain = emptyDomain ∧ KNode bits request.left ∧ KNode bits request.right ∧
    Available source.heap request.left ∧ Available source.heap request.right

/-- Edge instructions retain complete original rows and their bounded child records. -/
def EdgeInputs (bits : Nat) (source : Machine Symbol Guard) (request : EdgeRequest Symbol Guard) : Prop :=
  request.domain = emptyDomain ∧ KEdge bits request.left ∧ KEdge bits request.right ∧
    EdgeResident source.heap request.left ∧ EdgeResident source.heap request.right

/-- Only original bounded requests and source constructor continuations occur in this fragment. -/
def Certified (bits : Nat) (source : Machine Symbol Guard) (code : Code Symbol Guard A) : Prop :=
  match code with
  | .pure _ | .fail _ => True
  | .work _ next => ∀ value, Certified bits source (next value)
  | .node request next => NodeInputs bits source request ∧ ∀ value, Certified bits source (next value)
  | .edge request next => EdgeInputs bits source request ∧ ∀ value, Certified bits source (next value)
  | .finishNode _ _ next | .finishEdge _ _ next => Certified bits source next
  | .enter .. | .read .. | .optionalBinder .. => False

/-- Appended source continuations retain the original operand bounds. -/
theorem certified_bind (bits : Nat) (source : Machine Symbol Guard) (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (certificate : Certified bits source code) (continuation : ∀ value, Certified bits source (next value)) :
    Certified bits source (code.bind next) := by
  induction code with
  | pure value => exact continuation value
  | fail => trivial
  | work job resume ih => exact fun value => ih value (certificate value)
  | node request resume ih | edge request resume ih =>
      exact ⟨certificate.1, fun value => ih value (certificate.2 value)⟩
  | finishNode handle value rest ih | finishEdge handle value rest ih => exact ih certificate
  | enter | read | optionalBinder => cases certificate

/-- Ordered walks retain only the bounds of their original input occurrences. -/
theorem certified_walk (bits : Nat) (source : Machine Symbol Guard) (call : A → Code Symbol Guard B) (values : List A)
    (calls : ∀ value ∈ values, Certified bits source (call value)) : Certified bits source (walk call values) := by
  induction values with
  | nil => trivial
  | cons value values ih =>
      apply certified_bind bits source (call value) _ (calls value List.mem_cons_self)
      intro result
      apply certified_bind bits source (walk call values) _
        (ih (fun item member => calls item (List.mem_cons_of_mem _ member)))
      intro results
      trivial

/-- A literal node request uses only its bounded original operands. -/
theorem request_node (bits : Nat) (source : Machine Symbol Guard) (request : NodeRequest Symbol Guard) (inputs : NodeInputs bits source request) :
    Certified bits source (requestNode request.domain request.left request.right) := ⟨inputs, fun _ => trivial⟩

/-- A literal edge request uses only its bounded original rows. -/
theorem request_edge (bits : Nat) (source : Machine Symbol Guard) (request : EdgeRequest Symbol Guard) (inputs : EdgeInputs bits source request) :
    Certified bits source (requestEdge request.domain request.left request.right) := ⟨inputs, fun _ => trivial⟩

/-- Complete original row bounds cover every selected source row pair. -/
theorem rows_certified [DecidableEq Symbol] (bits : Nat) (source : Machine Symbol Guard) (left right : List Edge)
    (leftKeys : KRows bits left) (rightKeys : KRows bits right)
    (leftResident : Edges source.heap left) (rightResident : Edges source.heap right) :
    Certified bits source (compileRows emptyDomain left right) := by
  unfold compileRows
  apply certified_bind bits source _ _
  · apply certified_walk bits source
    intro pair member
    have inside := (pairs_member left right pair).mp member
    exact request_edge bits source ⟨emptyDomain, pair.1, pair.2⟩
      ⟨rfl, leftKeys.member pair.1 inside.1, rightKeys.member pair.2 inside.2.1,
        leftResident pair.1 inside.1, rightResident pair.2 inside.2.1⟩
  · intro results
    intro result
    trivial

/-- The actual node dispatcher emits no query on a newly constructed result. -/
theorem node_certified [DecidableEq Symbol] (bits : Nat) (source : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid source) (request : NodeRequest Symbol Guard)
    (inputs : NodeInputs bits source request) : Certified bits source (compileNode request) := by
  rcases request with ⟨domain, left, right⟩
  rcases inputs with ⟨rfl, leftKeys, rightKeys, leftAvailable, rightAvailable⟩
  by_cases emptyCase : SourceRecursiveIntersectionControl.hasEmpty left right = true
  · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, ite_true, Certified]
  · by_cases resetCase : SourceRecursiveIntersectionControl.reset (emptyDomain).key left right = true
    · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, Bool.false_eq_true, ite_false, ite_true]
      exact request_node bits source _ ⟨rfl, leftKeys, rightKeys, leftAvailable, rightAvailable⟩
    · by_cases selfCase : SourceRecursiveIntersectionControl.closedSelf left right = true
      · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, selfCase, Bool.false_eq_true, ite_false, ite_true, Certified]
      · by_cases swapCase : SourceRecursiveIntersectionControl.greater left right = true
        · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, selfCase, swapCase, Bool.false_eq_true, ite_false, ite_true]
          exact request_node bits source ⟨emptyDomain, right, left⟩ ⟨rfl, rightKeys, leftKeys, rightAvailable, leftAvailable⟩
        · simp only [compileNode, SourceRecursiveIntersectionControl.decision, emptyCase, resetCase, selfCase, swapCase, Bool.false_eq_true, ite_false]
          have firstDomain := leftKeys.domain
          have secondDomain := rightKeys.domain
          cases firstDomain with
          | empty => simp only [SourceRecursiveIntersectionControl.identity, SourceRecursiveIntersectionCode.unsupported, Certified]
          | @ordinary left first leftDepth leftFree leftRows =>
              cases secondDomain with
              | empty => simp only [SourceRecursiveIntersectionControl.identity, SourceRecursiveIntersectionCode.unsupported, Certified]
              | @ordinary right second rightDepth rightFree rightRows =>
                  simpa only [SourceRecursiveIntersectionControl.identity, IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey,
                    List.not_mem_nil, Bool.false_eq_true, ite_false, SourceRecursiveIntersectionControl.payload] using
                    rows_certified bits source left right leftKeys.rows rightKeys.rows
                      (resident_edges source.heap valid.1.linked _ leftAvailable.resident)
                      (resident_edges source.heap valid.1.linked _ rightAvailable.resident)

/-- Accepted checked code requests only the original paired children. -/
theorem children_certified (bits : Nat) (source : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid source) (request : EdgeRequest Symbol Guard) (inputs : EdgeInputs bits source request)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula) :
    Certified bits source (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) := by
  unfold SourceEqualityNativeCheckedCode.children
  apply certified_bind bits source _ _
  · apply certified_walk bits source
    intro pair member
    have inside := List.of_mem_zip member
    exact request_node bits source ⟨request.domain, pair.1, pair.2⟩
      ⟨inputs.1, inputs.2.1.2.member pair.1 inside.1, inputs.2.2.1.2.member pair.2 inside.2,
        valid.1.cached.edges _ request.left inputs.2.2.2.1 pair.1 inside.1,
        valid.1.cached.edges _ request.right inputs.2.2.2.2 pair.2 inside.2⟩
  · intro values result
    trivial

/-- The rejected sentinel introduces no recursive request. -/
theorem sentinel_certified (bits : Nat) (source : Machine Symbol Guard) (edge : Edge) :
    Certified bits source (SourceEqualityNativeCheckedCode.sentinel edge) := fun _ => trivial

/-- Every actual checked edge-body yield retains the bounded original request schedule. -/
theorem body_certified {width : Nat} (bits : Nat) (source : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid source) (request : EdgeRequest Symbol Guard)
    (inputs : EdgeInputs bits source request) (next : Edge → Code Symbol Guard Output)
    (before after : SourceEqualityNativeDemand.State width) (rest : Code Symbol Guard Output)
    (yielded : SourceEqualityNativeDemand.body request next before = .yielded (.code rest) after)
    (continuation : ∀ value, Certified bits source (next value)) : Certified bits source rest := by
  have bindCode : ∀ code, Certified bits source code → Certified bits source (code.bind next) :=
    fun code certificate => certified_bind bits source code next certificate continuation
  unfold SourceEqualityNativeDemand.body at yielded
  split at yielded
  · simp only [SourceEqualityNativeDemand.sentinel] at yielded
    cases yielded
    exact bindCode _ (sentinel_certified bits source _)
  · split at yielded
    · cases yielded
    · cases yielded
    · split at yielded
      · cases yielded
      · cases yielded
      · dsimp only at yielded
        split at yielded
        · cases yielded
        · simp only [SourceEqualityNativeDemand.sentinel] at yielded
          cases yielded
          exact bindCode _ (sentinel_certified bits source _)
        · simp only [SourceEqualityNativeDemand.sentinel] at yielded
          cases yielded
          exact bindCode _ (sentinel_certified bits source _)
        · cases yielded
          exact bindCode _ (children_certified bits source valid request inputs _)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryWordCode
