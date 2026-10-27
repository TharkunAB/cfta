import MicroCFTA.SourcePruningEnumerationNativeQueryArity
import MicroCFTA.SourceCurrentNativeWalkPrefix

/-!
# Arity through actual native node prefixes

The actual trace can stop at any retained control.
Completed child calls use the established whole-heap query theorem.
Unfinished child calls use only the bounded actual prefix condition.
The compiler's local constructor condition is derived from its literal code.
-/
namespace MicroCFTA.SourcePruningEnumerationNativePrefixArity
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {A B : Type} {width : Nat}

section Walk
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]

private theorem pure_prefix_heap (value : A) (fuel : Nat) (before after : Checked width)
    (remaining : Control A) (actual : Trace fuel (.code (.pure value)) before remaining after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases actual with
  | refl => exact heap
  | cons control state next middle final result count inputs one tail => cases one

/-- An actual ordered walk prefix retains the entire heap at its current control. -/
theorem walk_prefix_heap (limit : Nat) (call : A → Code Symbol Constraint B)
    (completed : ∀ (input : A) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (value : B), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (call input)) before (.code (.pure value)) after → Heap after.native.machine.heap)
    (prefixes : ∀ (input : A) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (remaining : Control B), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (call input)) before remaining after → Heap after.native.machine.heap)
    (fields : ∀ (input : A) (state : Checked width), Fields (.code (call input)) state)
    (inputs : List A) (fuel : Nat) (before after : Checked width) (remaining : Control (List B))
    (bounded : fuel ≤ limit) (initial : Good before) (heap : Heap before.native.machine.heap)
    (actual : Trace fuel (.code (walk call inputs)) before remaining after) : Heap after.native.machine.heap := by
  have bound : Trace fuel ((.code (walk call inputs) : Control (List B)).bind .pure)
      before remaining after := by
    simpa only [Control.bind, code_bind_pure] using actual
  rcases SourceCurrentNativeWalkPrefix.walk_prefix_cases call inputs .pure fuel before after remaining bound with
    ⟨index, input, values, entry, earlierFuel, currentFuel, inner,
      _selected, earlier, total, current, _nonpure, _same⟩ |
    ⟨walkFuel, outerFuel, values, middle, total, earlier, later⟩
  · have entryHeap := SourcePruningEnumerationNativeQueryArity.walk_heap limit call completed fields
      (inputs.take index) values before entry earlierFuel (by omega) initial heap earlier
    have entryFields : Fields (.code (walk call (inputs.take index))) before :=
      SourceCurrentAllocatedNativeCodeFields.fields_walk before.operations call (inputs.take index)
        (fun input _ => fields input before)
    have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects earlier.trace initial entryFields
    exact prefixes input currentFuel (by omega) entry after inner reached.1 entryHeap current
  · have middleHeap := SourcePruningEnumerationNativeQueryArity.walk_heap limit call completed fields
      inputs values before middle walkFuel (by omega) initial heap earlier
    exact pure_prefix_heap values outerFuel middle after remaining later middleHeap

end Walk

variable [DecidableEq (EdgeKey Symbol Constraint)]

private def LocalWorks : Code Symbol Constraint A → Prop
  | .pure _ | .fail _ => True
  | .work job next =>
      (∀ state, SourcePruningEnumerationNativeArityPrimitives.WorkFits job state) ∧
        ∀ value, LocalWorks (next value)
  | .enter _ _ _ _ _ next => ∀ value, LocalWorks (next value)
  | .read _ next => ∀ value, LocalWorks (next value)
  | .optionalBinder _ _ next => ∀ value, LocalWorks (next value)
  | .node _ next => ∀ value, LocalWorks (next value)
  | .edge _ next => ∀ value, LocalWorks (next value)
  | .finishNode _ _ next | .finishEdge _ _ next => LocalWorks next

private theorem localWorks_bind (code : Code Symbol Constraint A)
    (next : A → Code Symbol Constraint B) (first : LocalWorks code)
    (rest : ∀ value, LocalWorks (next value)) : LocalWorks (code.bind next) := by
  induction code with
  | pure value => exact rest value
  | fail => trivial
  | work job resume ih => exact ⟨first.1, fun value => ih value (first.2 value)⟩
  | enter domain left right firstKey secondKey resume ih | read name resume ih | optionalBinder key body resume ih | node request resume ih | edge request resume ih =>
      exact fun value => ih value (first value)
  | finishNode handle value next ih | finishEdge handle value next ih => exact ih first

private theorem localWorks_walk (call : A → Code Symbol Constraint B) (inputs : List A)
    (checked : ∀ input, LocalWorks (call input)) : LocalWorks (walk call inputs) := by
  induction inputs with
  | nil => trivial
  | cons first rest ih =>
      exact localWorks_bind _ _ (checked first) (fun _ => localWorks_bind _ _ ih (fun _ => trivial))

private theorem compileMu_localWorks (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : Value Symbol Constraint) : LocalWorks (compileMu domain left right) := by
  unfold compileMu
  split <;> simp only [LocalWorks, SourceRecursiveIntersectionCode.unsupported, implies_true]

private theorem compileReference_localWorks (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (name : Nat) (other : Value Symbol Constraint) (left : Bool) :
    LocalWorks (compileReference domain name other left) := by
  unfold compileReference
  split
  · intro found
    cases found with
    | none => trivial
    | some bound => split <;> intro value <;> trivial
  · trivial

variable [DecidableEq Symbol]

private theorem compileRows_localWorks (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : List (EdgeValue Symbol Constraint)) : LocalWorks (compileRows domain left right) := by
  apply localWorks_bind
  · exact localWorks_walk _ _ (fun _ => by intro value; trivial)
  · intro values
    exact ⟨SourcePruningEnumerationNativeArityPrimitives.makeNode_fits values, fun _ => trivial⟩

private theorem compileNode_localWorks (request : NodeRequest Symbol Constraint) :
    LocalWorks (compileNode request) := by
  cases selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right with
  | empty | reset | self | swap | repeated key | unsupported =>
      simp only [compileNode, selected, SourceRecursiveIntersectionCode.unsupported, requestNode, LocalWorks, implies_true]
  | bothMu | leftMu | rightMu =>
      simpa only [compileNode, selected] using compileMu_localWorks request.domain request.left request.right
  | leftUnion =>
      simp only [compileNode, selected]
      cases request.left with
      | union entry members depth free =>
          apply localWorks_bind
          · exact localWorks_walk _ _ (fun _ => by intro value; trivial)
          · intro values
            exact ⟨SourcePruningEnumerationNativeArityPrimitives.makeUnion_fits values, fun _ => trivial⟩
      | empty | reference | node | mu => trivial
  | rightUnion =>
      simp only [compileNode, selected]
      cases request.right with
      | union entry members depth free =>
          apply localWorks_bind
          · exact localWorks_walk _ _ (fun _ => by intro value; trivial)
          · intro values
            exact ⟨SourcePruningEnumerationNativeArityPrimitives.makeUnion_fits values, fun _ => trivial⟩
      | empty | reference | node | mu => trivial
  | leftReference =>
      simp only [compileNode, selected]
      cases request.left <;> try trivial
      rename_i name
      cases name <;> first | exact compileReference_localWorks _ _ _ _ | trivial
  | rightReference =>
      simp only [compileNode, selected]
      cases request.right <;> try trivial
      rename_i name
      cases name <;> first | exact compileReference_localWorks _ _ _ _ | trivial
  | ordinary =>
      simp only [compileNode, selected]
      cases request.left <;> cases request.right <;> first | exact compileRows_localWorks _ _ _ | trivial


private theorem yielded_prefix_heap (limit : Nat) (control next : Control A)
    (before middle after : Checked width) (remaining : Control A) (fuel : Nat)
    (bounded : fuel ≤ limit) (initial : Good before) (initialHeap : Heap before.native.machine.heap)
    (fields : Fields control before) (actual : Trace fuel control before remaining after)
    (one : step control before = .yielded next middle) (heap : Heap middle.native.machine.heap)
    (rest : ∀ count, count ≤ limit → Good middle → Heap middle.native.machine.heap → Fields next middle →
      Trace count next middle remaining after → Heap after.native.machine.heap) : Heap after.native.machine.heap := by
  cases actual with
  | refl => exact initialHeap
  | cons control state resumed current final result count inputs observed tail =>
      have same := Outcome.yielded.inj (one.symm.trans observed)
      rcases same.1 with rfl
      rcases same.2 with rfl
      have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control state initial inputs fields
      rw [one] at checked
      exact rest count (by omega) checked.1 heap checked.2.2.2.2.2 tail

private theorem localWorks_prefix_heap (limit : Nat)
    (nodes : ∀ (request : NodeRequest Symbol Constraint) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (remaining : Control (Value Symbol Constraint)), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (.node request .pure)) before remaining after → Heap after.native.machine.heap)
    (edges : ∀ (request : EdgeRequest Symbol Constraint) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (remaining : Control (EdgeValue Symbol Constraint)), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (.edge request .pure)) before remaining after → Heap after.native.machine.heap)
    (code : Code Symbol Constraint A) (checked : LocalWorks code)
    (before after : Checked width) (remaining : Control A) (fuel : Nat) (bounded : fuel ≤ limit)
    (initial : Good before) (heap : Heap before.native.machine.heap) (fields : Fields (.code code) before)
    (actual : Trace fuel (.code code) before remaining after) : Heap after.native.machine.heap := by
  induction code generalizing before after remaining fuel with
  | pure value | fail failure =>
      cases actual with
      | refl => exact heap
      | cons control state next middle final result count inputs one tail => cases one
  | work job next ih =>
      let result := run job before.native.machine.heap
      let middle : Checked width := {before with native := advance before.native {before.native.machine with heap := result.2}}
      have one : step (.code (.work job next)) before = .yielded (.code (next result.1)) middle := rfl
      apply yielded_prefix_heap limit _ _ before middle after remaining fuel bounded initial heap fields actual one
        (SourcePruningEnumerationNativeArityPrimitives.work_heap job before.native.machine.heap heap (checked.1 _))
      intro count bound good middleHeap retained tail
      exact ih result.1 (checked.2 result.1) middle after remaining count bound good middleHeap retained tail
  | enter domain left right first second next ih =>
      let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains domain.key left right first second
      let middle : Checked width := {before with native := advance before.native {before.native.machine with domains := entered.2}}
      have one : step (.code (.enter domain left right first second next)) before =
          .yielded (.code (next entered.1)) middle := rfl
      apply yielded_prefix_heap limit _ _ before middle after remaining fuel bounded initial heap fields actual one heap
      intro count bound good middleHeap retained tail
      exact ih entered.1 (checked entered.1) middle after remaining count bound good middleHeap retained tail
  | read name next ih =>
      let found := SourcePreparedSharedRows.read before.native.machine.heap name
      have one : step (.code (.read name next)) before = .yielded (.code (next found)) before := rfl
      apply yielded_prefix_heap limit _ _ before before after remaining fuel bounded initial heap fields actual one heap
      intro count bound good middleHeap retained tail
      exact ih found (checked found) before after remaining count bound good middleHeap retained tail
  | optionalBinder key body next ih =>
      cases actual with
      | refl => exact heap
      | cons control state rest middle final result count inputs one tail =>
          have currentHeap := SourcePruningEnumerationNativeArityPrimitives.step_optionalBinder_heap key body next
            before initial.native.machine.1 heap inputs
          rw [one, Outcome.state] at currentHeap
          have currentGood := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants _ before initial inputs fields
          rw [one] at currentGood
          cases built : SourceRecursiveIntersectionMaybeMu.maybeMu key body before.native.machine.heap with
          | done value finalHeap =>
              simp only [step, SourceRecursiveIntersectionNative.step, built, lift] at one
              cases one
              exact ih value (checked value) _ after remaining count (by omega)
                currentGood.1 currentHeap currentGood.2.2.2.2.2 tail
          | pending pending finalHeap =>
              simp only [step, SourceRecursiveIntersectionNative.step, built, lift] at one
              cases one
  | node request next ih =>
      rcases SourceCurrentNativeTracePrefixBind.bind_prefix_cases fuel (.code (.node request .pure)) next
        before after remaining actual with
        ⟨inner, first, _nonpure, _same⟩ | ⟨innerFuel, outerFuel, value, middle, total, first, rest⟩
      · exact nodes request fuel bounded before after inner initial heap first
      · have middleHeap := SourcePruningEnumerationNativeQueryArity.node_query_heap request before middle value
          innerFuel initial heap first
        have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects (first.bind next) initial fields
        exact ih value (checked value) middle after remaining outerFuel (by omega)
          reached.1 middleHeap reached.2.2.2.2 rest
  | edge request next ih =>
      rcases SourceCurrentNativeTracePrefixBind.bind_prefix_cases fuel (.code (.edge request .pure)) next
        before after remaining actual with
        ⟨inner, first, _nonpure, _same⟩ | ⟨innerFuel, outerFuel, value, middle, total, first, rest⟩
      · exact edges request fuel bounded before after inner initial heap first
      · have middleHeap := SourcePruningEnumerationNativeQueryArity.edge_query_heap request before middle value
          innerFuel initial heap first
        have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects (first.bind next) initial fields
        exact ih value (checked value) middle after remaining outerFuel (by omega)
          reached.1 middleHeap reached.2.2.2.2 rest
  | finishNode handle value next ih =>
      let middle : Checked width := {before with native := SourceRecursiveIntersectionThunks.finishNode handle value before.native}
      have one : step (.code (.finishNode handle value next)) before = .yielded (.code next) middle := rfl
      apply yielded_prefix_heap limit _ _ before middle after remaining fuel bounded initial heap fields actual one heap
      intro count bound good middleHeap retained tail
      exact ih checked middle after remaining count bound good middleHeap retained tail
  | finishEdge handle value next ih =>
      let middle : Checked width := {before with native := SourceRecursiveIntersectionThunks.finishEdge handle value before.native}
      have one : step (.code (.finishEdge handle value next)) before = .yielded (.code next) middle := rfl
      apply yielded_prefix_heap limit _ _ before middle after remaining fuel bounded initial heap fields actual one heap
      intro count bound good middleHeap retained tail
      exact ih checked middle after remaining count bound good middleHeap retained tail

/-- Literal node compilation retains every edge record's arity at any actual prefix endpoint. -/
theorem compileNode_prefix_heap (limit : Nat)
    (nodes : ∀ (request : NodeRequest Symbol Constraint) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (remaining : Control (Value Symbol Constraint)), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (.node request .pure)) before remaining after → Heap after.native.machine.heap)
    (edges : ∀ (request : EdgeRequest Symbol Constraint) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (remaining : Control (EdgeValue Symbol Constraint)), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (.edge request .pure)) before remaining after → Heap after.native.machine.heap)
    (request : NodeRequest Symbol Constraint) (before after : Checked width)
    (remaining : Control (Value Symbol Constraint)) (fuel : Nat) (bounded : fuel ≤ limit)
    (initial : Good before) (heap : Heap before.native.machine.heap)
    (actual : Trace fuel (.code (compileNode request)) before remaining after) : Heap after.native.machine.heap :=
  localWorks_prefix_heap limit nodes edges (compileNode request) (compileNode_localWorks request)
    before after remaining fuel bounded initial heap
    (SourceCurrentAllocatedNativeCodeFields.compileNode_fields before.operations request) actual

end MicroCFTA.SourcePruningEnumerationNativePrefixArity
