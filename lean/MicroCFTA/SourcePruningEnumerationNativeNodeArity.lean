import MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback
import MicroCFTA.SourcePruningEnumerationNativeArityPrimitives

/-!
# Arity through actual native node compilation

Each child call retains the arity of the heap at its actual endpoint.
The walk uses only the subcalls recorded by the completed rich trace.
The node compiler creates no edge outside those child calls.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeQueryArity
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedNativeSemanticTraceReadback (Walk)
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {A B : Type} {width : Nat}
section Walk
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]

/-- An actual ordered walk preserves arity from its bounded actual child calls. -/
theorem walk_heap (limit : Nat) (call : A → Code Symbol Constraint B)
    (calls : ∀ (input : A) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (value : B), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (call input)) before (.code (.pure value)) after →
        Heap after.native.machine.heap)
    (fields : ∀ (input : A) (state : Checked width), Fields (.code (call input)) state)
    (inputs : List A) (values : List B) (before after : Checked width) (fuel : Nat)
    (bounded : fuel ≤ limit) (initial : Good before) (heap : Heap before.native.machine.heap)
    (actual : Walk call inputs before values after fuel) : Heap after.native.machine.heap := by
  revert bounded initial heap
  induction actual with
  | nil state => intro _ _ heap; exact heap
  | cons first rest before middle after value values firstFuel restFuel called tail ih =>
      intro bounded initial heap
      have firstHeap := calls first firstFuel (by omega) before middle value initial heap called
      have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects called initial (fields first before)
      exact ih (by omega) reached.1 firstHeap

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

private theorem yielded_heap (limit : Nat) (control next : Control A)
    (before middle after : Checked width) (value : A) (fuel : Nat)
    (bounded : fuel ≤ limit) (initial : Good before) (fields : Fields control before)
    (actual : Trace fuel control before (.code (.pure value)) after)
    (one : step control before = .yielded next middle) (heap : Heap middle.native.machine.heap)
    (rest : ∀ count, count ≤ limit → Good middle → Heap middle.native.machine.heap → Fields next middle →
      Trace count next middle (.code (.pure value)) after → Heap after.native.machine.heap) :
    Heap after.native.machine.heap := by
  obtain ⟨count, total, remaining⟩ :=
    SourceCurrentAllocatedNativeSemanticTraceReadback.after_step fuel control next before middle after value actual one
  have checked := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control before initial
    (SourceCurrentAllocatedNativeSemanticTraceReadback.current_inputs actual) fields
  rw [one] at checked
  exact rest count (by omega) checked.1 heap checked.2.2.2.2.2 remaining

private theorem localWorks_heap (limit : Nat)
    (nodes : ∀ (request : NodeRequest Symbol Constraint) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (value : Value Symbol Constraint), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (.node request .pure)) before (.code (.pure value)) after →
        Heap after.native.machine.heap)
    (edges : ∀ (request : EdgeRequest Symbol Constraint) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (value : EdgeValue Symbol Constraint), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (.edge request .pure)) before (.code (.pure value)) after →
        Heap after.native.machine.heap)
    (code : Code Symbol Constraint A) (checked : LocalWorks code)
    (before after : Checked width) (value : A) (fuel : Nat) (bounded : fuel ≤ limit)
    (initial : Good before) (heap : Heap before.native.machine.heap) (fields : Fields (.code code) before)
    (actual : Trace fuel (.code code) before (.code (.pure value)) after) : Heap after.native.machine.heap := by
  induction code generalizing before after value fuel with
  | pure result =>
      obtain ⟨_, _, same⟩ := pure_trace fuel result value before after actual.steps
      simpa only [same] using heap
  | fail failure =>
      cases actual with
      | cons control state next middle final result count inputs one tail => cases one
  | work job next ih =>
      let result := run job before.native.machine.heap
      let middle : Checked width := {before with native := advance before.native {before.native.machine with heap := result.2}}
      have one : step (.code (.work job next)) before = .yielded (.code (next result.1)) middle := rfl
      apply yielded_heap limit _ _ before middle after value fuel bounded initial fields actual one
        (SourcePruningEnumerationNativeArityPrimitives.work_heap job before.native.machine.heap heap (checked.1 _))
      intro count bound good middleHeap retained tail
      exact ih result.1 (checked.2 result.1) middle after value count bound good
        middleHeap retained tail
  | enter domain left right first second next ih =>
      let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains domain.key left right first second
      let middle : Checked width := {before with native := advance before.native {before.native.machine with domains := entered.2}}
      have one : step (.code (.enter domain left right first second next)) before =
          .yielded (.code (next entered.1)) middle := rfl
      apply yielded_heap limit _ _ before middle after value fuel bounded initial fields actual one heap
      intro count bound good middleHeap retained tail
      exact ih entered.1 (checked entered.1) middle after value count bound good middleHeap retained tail
  | read name next ih =>
      let found := SourcePreparedSharedRows.read before.native.machine.heap name
      have one : step (.code (.read name next)) before = .yielded (.code (next found)) before := rfl
      apply yielded_heap limit _ _ before before after value fuel bounded initial fields actual one heap
      intro count bound good middleHeap retained tail
      exact ih found (checked found) before after value count bound good middleHeap retained tail
  | optionalBinder key body next ih =>
      have inputs := SourceCurrentAllocatedNativeSemanticTraceReadback.current_inputs actual
      have retained := SourcePruningEnumerationNativeArityPrimitives.optionalBinder_heap key body
        before.native.machine.heap initial.native.machine.1 heap inputs
      cases built : SourceRecursiveIntersectionMaybeMu.maybeMu key body before.native.machine.heap with
      | done result finalHeap =>
          let middle : Checked width := {before with native := advance before.native {before.native.machine with heap := finalHeap}}
          have one : step (.code (.optionalBinder key body next)) before =
              .yielded (.code (next result)) middle := by
            simp only [step, SourceRecursiveIntersectionNative.step, built, lift, middle]
          have middleHeap : Heap middle.native.machine.heap := by
            change Heap finalHeap
            simpa only [built, InternedNestedConstruction.Outcome.state] using retained
          apply yielded_heap limit _ _ before middle after value fuel bounded initial fields actual one middleHeap
          intro count bound good reachedHeap later tail
          exact ih result (checked result) middle after value count bound good reachedHeap later tail
      | pending pending finalHeap =>
          cases actual with
          | cons control state rest middle final result count inputs one tail =>
              simp only [step, SourceRecursiveIntersectionNative.step, built, lift] at one
              cases one
  | node request next ih =>
      obtain ⟨inner, outer, result, middle, count, first, rest⟩ :=
        SourceCurrentAllocatedNativeSemanticTraceReadback.bind_inverse fuel (.code (.node request .pure))
          next before after value actual
      have middleHeap := nodes request inner (by omega) before middle result initial heap first
      have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects (first.bind next) initial fields
      exact ih result (checked result) middle after value outer (by omega) reached.1 middleHeap reached.2.2.2.2 rest
  | edge request next ih =>
      obtain ⟨inner, outer, result, middle, count, first, rest⟩ :=
        SourceCurrentAllocatedNativeSemanticTraceReadback.bind_inverse fuel (.code (.edge request .pure))
          next before after value actual
      have middleHeap := edges request inner (by omega) before middle result initial heap first
      have reached := SourceCurrentAllocatedNativeSemanticTraceReadback.effects (first.bind next) initial fields
      exact ih result (checked result) middle after value outer (by omega) reached.1 middleHeap reached.2.2.2.2 rest
  | finishNode handle result next ih =>
      let middle : Checked width := {before with native := SourceRecursiveIntersectionThunks.finishNode handle result before.native}
      have one : step (.code (.finishNode handle result next)) before = .yielded (.code next) middle := rfl
      apply yielded_heap limit _ _ before middle after value fuel bounded initial fields actual one heap
      intro count bound good middleHeap retained tail
      exact ih checked middle after value count bound good middleHeap retained tail
  | finishEdge handle result next ih =>
      let middle : Checked width := {before with native := SourceRecursiveIntersectionThunks.finishEdge handle result before.native}
      have one : step (.code (.finishEdge handle result next)) before = .yielded (.code next) middle := rfl
      apply yielded_heap limit _ _ before middle after value fuel bounded initial fields actual one heap
      intro count bound good middleHeap retained tail
      exact ih checked middle after value count bound good middleHeap retained tail

/-- Literal node compilation preserves arity from its bounded actual node and edge requests. -/
theorem compileNode_heap (limit : Nat)
    (nodes : ∀ (request : NodeRequest Symbol Constraint) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (value : Value Symbol Constraint), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (.node request .pure)) before (.code (.pure value)) after →
        Heap after.native.machine.heap)
    (edges : ∀ (request : EdgeRequest Symbol Constraint) (fuel : Nat), fuel ≤ limit →
      ∀ (before after : Checked width) (value : EdgeValue Symbol Constraint), Good before →
        Heap before.native.machine.heap →
        Trace fuel (.code (.edge request .pure)) before (.code (.pure value)) after →
        Heap after.native.machine.heap)
    (request : NodeRequest Symbol Constraint) (before after : Checked width)
    (value : Value Symbol Constraint) (fuel : Nat) (bounded : fuel ≤ limit)
    (initial : Good before) (heap : Heap before.native.machine.heap)
    (actual : Trace fuel (.code (compileNode request)) before (.code (.pure value)) after) :
    Heap after.native.machine.heap :=
  localWorks_heap limit nodes edges (compileNode request) (compileNode_localWorks request)
    before after value fuel bounded initial heap
    (SourceCurrentAllocatedNativeCodeFields.compileNode_fields before.operations request) actual

end MicroCFTA.SourcePruningEnumerationNativeQueryArity
