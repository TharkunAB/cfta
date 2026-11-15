import MicroCFTA.SourceCurrentAllocatedNativeOpenUniverseRowReplay
import MicroCFTA.SourceCurrentNativeEnterCommonOperand

/-!
# Physical readback of an actual open universe-row constructor

The same completed physical trace supplies the actual constructor inputs.
The literal prefix derives current heap facts from the original weak validity.
The original request, domain, fuel, allocated prefix and endpoint remain fixed.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback
open Cache InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceEqualityNativeDemandHeapPrimitives (WorkInputs)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceRecursiveIntersectionControl (repeatedValue)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Pair" => Value Symbol Guard × Value Symbol Guard
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat} {A : Type}

set_option autoImplicit false

/-- A literal prefix selects its checks from the same completed physical trace. -/
private theorem physical_prefix
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {prefixFuel total : Nat} {control reached : Control A}
    {before middle after : Checked width} {value : A}
    (stepsBeforeWork : Steps prefixFuel control before reached middle)
    (actual : Trace total control before (.code (.pure value)) after) :
    ∃ extra, total = prefixFuel + extra ∧
      Trace prefixFuel control before reached middle ∧
      Trace extra reached middle (.code (.pure value)) after := by
  induction stepsBeforeWork generalizing total with
  | refl => exact ⟨total, by omega, .refl _ _, actual⟩
  | cons start state next current final result count one tail ih =>
      cases actual with
      | refl => cases one
      | cons _ _ chosen returned _ _ remaining inputs step rest =>
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (step.symm.trans one)
          obtain ⟨extra, same, first, last⟩ := ih rest
          exact ⟨extra, by omega, .cons _ _ _ _ _ _ _ inputs one first, last⟩

/-- The actual edge work check supplies every original constructor argument. -/
private theorem edge_input_values
    (heap : InternedConstructorTemplates.State Symbol Guard) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (inputs : WorkInputs heap (makeEdge symbol guard values)) :
    Values heap values := by
  let check : {Result : Type} → Work Symbol Guard Result → Prop := fun {_} job =>
    match job with
    | .edge key identify _ => Values heap (identify ⟨0, key⟩).children
    | _ => True
  have nodeCheck : ∀ edges : List (EdgeValue Symbol Guard), check (makeNode edges) := by
    intro edges
    cases kept : canonicalEdges (surviving edges) with
    | nil => simp only [check, makeNode, kept]
    | cons first rest => simp only [check, makeNode, kept]
  have general : ∀ {Result : Type} (job : Work Symbol Guard Result), WorkInputs heap job → check job := by
    intro Result job checked
    cases checked with
    | pure value => exact True.intro
    | edge _ _ _ available => exact available
    | node edges _ => exact nodeCheck edges
    | union values _ =>
        cases members : distinctNodes (values.flatMap unionMembers) with
        | nil => simp only [check, makeUnion, members]
        | cons first rest =>
            cases rest with
            | nil => simp only [check, makeUnion, members]
            | cons second tail =>
                cases ordinary : ordinaryEdges (first :: second :: tail) with
                | none => simp only [check, makeUnion, members, ordinary]
                | some edges => simpa only [makeUnion, members, ordinary] using nodeCheck edges
  exact general (makeEdge symbol guard values) inputs

/-- The same physical body trace derives open row children and the full key without future heap premises. -/
theorem open_row_physical_readback_of_children
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (sourceName cutoffLeft cutoffRight : Nat)
    (request : EdgeRequest Symbol Guard) (before after : Checked width)
    (fuel traceFuel : Nat) (result : EdgeValue Symbol Guard)
    (physical : Physical before.native)
    (self : request.right = request.left) (sourceTop : request.left.entry.key.constraint = top)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (fieldOrigin : SourceEqualityOriginalFieldOrigins.Origin before.operations.constraints
      request.left.entry.key.constraint)
    (done : SourceEqualityNativeDemand.execute fuel (.edgeBody request .pure) before = .done result after)
    (actual : Trace traceFuel (.edgeBody request .pure) before (.code (.pure result)) after)
    (childrenReplay : ∀ stepsBefore childFuel, 0 < stepsBefore → stepsBefore + childFuel ≤ fuel → childFuel < fuel →
      ∀ pair ∈ request.left.children.zip request.right.children,
      ∀ (next : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
        (first last : Checked width) (value : Value Symbol Guard),
      Steps stepsBefore (.edgeBody request .pure) before
        (.code ((requestNode request.domain pair.1 pair.2).bind next)) first →
      SourceEqualityNativeDemand.execute childFuel (.code (requestNode request.domain pair.1 pair.2)) first =
        .done value last →
      value = input (replacement (.interned sourceName)
        (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))) pair.1) :
    ∃ (loaded combined : Allocated) (values : List (Value Symbol Guard)) (middle : Checked width) (count : Nat),
      SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints =
        .ok (some loaded) ∧
      (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
        request.left.children.length request.right.children.length before.operations).1 = .ok (.ready combined) ∧
      SourceEqualityConjoinAllocation.readback combined = top ∧
      count + 1 < fuel ∧
      SourceEqualityNativeDemandWalkExecution.Walk (fun pair => requestNode request.domain pair.1 pair.2)
        (request.left.children.zip request.right.children)
        {before with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
          request.left.children.length request.right.children.length before.operations).2} values middle count ∧
      values = request.left.children.map
        (input (replacement (.interned sourceName)
          (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight)))) ∧
      Physical middle.native ∧
      SourceRecursiveIntersectionKernel.Extension before.native.machine middle.native.machine ∧
      Values middle.native.machine.heap values ∧
      Trace (1 + count) (.edgeBody request .pure) before
        (.code (.work (makeEdge request.left.entry.key.symbol
          (SourceEqualityConjoinAllocation.readback combined) values) .pure)) middle ∧
      result.children = values ∧
      result.entry.key = ⟨request.left.entry.key.symbol, values.map Value.referenceOf, top⟩ ∧
      result = (run (makeEdge request.left.entry.key.symbol top values) middle.native.machine.heap).1 ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap :=
        (run (makeEdge request.left.entry.key.symbol top values) middle.native.machine.heap).2}} := by
  have observed := SourceCurrentAllocatedNativeOpenUniverseRowReplay.open_row_replay_and_returned_of_children
    (fun _ _ => True) (fun _ _ => True) sourceName cutoffLeft cutoffRight request before fuel self sourceTop valid fieldOrigin
    (by simp [SourceCurrentAllocatedNativeContextCache.Returned])
    (by simp [SourceCurrentAllocatedNativeContextCache.Returned])
    (by intros; constructor <;> simp [SourceCurrentAllocatedNativeContextCache.Returned]) childrenReplay
  obtain ⟨loaded, combined, values, middle, count, actualLoad, allocation, combinedTop, bounded, walked,
      ordered, sameResult, sameAfter⟩ := observed.2.2 result after done
  have arity : request.left.children.length = request.right.children.length := by rw [self]
  have rightLoad : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint
      before.operations.constraints = .ok (some loaded) := by rw [self]; exact actualLoad
  have one := body_ready request (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
    before arity loaded loaded combined actualLoad rightLoad allocation
  simp only [code_bind_pure] at one
  let next : List (Value Symbol Guard) → Code Symbol Guard (EdgeValue Symbol Guard) :=
    fun values => .work (makeEdge request.left.entry.key.symbol
      (SourceEqualityConjoinAllocation.readback combined) values) .pure
  have origin : Steps 1 (.edgeBody request .pure) before
      (.code ((SourceRecursiveIntersectionCode.walk (fun pair : Pair => requestNode request.domain pair.1 pair.2)
        (request.left.children.zip request.right.children)).bind next))
      {before with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
        request.left.children.length request.right.children.length before.operations).2} :=
    .cons _ _ _ _ _ _ _ one (.refl _ _)
  have walkedBound := walked.trace.bind _ _ _ _ _ next
  have throughWork : Steps (1 + count) (.edgeBody request .pure) before
      (.code (.work (makeEdge request.left.entry.key.symbol
        (SourceEqualityConjoinAllocation.readback combined) values) .pure)) middle :=
    origin.trans _ _ _ _ _ _ _ _ walkedBound
  obtain ⟨extra, _length, physicalPrefix, workTrace⟩ := physical_prefix throughWork actual
  have middleChecked := SourceCurrentNativeEnterCommonOperand.checked_trace_extension physicalPrefix physical
  have available : Values middle.native.machine.heap values := by
    cases extra with
    | zero => cases (steps_zero _ _ _ _ workTrace.steps).1
    | succ extra =>
        cases workTrace with
        | cons _ _ _ _ _ _ _ inputs _ _ =>
            exact edge_input_values middle.native.machine.heap request.left.entry.key.symbol
              (SourceEqualityConjoinAllocation.readback combined) values inputs
  have fields := InternedGuardedExecutionLists.makeEdge_fields request.left.entry.key.symbol top values
    middle.native.machine.heap middleChecked.1.machine.1.coherent middleChecked.1.machine.1.cached available
  have resultChildren : result.children = values := by rw [sameResult]; exact fields.2
  have resultKey : result.entry.key = ⟨request.left.entry.key.symbol, values.map Value.referenceOf, top⟩ := by
    rw [sameResult]
    exact fields.1
  exact ⟨loaded, combined, values, middle, count, actualLoad, allocation, combinedTop, bounded, walked,
    ordered, middleChecked.1, middleChecked.2, available, physicalPrefix, resultChildren, resultKey, sameResult, sameAfter⟩

end MicroCFTA.SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback


#check MicroCFTA.SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.open_row_physical_readback_of_children
#print axioms MicroCFTA.SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.open_row_physical_readback_of_children
