import MicroCFTA.SourceCurrentOuterPositionalDispatch
import MicroCFTA.SourceCurrentOuterGuardHeapReturns

/-!
# Actual dispatches through untouched continuations

An actual Parent return retains a source anchor at an untouched next slot.
A positive row at the dispatched value has a smaller next anchor. The two
child indices can differ. Completed earlier siblings supply the dispatch;
the enclosing node and walk need not return. These results do not establish
that all recursive dispatches satisfy the untouched footprint condition.
-/
namespace MicroCFTA.SourceCurrentOuterUntouchedProgress
open Cache InternedConstructorTemplates InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
open SourceCurrentOuterPrefixInvariants (Good Inputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Record" => SourceEqualityClassOrder.Record
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
local notation "descend" => SourceCurrentAllocatedPartialGraph.descend
local notation "prefixState" => SourceCurrentAllocatedPartialGraph.prefixState
local notation "Origins" => SourceCurrentOuterPositionalOrigins.Origins
local notation "PlainHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
  (fun guard : Guard => SourceMemoGate.plain guard = true)

private theorem bind_done {A B : Type} (first : Outcome A width)
    (next : A → Caller width → Outcome B width) {result : B} {after : Caller width}
    (actual : first.bind next = .done result after) :
    ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value middle => exact ⟨value,middle,rfl,actual⟩
  | failed => cases actual

section Workers
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {width : Nat}

/-- Completed earlier siblings derive the exact indexed dispatch without an enclosing return. -/
theorem walk_prefix {fuel g s r e p h m c n budget offset slot : Nat}
    {combined : EqValue} {values outputs : List Node} {value : Node} {before start : Caller width}
    (earlierCalls : walk (fuel + slot + 1) g s r e p h m c n budget combined offset
      (values.take slot) before = .done outputs start)
    (selected : values[slot]? = some value) :
    Reached g s r e p h m c n budget
      (.walk (fuel + slot + 1) combined offset values before)
      (.node fuel ⟨(descend start combined (offset + slot)).1,value⟩
        (descend start combined (offset + slot)).2) := by
  induction slot generalizing offset values outputs before with
  | zero =>
    have same : before = start := by
      simpa only [List.take_zero,walk,Outcome.done.injEq] using (congrArg Outcome.state earlierCalls)
    subst start
    cases values with
    | nil => cases selected
    | cons first rest =>
      cases Option.some.inj selected
      simpa only [Nat.add_zero] using (Reached.snoc (Reached.refl _) Step.walk_head)
  | succ slot ih =>
    cases values with
    | nil => cases selected
    | cons first rest =>
      have count : fuel + (slot + 1) + 1 = (fuel + slot + 1) + 1 := by omega
      obtain ⟨returned,middle,called,later⟩ := bind_done _ _
        (by simpa only [count,List.take_succ_cons,walk] using earlierCalls)
      obtain ⟨tail,final,remaining,done⟩ := bind_done _ _ later
      cases done
      have child := ih remaining (by simpa only [List.getElem?_cons_succ] using selected)
      have firstStep : Reached g s r e p h m c n budget
          (.walk ((fuel + slot + 1) + 1) combined offset (first :: rest) before)
          (.walk (fuel + slot + 1) combined (offset + 1) rest middle) :=
        .snoc (.refl _) (.walk_tail called)
      simpa only [count,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using firstStep.trans child

/-- An actual child dispatch yields strict anchor descent at any untouched next child index. -/
theorem dispatch {g s r e p h m c n budget fuel slot nextSlot : Nat}
    {entry : Phase width} {inherited combined : EqValue} {original parented row : Edge}
    {rest : List Edge} {before afterParent start : Caller width}
    {earlier : List Node} {anchor value nextAnchor : Node} {records : List Record}
    (good : Good (caller entry)) (inputs : Inputs entry)
    (guards : PlainHeap (caller entry).checked.native.machine.heap)
    (origins : Origins (caller entry))
    (past : Reached g s r e p h m c n budget entry
      (.rows (fuel + slot + 2) inherited (original :: rest) before))
    (parent : edgeCall (fuel + slot + 1) g s r e p h m c n budget
      ⟨inherited,original⟩ before = .done parented afterParent)
    (combinedAt : (SourceCurrentAllocatedInheritedPrefix.run parented.entry.key.constraint inherited
      afterParent.checked.operations).1 = .ok (some combined))
    (live : combined ≠ .contradiction)
    (earlierCalls : walk (fuel + slot + 1) g s r e p h m c n budget combined 0
      (parented.children.take slot) (prefixState afterParent parented inherited) = .done earlier start)
    (footprint : ∀ originals : List Record,
      SourceEqualityPhysicalPayload.own original.entry.key.constraint = .ok (some originals) →
        ∀ record ∈ originals, SourceCurrentClassPositionalFootprints.Unselected record slot nextSlot)
    (source : original.children[slot]? = some anchor)
    (selected : parented.children[slot]? = some value)
    (member : row ∈ nodeEdges value)
    (positive : SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records))
    (nonempty : records ≠ []) (present : row.children[nextSlot]? = some nextAnchor) :
    Reached g s r e p h m c n budget entry
      (.node fuel ⟨(descend start combined slot).1,value⟩ (descend start combined slot).2) ∧
    Origins afterParent ∧
    SourceCurrentActualRequiredRowOrigins.Link nextSlot anchor value ∧
    SourceCurrentPositionalOriginChain.Below nextSlot nextAnchor anchor ∧
    InternedValueMass.value nextAnchor < InternedValueMass.value anchor := by
  have current := SourceCurrentOuterPrefixInvariants.reached past good inputs
  have currentGuards := SourceCurrentOuterGuardHeapReturns.reached _ past good inputs guards
  have currentOrigins := SourceCurrentOuterPositionalOrigins.reached past good inputs origins
  obtain ⟨retained,related⟩ := SourceCurrentOuterPositionalOrigins.edge_call parent current.1
    ⟨current.2.1,current.2.2 _ List.mem_cons_self⟩ currentGuards currentOrigins
  have link := related slot nextSlot footprint anchor value source selected
  have below : SourceCurrentPositionalOriginChain.Below nextSlot nextAnchor anchor :=
    ⟨value,row,records,link,member,positive,nonempty,present⟩
  refine ⟨?_,retained,link,below,SourceCurrentPositionalOriginChain.mass_lt below⟩
  have rowStep : Reached g s r e p h m c n budget
      (.rows (fuel + slot + 2) inherited (original :: rest) before)
      (.descendants (fuel + slot + 1) inherited parented afterParent) :=
    .snoc (.refl _) (.rows_edge parent)
  have childStep := (past.trans rowStep).snoc (Step.descendants_children combinedAt)
  have walkStep := childStep.snoc (Step.children_walk live)
  have entered := walk_prefix earlierCalls selected
  exact walkStep.trans (by simpa only [Nat.zero_add] using entered)

end Workers

/-- A finite anchor chain consumes mass even when its child indices change at every step. -/
theorem budget (anchors : Nat → Node) (indices : Nat → Nat) (count : Nat)
    (steps : ∀ index, index < count →
      SourceCurrentPositionalOriginChain.Below (indices index) (anchors (index + 1)) (anchors index)) :
    InternedValueMass.value (anchors count) + count ≤ InternedValueMass.value (anchors 0) := by
  induction count with
  | zero => omega
  | succ count ih =>
    have earlier := ih (fun index inside => steps index (by omega))
    have last := SourceCurrentPositionalOriginChain.mass_lt (steps count (by omega))
    omega

end MicroCFTA.SourceCurrentOuterUntouchedProgress
