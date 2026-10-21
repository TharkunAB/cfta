import MicroCFTA.SourceCurrentOuterClosedInputs

/-!
# Reference and absent-node faults in actual outer execution

Each failure supplies its exact reached cut and unchanged failed caller.
Closed phase inputs exclude references. Valid node links exclude absence.
-/
namespace MicroCFTA.SourceCurrentOuterReferenceAbsent
open Cache InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached NodeValid)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "caller" => SourceCurrentOuterActiveAncestry.caller

private theorem not_absent (request : NodeRequest) (before : Caller width) (valid : NodeValid before) :
    (beginNode request before).2.1 ≠ .absent := by
  cases published : before.nodeResults.table request.key with
  | none => simp only [beginNode,FlatMemoThunk.lookupOrInsert,published,FlatMemoThunk.demand,put]; simp
  | some handle =>
    obtain ⟨⟨original,status⟩,present,_key⟩ := valid.linked request.key handle published
    cases status <;> simp only [beginNode,FlatMemoThunk.lookupOrInsert,published,FlatMemoThunk.demand,present] <;> simp

private theorem erase_failed {actual : Outcome A width}
    (failed : actual.bind (fun _ after => .done () after) = .failed fault after) : actual = .failed fault after := by
  cases actual <;> simp_all [Outcome.bind]

private theorem bind_failed (first : Outcome A width) (next : A → Caller width → Outcome B width)
    (failed : first.bind next = .failed fault after) :
    first = .failed fault after ∨ ∃ value middle, first = .done value middle ∧ next value middle = .failed fault after := by
  cases first with
  | failed => simp only [Outcome.bind] at failed; cases failed; exact Or.inl rfl
  | done value middle => exact Or.inr ⟨value,middle,rfl,failed⟩

private def diagnostic (kind : Bool) (name : InternedBinderProtocol.Reference) (handle : Nat) : Fault width :=
  if kind then .unexpectedReference name else .nodeMemo handle .absent

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

private def Cut (g s r e p h m c n budget : Nat) (entry : Phase width)
    (kind : Bool) (name : InternedBinderProtocol.Reference) (handle : Nat) (after : Caller width) : Prop :=
  if kind then ∃ fuel inherited, Reached g s r e p h m c n budget entry (.body fuel ⟨inherited,.reference name⟩ after)
  else ∃ fuel request before, Reached g s r e p h m c n budget entry (.node fuel request before) ∧
    beginNode request before = (handle,.absent,after)

private theorem cut_step (first : Step g s r e p h m c n budget entry middle)
    (last : Cut g s r e p h m c n budget middle kind name handle after) :
    Cut g s r e p h m c n budget entry kind name handle after := by
  cases kind <;> dsimp only [Cut] at last ⊢
  · obtain ⟨fuel,request,before,later,started⟩ := last
    exact ⟨fuel,request,before,(Reached.snoc (.refl _) first).trans later,started⟩
  · obtain ⟨fuel,inherited,later⟩ := last
    exact ⟨fuel,inherited,(Reached.snoc (.refl _) first).trans later⟩

private theorem edge_safe (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
    (before : Caller width) (kind : Bool) (name : InternedBinderProtocol.Reference) (handle : Nat) (after : Caller width) :
    edgeCall fuel g s r e p h m c n budget request before ≠ .failed (diagnostic kind name handle) after := by
  intro failed
  rcases started : beginEdge request before with ⟨chosen,action,running⟩
  cases action with
  | ready result | busy | absent => cases kind <;> simp only [edgeCall,started,diagnostic] at failed <;> cases failed
  | evaluate original =>
    simp only [edgeCall,started,edgeBody] at failed
    split at failed <;> simp only [Outcome.bind] at failed <;> cases kind <;> simp only [diagnostic] at failed <;> cases failed

private def NodeFailureAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget request (before : Caller width) kind name handle after,
  nodeCall fuel g s r e p h m c n budget request before = .failed (diagnostic kind name handle) after →
  Cut g s r e p h m c n budget (.node fuel request before) kind name handle after
private def BodyFailureAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget request (before : Caller width) kind name handle after,
  nodeBody fuel g s r e p h m c n budget request before = .failed (diagnostic kind name handle) after →
  Cut g s r e p h m c n budget (.body fuel request before) kind name handle after
private def RowsFailureAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget inherited values (before : Caller width) kind name handle after,
  rows fuel g s r e p h m c n budget inherited values before = .failed (diagnostic kind name handle) after →
  Cut g s r e p h m c n budget (.rows fuel inherited values before) kind name handle after
private def DescendantsFailureAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget inherited value (before : Caller width) kind name handle after,
  descendants fuel g s r e p h m c n budget inherited value before = .failed (diagnostic kind name handle) after →
  Cut g s r e p h m c n budget (.descendants fuel inherited value before) kind name handle after
private def ChildrenFailureAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget combined values (before : Caller width) kind name handle after,
  children fuel g s r e p h m c n budget combined values before = .failed (diagnostic kind name handle) after →
  Cut g s r e p h m c n budget (.children fuel combined values before) kind name handle after
private def WalkFailureAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget combined index values (before : Caller width) kind name handle after,
  walk fuel g s r e p h m c n budget combined index values before = .failed (diagnostic kind name handle) after →
  Cut g s r e p h m c n budget (.walk fuel combined index values before) kind name handle after

private theorem all_failures (fuel : Nat) :
    NodeFailureAt (width := width) fuel ∧ BodyFailureAt (width := width) fuel ∧ RowsFailureAt (width := width) fuel ∧
      DescendantsFailureAt (width := width) fuel ∧ ChildrenFailureAt (width := width) fuel ∧ WalkFailureAt (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    have walkAt : WalkFailureAt (width := width) fuel := by
      intro g s r e p h m c n budget combined index values before kind name handle after failed
      cases values with
      | nil => simp only [walk] at failed; cases failed
      | cons value rest =>
        cases fuel with
        | zero => simp only [walk] at failed; cases kind <;> simp only [diagnostic] at failed <;> cases failed
        | succ fuel =>
          simp only [walk] at failed
          rcases bind_failed _ _ failed with headFailed | ⟨head,middle,headDone,later⟩
          · exact cut_step .walk_head ((ih fuel (Nat.lt_succ_self _)).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ headFailed)
          · rcases bind_failed _ _ later with tailFailed | ⟨outputs,final,tailDone,impossible⟩
            · exact cut_step (.walk_tail headDone)
                ((ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  _ _ tailFailed)
            · cases impossible
    have childrenAt : ChildrenFailureAt (width := width) fuel := by
      intro g s r e p h m c n budget combined values before kind name handle after failed
      cases combined with
      | contradiction => simp only [children] at failed; cases failed
      | live identity records =>
        simp only [children] at failed
        exact cut_step (.children_walk (by intro impossible; cases impossible))
          (walkAt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ failed)
    have descendantsAt : DescendantsFailureAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited value before kind name handle after failed
      simp only [descendants] at failed
      split at failed
      · cases kind <;> simp only [diagnostic] at failed <;> cases failed
      · cases kind <;> simp only [diagnostic] at failed <;> cases failed
      · rename_i combined observed
        rcases bind_failed _ _ failed with childFailed | ⟨outputs,middle,childDone,impossible⟩
        · have observed : (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations).1 =
              .ok (some combined) := observed
          have prefixEq : advance before
              (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked
                ⟨before.checked.native.machine.heap,
                  (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations).2⟩)
              before.fourth before.merge = SourceCurrentAllocatedPartialGraph.prefixState before value inherited := rfl
          rw [prefixEq] at childFailed
          exact cut_step (.descendants_children observed) (childrenAt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ childFailed)
        · cases impossible
    have rowsAt : RowsFailureAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited values before kind name handle after failed
      cases values with
      | nil => simp only [rows] at failed; cases failed
      | cons original rest =>
        cases fuel with
        | zero => simp only [rows] at failed; cases kind <;> simp only [diagnostic] at failed <;> cases failed
        | succ fuel =>
          simp only [rows] at failed
          rcases bind_failed _ _ failed with edgeFailed | ⟨narrowed,middle,edgeDone,later⟩
          · exact False.elim (edge_safe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ edgeFailed)
          · rcases bind_failed _ _ later with childFailed | ⟨result,returned,childDone,suffix⟩
            · exact cut_step (.rows_edge edgeDone)
                ((ih fuel (Nat.lt_succ_self _)).2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  _ _ childFailed)
            · rcases bind_failed _ _ suffix with tailFailed | ⟨outputs,final,tailDone,impossible⟩
              · exact cut_step (.rows_tail edgeDone childDone)
                  ((ih fuel (Nat.lt_succ_self _)).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tailFailed)
              · cases impossible
    have bodyAt : BodyFailureAt (width := width) fuel := by
      intro g s r e p h m c n budget request before kind name handle after failed
      rcases request with ⟨inherited,value⟩
      cases value with
      | empty | union => simp only [nodeBody] at failed; cases failed
      | reference actualName =>
        cases kind <;> simp only [nodeBody, diagnostic] at failed
        · cases failed
        · cases failed; exact ⟨fuel,inherited,.refl _⟩
      | mu entry body depth ordinary =>
        simp only [nodeBody] at failed
        split at failed <;> cases kind <;> simp only [diagnostic] at failed <;> cases failed
      | node entry original depth free =>
        cases fuel with
        | zero => simp only [nodeBody] at failed; cases kind <;> simp only [diagnostic] at failed <;> cases failed
        | succ fuel =>
          simp only [nodeBody] at failed
          rcases bind_failed _ _ failed with rowsFailed | ⟨outputs,middle,rowsDone,impossible⟩
          · exact cut_step (.body_rows rfl)
              ((ih fuel (Nat.lt_succ_self _)).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rowsFailed)
          · cases impossible
    have nodeAt : NodeFailureAt (width := width) fuel := by
      intro g s r e p h m c n budget request before kind name handle after failed
      rcases started : beginNode request before with ⟨chosen,action,running⟩
      cases action with
      | ready result => simp only [nodeCall,started] at failed; cases failed
      | busy => cases kind <;> simp only [nodeCall,started,diagnostic] at failed <;> cases failed
      | absent =>
        cases kind <;> simp only [nodeCall,started,diagnostic] at failed
        · cases failed; exact ⟨fuel,request,before,.refl _,started⟩
        · cases failed
      | evaluate original =>
        simp only [nodeCall,started] at failed
        rcases bind_failed _ _ failed with bodyFailed | ⟨result,middle,bodyDone,impossible⟩
        · exact cut_step (.node_evaluate started)
            (bodyAt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bodyFailed)
        · cases impossible
    exact ⟨nodeAt,bodyAt,rowsAt,descendantsAt,childrenAt,walkAt⟩

private theorem failure_cut {g s r e p h m c n budget : Nat} {first : Phase width}
    {kind : Bool} {name : InternedBinderProtocol.Reference} {handle : Nat} {after : Caller width}
    (failed : SourceCurrentOuterActiveAncestry.run g s r e p h m c n budget first = .failed (diagnostic kind name handle) after) :
    Cut g s r e p h m c n budget first kind name handle after := by
  cases first with
  | node fuel request before => exact (all_failures fuel).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed failed)
  | body fuel request before => exact (all_failures fuel).2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed failed)
  | rows fuel inherited values before => exact (all_failures fuel).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed failed)
  | descendants fuel inherited value before => exact (all_failures fuel).2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed failed)
  | children fuel combined values before => exact (all_failures fuel).2.2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed failed)
  | walk fuel combined index values before => exact (all_failures fuel).2.2.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed failed)

variable {bits : Nat}

/-- Closed initial inputs and valid node links exclude both literal diagnostics at their actual reached cuts. -/
theorem no_reference_or_node_absent
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s r e p h m c n budget : Nat} {first : Phase (bits + 2)}
    {inventory : Inventory} {memos : Memos} (seed : List Guard × Profile)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      (caller first).checked.native.machine.heap)
    (inputs : SourceCurrentOuterPrefixInvariants.Inputs first)
    (room : Room bits (SourceCurrentOuterInitialPrefix.forecast budget first seed).2)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal (caller first).checked.native.machine.heap)
    (supported : SourceCurrentNativeRequestPositivePositions.Support
      (caller first).checked.native.machine.heap (caller first).checked.native)
    (causal : SourceCurrentNativeMuPublication.History empty (caller first).checked.native.machine.heap)
    (merged : SourceCurrentConstrainedCapMemoMerge.Stored
      (fun guard : Guard => SourceMemoGate.plain guard = true) (caller first).merge)
    (positiveMemo : SourceCurrentMergePositivePosition.Support (caller first).merge)
    (origins : SourceCurrentResourceParentWriters.Origins formulas solver (caller first))
    (stored : SourceCurrentOuterClosedInputs.NodeStored (caller first))
    (closed : SourceCurrentOuterClosedInputs.InputsClosed first)
    (name : InternedBinderProtocol.Reference) (handle : Nat) (after : Caller (bits + 2)) :
    (SourceCurrentOuterActiveAncestry.run g s r e p h m c n budget first ≠
      .failed (.unexpectedReference name) after) ∧
    (SourceCurrentOuterActiveAncestry.run g s r e p h m c n budget first ≠
      .failed (.nodeMemo handle .absent) after) := by
  constructor
  · intro failed
    obtain ⟨fuel,inherited,actual⟩ := failure_cut (kind := true) (name := name) (handle := handle) failed
    have closedAt := (SourceCurrentOuterClosedInputs.reached formulas solver seed actual initial frame fits known inputs room
      normal supported causal merged positiveMemo origins stored closed).2
    change [name] = [] at closedAt
    cases closedAt
  · intro failed
    obtain ⟨fuel,request,before,actual,started⟩ := failure_cut (kind := false) (name := name) (handle := handle) failed
    have valid : NodeValid (caller first) :=
      FlatMemoThunk.Valid.keyMap _ _ _ _ initial.sound.valid.nodes (fun _ _ linked => linked.2)
    exact not_absent request before (actual.valid valid) (congrArg (fun result => result.2.1) started)

end MicroCFTA.SourceCurrentOuterReferenceAbsent

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentOuterReferenceAbsent.no_reference_or_node_absent
#print MicroCFTA.SourceCurrentOuterReferenceAbsent.no_reference_or_node_absent
#print axioms MicroCFTA.SourceCurrentOuterReferenceAbsent.no_reference_or_node_absent
