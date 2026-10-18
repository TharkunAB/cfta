import MicroCFTA.SourceCurrentOuterExecutionAncestry
import MicroCFTA.SourceCurrentPositionalOriginChain
import MicroCFTA.SourceCurrentOuterPositionalOrigins

/-!
# Indexed literal outer dispatch and positional anchors

The completed walk supplies the exact earlier calls, inherited descent,
node dispatch, and suffix. No execution graph or future link is supplied.
Positional origin composition uses the returned Parent children as the
actual dispatched values. It does not identify every worker dispatch with
a consecutive step of the conditional continuation-chain relation.
-/
namespace MicroCFTA.SourceCurrentOuterPositionalDispatch
open Cache InternedConstructorTemplates InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Reached Step)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "descend" => SourceCurrentAllocatedPartialGraph.descend
variable {width : Nat}

private theorem bind_done {A B : Type} (first : Outcome A width)
    (next : A → Caller width → Outcome B width) {result : B} {after : Caller width}
    (actual : first.bind next = .done result after) :
    ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value middle => exact ⟨value,middle,rfl,actual⟩
  | failed => cases actual

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Every present walk input has an exact indexed node call, literal prefix, and returned suffix. -/
theorem walk_indexed {fuel g s r e p h m c n budget : Nat} {combined : EqValue} {offset : Nat}
    {values results : List Node} {before after : Caller width}
    (actual : walk fuel g s r e p h m c n budget combined offset values before = .done results after)
    {slot : Nat} {value : Node} (input : values[slot]? = some value) :
    ∃ (start finish : Caller width) (childFuel : Nat) (returned : Node),
      fuel = childFuel + slot + 1 ∧ results[slot]? = some returned ∧
      walk fuel g s r e p h m c n budget combined offset (values.take slot) before =
        .done (results.take slot) start ∧
      nodeCall childFuel g s r e p h m c n budget
        ⟨(descend start combined (offset + slot)).1,value⟩
        (descend start combined (offset + slot)).2 = .done returned finish ∧
      walk childFuel g s r e p h m c n budget combined (offset + slot + 1)
        (values.drop (slot + 1)) finish = .done (results.drop (slot + 1)) after ∧
      Reached g s r e p h m c n budget (.walk fuel combined offset values before)
        (.node childFuel ⟨(descend start combined (offset + slot)).1,value⟩
          (descend start combined (offset + slot)).2) := by
  induction slot generalizing fuel offset values results before with
  | zero =>
    cases values with
    | nil => cases input
    | cons first rest =>
      cases fuel with
      | zero => simp only [walk] at actual; cases actual
      | succ fuel =>
        obtain ⟨returned,middle,called,later⟩ := bind_done _ _ (by simpa only [walk] using actual)
        obtain ⟨outputs,final,tail,done⟩ := bind_done _ _ later
        cases done
        cases Option.some.inj input
        refine ⟨before,middle,fuel,returned,by omega,rfl,(by simp only [List.take_zero,walk]),?_,?_,?_⟩
        · simpa only [Nat.add_zero] using called
        · simpa only [List.drop_succ_cons,List.drop_zero,Nat.add_zero] using tail
        · simpa only [Nat.add_zero] using (Reached.snoc (.refl _) Step.walk_head)
  | succ slot ih =>
    cases values with
    | nil => cases input
    | cons first rest =>
      cases fuel with
      | zero => simp only [walk] at actual; cases actual
      | succ fuel =>
        obtain ⟨returned,middle,called,later⟩ := bind_done _ _ (by simpa only [walk] using actual)
        obtain ⟨outputs,final,tail,done⟩ := bind_done _ _ later
        cases done
        obtain ⟨start,finish,childFuel,output,count,selected,earlier,child,suffix,reached⟩ :=
          ih tail input
        refine ⟨start,finish,childFuel,output,by omega,selected,?_,?_,?_,?_⟩
        · simp only [List.take_succ_cons,walk,called,Outcome.bind,earlier]
        · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using child
        · simpa only [List.drop_succ_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using suffix
        · have firstStep : Reached g s r e p h m c n budget
              (.walk (fuel + 1) combined offset (first :: rest) before)
              (.walk fuel combined (offset + 1) rest middle) :=
            Reached.snoc (Reached.refl _) (Step.walk_tail called)
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using firstStep.trans reached

/-- Actual Parent and walk calls derive the source anchor and strict mass decrease for a positive continuation. -/
theorem edge_dispatch {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
    {parented : Edge} {before afterParent afterWalk : Caller width} {combined : EqValue}
    {results : List Node} {rest : List Edge}
    (parent : edgeCall fuel g s r e p h m c n budget request before = .done parented afterParent)
    (good : SourceCurrentOuterPrefixInvariants.Good before)
    (ready : SourceCurrentOuterPrefixInvariants.EdgeReady before request)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap
      (fun guard : Guard => SourceMemoGate.plain guard = true) before.checked.native.machine.heap)
    (origins : SourceCurrentOuterPositionalOrigins.Origins before)
    (combinedAt : (SourceCurrentAllocatedInheritedPrefix.run parented.entry.key.constraint
      request.inherited afterParent.checked.operations).1 = .ok (some combined))
    (live : combined ≠ .contradiction)
    (actual : walk fuel g s r e p h m c n budget combined 0 parented.children
      (SourceCurrentAllocatedPartialGraph.prefixState afterParent parented request.inherited) =
        .done results afterWalk)
    {slot childIndex : Nat} {source value next : Node} {row : Edge} {records : List Record}
    (footprint : ∀ originals : List Record,
      SourceEqualityPhysicalPayload.own request.value.entry.key.constraint = .ok (some originals) →
        ∀ record ∈ originals, SourceCurrentClassPositionalFootprints.Unselected record slot childIndex)
    (input : request.value.children[slot]? = some source)
    (selected : parented.children[slot]? = some value)
    (member : row ∈ nodeEdges value)
    (positive : SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records))
    (nonempty : records ≠ []) (present : row.children[childIndex]? = some next) :
    SourceCurrentOuterPositionalOrigins.Origins afterParent ∧
    SourceCurrentActualRequiredRowOrigins.Link childIndex source value ∧
    SourceCurrentPositionalOriginChain.Below childIndex next source ∧
    InternedValueMass.value next < InternedValueMass.value source ∧
    ∃ (start finish : Caller width) (childFuel : Nat) (returned : Node),
      fuel = childFuel + slot + 1 ∧ results[slot]? = some returned ∧
      walk fuel g s r e p h m c n budget combined 0 (parented.children.take slot)
        (SourceCurrentAllocatedPartialGraph.prefixState afterParent parented request.inherited) =
          .done (results.take slot) start ∧
      nodeCall childFuel g s r e p h m c n budget
        ⟨(descend start combined slot).1,value⟩ (descend start combined slot).2 = .done returned finish ∧
      walk childFuel g s r e p h m c n budget combined (slot + 1)
        (parented.children.drop (slot + 1)) finish = .done (results.drop (slot + 1)) afterWalk ∧
      Reached g s r e p h m c n budget
        (.rows (fuel + 1) request.inherited (request.value :: rest) before)
        (.node childFuel ⟨(descend start combined slot).1,value⟩ (descend start combined slot).2) := by
  obtain ⟨retained,related⟩ := SourceCurrentOuterPositionalOrigins.edge_call parent good ready guards origins
  have link := related slot childIndex footprint source value input selected
  have below : SourceCurrentPositionalOriginChain.Below childIndex next source :=
    ⟨value,row,records,link,member,positive,nonempty,present⟩
  refine ⟨retained,link,below,SourceCurrentPositionalOriginChain.mass_lt below,?_⟩
  obtain ⟨start,finish,childFuel,returned,count,output,earlier,called,later,reached⟩ := walk_indexed actual selected
  refine ⟨start,finish,childFuel,returned,count,output,earlier,?_,?_,?_⟩
  · simpa only [Nat.zero_add] using called
  · simpa only [Nat.zero_add] using later
  · have parentStep : Reached g s r e p h m c n budget
        (.rows (fuel + 1) request.inherited (request.value :: rest) before)
        (.descendants fuel request.inherited parented afterParent) :=
      .snoc (.refl _) (.rows_edge parent)
    have prefixStep := parentStep.snoc (Step.descendants_children combinedAt)
    have walkStep := prefixStep.snoc (Step.children_walk live)
    simpa only [Nat.zero_add] using walkStep.trans reached

end MicroCFTA.SourceCurrentOuterPositionalDispatch
