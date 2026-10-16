import MicroCFTA.SourceCurrentAllocatedNativeNodeBranches
import MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning
import MicroCFTA.SourceEqualityNativeDemandHeapPrimitives

/-!
# Contextual union meaning through actual checked member traces

Each member certificate concerns its actual child request. The proof composes
those traces in source order and executes the final union constructor.
The original input model stays fixed across the returned heap effects.
The recursive proof must still derive each child certificate.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeUnionMeaning
open Language Cache InternedBinderProtocol InternedConstructorTemplates InternedProbeProvenance
open InternedNestedFacts SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {width : Nat}

private theorem walk_map {A B C : Type} (convert : A → B) (call : B → Code Symbol Guard C) (inputs : List A) :
    SourceRecursiveIntersectionCode.walk call (inputs.map convert) =
      SourceRecursiveIntersectionCode.walk (fun input => call (convert input)) inputs := by
  induction inputs with
  | nil => rfl
  | cons first rest ih => simp only [List.map, SourceRecursiveIntersectionCode.walk, ih]

private theorem laws_map {A B C : Type} {R : B → C → Prop} (convert : A → B)
    (inputs : List A) (outputs : List C) (laws : All₂ R (inputs.map convert) outputs) :
    All₂ (fun input output => R (convert input) output) inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases laws; exact .nil
  | cons first rest ih =>
      cases laws with
      | cons law tail => exact .cons law (ih _ tail)

/-- The selected union branch derives its language and exact returned state from its member calls. -/
theorem union_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (sourceFacts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference) (other : Value Symbol Guard)
    (side : Bool) (available : Available source (.union entry members depth free))
    (before middle : SourceEqualityNativeDemand.State width) (values : List (Value Symbol Guard)) (fuel : Nat)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap)
    (selected : SourceRecursiveIntersectionControl.decision domain.key
      (if side then .union entry members depth free else other)
      (if side then other else .union entry members depth free) =
      if side then .leftUnion else .rightUnion)
    (walk : SourceCurrentAllocatedNativeEdgeMeaning.Walk (view source holds) model ranked holds domain
      (members.map fun member => if side then (member, other) else (other, member)) before values middle fuel) :
    let request : NodeRequest Symbol Guard := ⟨domain,
      if side then .union entry members depth free else other,
      if side then other else .union entry members depth free⟩
    let built := run (makeUnion values) middle.native.machine.heap
    let after : SourceEqualityNativeDemand.State width :=
      {middle with native := advance middle.native {middle.native.machine with heap := built.2}}
    execute (fuel + 2) (.code (compileNode request)) before = .done built.1 after ∧
      NodeLaw (view source holds) model ranked holds request built.1 ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap built.1 := by
  have effects := walk.effects ready
  have constructor := SourceEqualityNativeDemandHeapPrimitives.union values middle.native.machine.heap effects.1.ready effects.2.1
  have childLaws := laws_map (fun member => if side then (member, other) else (other, member)) members values effects.2.2
  have law : NodeLaw (view source holds) model ranked holds
      ⟨domain, if side then .union entry members depth free else other,
        if side then other else .union entry members depth free⟩
      (run (makeUnion values) middle.native.machine.heap).1 := by
    cases side
    · exact SourceCurrentAllocatedNativeNodeBranches.right_union_law source sourceFacts holds model ranked domain entry members
        depth free other available middle.native.machine.heap effects.1.ready.semantic.1.normal.facts values effects.2.1 childLaws
    · exact SourceCurrentAllocatedNativeNodeBranches.left_union_law source sourceFacts holds model ranked domain entry members
        depth free other available middle.native.machine.heap effects.1.ready.semantic.1.normal.facts values effects.2.1 childLaws
  have childTrace := walk.actual.trace
  rw [walk_map] at childTrace
  have memberTrace := childTrace.bind _ _ _ _ _ (fun values => .work (makeUnion values) .pure)
  have actual : compileNode
      ⟨domain, if side then .union entry members depth free else other,
        if side then other else .union entry members depth free⟩ =
      (SourceRecursiveIntersectionCode.walk (fun member =>
        let pair := if side then (member, other) else (other, member)
        requestNode domain pair.1 pair.2) members).bind (fun values => .work (makeUnion values) .pure) := by
    cases side <;> simp_all [compileNode]
  have trace := memberTrace.trans _ _ _ _ _ _ _ _
    (Steps.cons _ _ _ _ _ _ 0 rfl (Steps.refl _ _))
  exact ⟨by rw [actual]; exact trace_done (fuel + 1) _ before _ _ trace,
    law, effects.1.trans constructor.1, constructor.2⟩

end MicroCFTA.SourceCurrentAllocatedNativeUnionMeaning
