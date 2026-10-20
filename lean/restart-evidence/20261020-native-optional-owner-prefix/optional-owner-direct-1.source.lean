import MicroCFTA.SourceCurrentNativeOptionalOwnerReceipt
import MicroCFTA.SourceCurrentNativeQueryOptionalPrefix
import MicroCFTA.SourceCurrentNativeMuOptionalPrefix
import MicroCFTA.SourceCurrentNativeCompilerOptionalPrefix
import MicroCFTA.SourceCurrentNativeEdgeOptionalPrefix

/-!
# Actual captured owners of optional instructions

The actual finite prefix determines a captured node query that owns the
selected optional instruction. The same receipt retains its entered domain
and exact child return. No future owner return is a premise.
-/
namespace MicroCFTA.SourceCurrentNativeOptionalOwner
open Cache InternedConstructorTemplates SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentNativeOptionalOwnerReceipt (Owner)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private def Recursive (request : NodeRequest Symbol Guard) : Prop :=
  SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu ∨
  SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu ∨
  SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu

private theorem compile_recursive (request : NodeRequest Symbol Guard) (recursive : Recursive request) :
    compileNode request = compileMu request.domain request.left request.right := by
  rcases recursive with both | left | right <;> simp only [compileNode, *]

private def Own (request : NodeRequest Symbol Guard) (fuel : Nat) (before after : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node) : Prop :=
  Recursive request ∧ ∃ first second childFuel,
    let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
      request.domain.key request.left request.right first second
    let childBefore : Checked width :=
      {before with native := advance before.native {before.native.machine with domains := entered.2}}
    fuel = childFuel + 1 ∧
    SourceRecursiveIntersectionControl.identity request.left = some first ∧
    SourceRecursiveIntersectionControl.identity request.right = some second ∧
    pair = SourceRecursiveIntersectionControl.pair first second ∧
    siteNext = .pure ∧
    Inputs (.code (compileMu request.domain request.left request.right)) before ∧
    step (.code (compileMu request.domain request.left request.right)) before = .yielded
      (.code ((requestNode entered.1 (body request.left) (body request.right)).bind
        (fun value => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure))) childBefore ∧
    Trace childFuel (.code (requestNode entered.1 (body request.left) (body request.right)))
      childBefore (.code (.pure siteBody)) after

private def Recover (fuel : Nat) : Prop :=
  (∀ (request : NodeRequest Symbol Guard) (before after : Checked width)
      (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node),
    Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) after →
    Owner fuel (.code (requestNode request.domain request.left request.right)) before
      pair siteBody siteNext after) ∧
  (∀ (request : EdgeRequest Symbol Guard) (before after : Checked width)
      (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Edge),
    Trace fuel (.code (requestEdge request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) after →
    Owner fuel (.code (requestEdge request.domain request.left request.right)) before
      pair siteBody siteNext after)

private theorem compiler (bound : Nat) (ih : ∀ count, count < bound → Recover (width := width) count)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (smaller : fuel < bound)
    (before after : Checked width) (pair : Nat × Nat) (siteBody : Node)
    (siteNext : Node → Code Symbol Guard Node)
    (actual : Trace fuel (.code (compileNode request)) before
      (.code (.optionalBinder pair siteBody siteNext)) after) :
    Own request fuel before after pair siteBody siteNext ∨
      Owner fuel (.code (compileNode request)) before pair siteBody siteNext after := by
  rcases SourceCurrentNativeCompilerOptionalPrefix.node request fuel before after pair siteBody siteNext actual with
    ⟨recursive, muTrace⟩ | nodeCut | edgeCut
  · obtain ⟨first, second, count, left, right, total, inputs, enteredStep, childSite⟩ :=
      SourceCurrentNativeMuOptionalPrefix.trace request fuel before after pair siteBody siteNext muTrace
    rcases childSite with ⟨innerNext, child, same⟩ | ⟨pairEq, ownNext, child⟩
    · let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
        request.domain.key request.left request.right first second
      let childBefore : Checked width :=
        {before with native := advance before.native {before.native.machine with domains := entered.2}}
      let childRequest : NodeRequest Symbol Guard := ⟨entered.1, body request.left, body request.right⟩
      let callNext := fun value => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure
      have childOwner := (ih count (by omega)).1 childRequest childBefore after pair siteBody innerNext child
      have boundOwner := SourceCurrentNativeOptionalOwnerReceipt.bind childOwner callNext
      have one : Trace 1 (.code (compileNode request)) before
          ((.code (requestNode childRequest.domain childRequest.left childRequest.right) : Control Node).bind callNext)
          childBefore := by
        rw [compile_recursive request recursive]
        exact .cons _ _ _ _ _ _ 0 inputs enteredStep (.refl _ _)
      have joined := SourceCurrentNativeOptionalOwnerReceipt.prepend one boundOwner
      have sum : 1 + count = fuel := by omega
      rw [sum] at joined
      rw [same]
      exact .inr joined
    · exact .inl ⟨recursive, first, second, count, total, left, right, pairEq, ownNext, inputs, enteredStep, child⟩
  · obtain ⟨prefixFuel, childFuel, child, callNext, entry, innerNext, total, earlier, called, same⟩ := nodeCut
    have childOwner := (ih childFuel (by omega)).1 child entry after pair siteBody innerNext called
    have joined := SourceCurrentNativeOptionalOwnerReceipt.prepend earlier
      (SourceCurrentNativeOptionalOwnerReceipt.bind childOwner callNext)
    rw [total] at joined
    rw [same]
    exact .inr joined
  · obtain ⟨prefixFuel, childFuel, child, callNext, entry, innerNext, total, earlier, called, same⟩ := edgeCut
    have childOwner := (ih childFuel (by omega)).2 child entry after pair siteBody innerNext called
    have joined := SourceCurrentNativeOptionalOwnerReceipt.prepend earlier
      (SourceCurrentNativeOptionalOwnerReceipt.bind childOwner callNext)
    rw [total] at joined
    rw [same]
    exact .inr joined

private theorem identity_keyable (value : Node) (name : Nat)
    (named : SourceRecursiveIntersectionControl.identity value = some name) :
    ∃ input, IntersectionFlatMemoKey.input value.referenceOf = some input := by
  cases value with
  | reference reference =>
      cases reference <;> simp_all [SourceRecursiveIntersectionControl.identity, Value.referenceOf, IntersectionFlatMemoKey.input]
  | empty | node | mu | union =>
      simp_all [SourceRecursiveIntersectionControl.identity, Value.referenceOf, IntersectionFlatMemoKey.input]

private theorem no_identity_pair (request : NodeRequest Symbol Guard)
    (missing : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none)
    (first second : Nat)
    (left : SourceRecursiveIntersectionControl.identity request.left = some first)
    (right : SourceRecursiveIntersectionControl.identity request.right = some second) : False := by
  obtain ⟨leftInput, leftCodec⟩ := identity_keyable _ _ left
  obtain ⟨rightInput, rightCodec⟩ := identity_keyable _ _ right
  have key := IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain _ _
    leftInput rightInput leftCodec rightCodec
  change IntersectionFlatMemoKeyDomain.sourceKey width request.domain request.left.referenceOf request.right.referenceOf = none at missing
  rw [key] at missing
  cases missing

private theorem recover (fuel : Nat) : Recover (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    constructor
    · intro request before after pair siteBody siteNext actual
      obtain ⟨queryInputs, direct | started⟩ :=
        SourceCurrentNativeQueryOptionalPrefix.node request before after pair siteBody siteNext actual
      · obtain ⟨compilerFuel, total, missing, selected, one, compiled⟩ := direct
        rcases compiler fuel ih request compilerFuel (by omega) before after pair siteBody siteNext compiled with own | nested
        · obtain ⟨recursive, first, second, childFuel, childTotal, left, right, rest⟩ := own
          exact False.elim (no_identity_pair request missing first second left right)
        · have earlier : Trace 1 (.code (requestNode request.domain request.left request.right)) before
              (.code (compileNode request)) before := .cons _ _ _ _ _ _ 0 queryInputs one (.refl _ _)
          have joined := SourceCurrentNativeOptionalOwnerReceipt.prepend earlier nested
          have sum : 1 + compilerFuel = fuel := by omega
          rw [sum] at joined
          exact joined
      · obtain ⟨compilerFuel, handle, chosen, running, captured, compilerBefore, innerNext,
          total, selected, demanded, suspended, evaluating, machine, stateEq, queryStep, compiled, same⟩ := started
        subst compilerBefore
        rcases compiler fuel ih captured compilerFuel (by omega) _ after pair siteBody innerNext compiled with own | nested
        · obtain ⟨recursive, first, second, childFuel, childTotal, left, right, pairEq,
            ownNext, enterInputs, enterStep, child⟩ := own
          refine ⟨0, childFuel, request, .pure, before, handle, chosen, running, captured, first, second,
            by omega, .refl _ _, queryInputs, selected, demanded, suspended, evaluating, machine,
            queryStep, recursive, left, right, pairEq, enterInputs, enterStep, child, ?_⟩
          rw [same, ownNext]
          rfl
        · let finish := fun value => .finishNode handle value (.pure value)
          have boundOwner := SourceCurrentNativeOptionalOwnerReceipt.bind nested finish
          have earlier : Trace 1 (.code (requestNode request.domain request.left request.right)) before
              ((.code (compileNode captured) : Control Node).bind finish) ⟨running, before.operations⟩ :=
            .cons _ _ _ _ _ _ 0 queryInputs queryStep (.refl _ _)
          have joined := SourceCurrentNativeOptionalOwnerReceipt.prepend earlier boundOwner
          have sum : 1 + compilerFuel = fuel := by omega
          rw [sum] at joined
          rw [same]
          exact joined
    · intro request before after pair siteBody siteNext actual
      obtain ⟨queryInputs, compilerFuel, handle, chosen, running, captured, compilerBefore, innerNext,
          total, selected, demanded, suspended, evaluating, machine, stateEq, queryStep, compiled, same⟩ :=
        SourceCurrentNativeQueryOptionalPrefix.edge request before after pair siteBody siteNext actual
      obtain ⟨first, second, combined, operations, index, child, values, entry, walkFuel, childFuel,
          childNext, arity, firstLoaded, secondLoaded, allocation, bodyStep, selectedChild, earlier,
          childTotal, prefixTrace, called, childSame⟩ :=
        SourceCurrentNativeEdgeOptionalPrefix.edge_body captured compilerFuel compilerBefore after pair siteBody innerNext compiled
      have childOwner := (ih childFuel (by omega)).1
        ⟨captured.domain, child.1, child.2⟩ entry after pair siteBody childNext called
      have bodyOwner := SourceCurrentNativeOptionalOwnerReceipt.prepend prefixTrace
        (SourceCurrentNativeOptionalOwnerReceipt.bind childOwner _)
      rw [childTotal] at bodyOwner
      rw [←childSame] at bodyOwner
      let finish := fun value => .finishEdge handle value (.pure value)
      have boundOwner := SourceCurrentNativeOptionalOwnerReceipt.bind bodyOwner finish
      have queried : Trace 1 (.code (requestEdge request.domain request.left request.right)) before
          ((Control.edgeBody captured (.pure : Edge → Code Symbol Guard Edge)).bind finish) compilerBefore :=
        .cons _ _ _ _ _ _ 0 queryInputs queryStep (.refl _ _)
      have joined := SourceCurrentNativeOptionalOwnerReceipt.prepend queried boundOwner
      have sum : 1 + compilerFuel = fuel := by omega
      rw [sum] at joined
      rw [same]
      exact joined

/-- Every actual node-query optional prefix derives its same captured compiler owner and child return. -/
theorem request (request : NodeRequest Symbol Guard) (fuel : Nat) (before after : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) after) :
    Owner fuel (.code (requestNode request.domain request.left request.right)) before
      pair siteBody siteNext after :=
  (recover fuel).1 request before after pair siteBody siteNext actual

end MicroCFTA.SourceCurrentNativeOptionalOwner
