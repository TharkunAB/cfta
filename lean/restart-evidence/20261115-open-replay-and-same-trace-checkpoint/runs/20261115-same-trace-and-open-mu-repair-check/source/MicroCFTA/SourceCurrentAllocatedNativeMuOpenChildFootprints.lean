import MicroCFTA.SourceCurrentAllocatedNativeMuClosedChildFootprints
import MicroCFTA.SourceCurrentAllocatedNativeOpenProductReclosure
import MicroCFTA.SourceSynthesisCurrentUniverseStartupAtoms

/-!
# Original U at an actual open-child Mu completion

The parent observation fixes its real child and middle state.
The smaller child profile describes the open rows at that same middle.
Actual optional completion returns the original U and preserves that full state.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeMuOpenChildFootprints
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency
open InternedBinderProtocol (NodeKey Reference)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable {width : Nat}

set_option autoImplicit false

/-- An actual open child with exact source rows recloses the Mu parent to original U at the same middle. -/
theorem node_mu_open_child_footprint
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (request : NodeRequest Symbol Guard) (before after : Checked width)
    (growth : Grows sourceHeap before.native.machine.heap)
    (first second fuel : Nat) (value : Value Symbol Guard)
    (leftIdentity : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity request.right = some second)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu)
    (done : SourceEqualityNativeDemand.execute fuel (.code (compileNode request)) before = .done value after)
    (children :
      let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
        request.left request.right first second
      let started : Checked width :=
        {before with native := advance before.native {before.native.machine with domains := entered.2}}
      ∀ childFuel, childFuel < fuel → ∀ child middle,
        Steps 1 (.code (compileNode request)) before
          (.code ((requestNode entered.1 (SourceRecursiveIntersectionKernel.body request.left)
            (SourceRecursiveIntersectionKernel.body request.right)).bind fun result =>
              .optionalBinder (SourceRecursiveIntersectionControl.pair first second) result .pure)) started →
        SourceEqualityNativeDemand.execute childFuel
          (.code (requestNode entered.1 (SourceRecursiveIntersectionKernel.body request.left)
            (SourceRecursiveIntersectionKernel.body request.right))) started = .done child middle →
        Facts middle.native.machine.heap ∧ Extension started.native.machine middle.native.machine ∧
        Available middle.native.machine.heap child ∧
        ∃ (productEntry : Interned NodeKey) (products : List (EdgeValue Symbol Guard)),
          child = .node productEntry (canonicalEdges products) 0
            [.intersection (SourceRecursiveIntersectionControl.pair first second).1
              (SourceRecursiveIntersectionControl.pair first second).2] ∧
          All₂ (fun (source : EdgeValue Symbol Guard) target =>
            target.children = source.children.map (input (replacement (.interned entry.identity)
              (.reference (.intersection (SourceRecursiveIntersectionControl.pair first second).1
                (SourceRecursiveIntersectionControl.pair first second).2)))) ∧
            target.entry.key = ⟨source.entry.key.symbol,
              (source.children.map (input (replacement (.interned entry.identity)
                (.reference (.intersection (SourceRecursiveIntersectionControl.pair first second).1
                  (SourceRecursiveIntersectionControl.pair first second).2))))).map Value.referenceOf, top⟩)
            (match body with | .node _ rows _ _ => rows | _ => []) products ∧
          (∀ row ∈ products, EdgeResident middle.native.machine.heap row)) :
    value = .mu entry body depth ordinary ∧ Available after.native.machine.heap value ∧ value.free = [] ∧
    (∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity) ∧
    ∃ child middle childSteps restSteps,
      after = middle ∧ childSteps + 1 < fuel ∧
      Steps 1 (.code (compileNode request)) before
        (.code ((requestNode
          (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
            request.left request.right first second).1
          (SourceRecursiveIntersectionKernel.body request.left) (SourceRecursiveIntersectionKernel.body request.right)).bind
          fun result => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) result .pure))
        {before with native := advance before.native {before.native.machine with domains :=
          (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
            request.left request.right first second).2}} ∧
      Steps childSteps
        (.code (requestNode
          (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
            request.left request.right first second).1
          (SourceRecursiveIntersectionKernel.body request.left) (SourceRecursiveIntersectionKernel.body request.right)))
        {before with native := advance before.native {before.native.machine with domains :=
          (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
            request.left request.right first second).2}}
        (.code (.pure child)) middle ∧
      child.free = [.intersection (SourceRecursiveIntersectionControl.pair first second).1
        (SourceRecursiveIntersectionControl.pair first second).2] ∧
      SourceEqualityNativeDemand.execute (restSteps + 1)
        (.code (.optionalBinder (SourceRecursiveIntersectionControl.pair first second) child .pure)) middle =
        .done value after := by
  obtain ⟨child, middle, childSteps, restSteps, shorter, entered, childTrace, binderDone⟩ :=
    SourceCurrentAllocatedNativeMuClosedChildFootprints.node_mu_observation
      request before after first second fuel value leftIdentity rightIdentity selected done
  have childDone := trace_done childSteps _ _ middle child childTrace
  obtain ⟨middleFacts, continuation, childAvailable, productEntry, products, productRead, readback, resident⟩ :=
    children (childSteps + 1) shorter child middle entered childDone
  have pastGrowth : Grows before.native.machine.heap middle.native.machine.heap := continuation.heap
  have middleGrowth : Grows sourceHeap middle.native.machine.heap := grows_trans growth pastGrowth
  have reclosed := SourceCurrentAllocatedNativeOpenProductReclosure.stored_open_product_optional_reclosure
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    middle middleFacts middleGrowth (SourceRecursiveIntersectionControl.pair first second)
    child productEntry products productRead childAvailable readback resident
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  have observed := SourceEqualityNativeDemand.done_stable (restSteps + 1) 2
    (.code (.optionalBinder (SourceRecursiveIntersectionControl.pair first second) child .pure))
    middle after value binderDone
  have expected := SourceEqualityNativeDemand.done_stable 2 (restSteps + 1)
    (.code (.optionalBinder (SourceRecursiveIntersectionControl.pair first second) child .pure))
    middle middle universeValue reclosed.2.2
  rw [Nat.add_comm 2 (restSteps + 1)] at expected
  have same : value = universeValue ∧ after = middle := Outcome.done.inj (observed.symm.trans expected)
  have universeAvailable : Available middle.native.machine.heap universeValue :=
    middleFacts.cached.nodes key _ (middleGrowth.nodeRecords key _ stored)
  have universeAtoms : ∀ atom ∈ InternedBoundaryAtoms.atoms universeValue, atom = .mu entry.identity := by
    intro atom included
    simpa only [universeValue, InternedBoundaryAtoms.atoms, List.mem_singleton] using included
  have universeClosed :=
    SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_boundary_atoms_closed_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      middle.native.machine.heap middleFacts middleGrowth universeValue universeAvailable universeAtoms
  have valueAvailable : Available after.native.machine.heap value := by
    rw [same.1, same.2]
    exact universeAvailable
  have valueClosed : value.free = [] := by rw [same.1]; exact universeClosed
  have valueAtoms : ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity := by
    rw [same.1]
    exact universeAtoms
  have childOpen : child.free = [.intersection (SourceRecursiveIntersectionControl.pair first second).1
      (SourceRecursiveIntersectionControl.pair first second).2] := by
    rw [productRead]
    rfl
  exact ⟨same.1, valueAvailable, valueClosed, valueAtoms, child, middle, childSteps, restSteps,
    same.2, shorter, entered, childTrace, childOpen, binderDone⟩

end MicroCFTA.SourceCurrentAllocatedNativeMuOpenChildFootprints

#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuOpenChildFootprints.node_mu_open_child_footprint
