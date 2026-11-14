import MicroCFTA.SourceSynthesisCurrentUniverseReferenceDescendantSteps
import MicroCFTA.InternedBoundaryAtoms

/-!
# The original refU and closed-node case under lower-fuel A

Actual sorting, bound readback and closed reset precede empty-domain A.
Short fuel prefixes retain the exhausted result in the same machine.
The original entered domain remains fixed before the actual reset.
The full simultaneous generated-Type theorem remains open.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseReferenceNodeInductionStep
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedBoundaryAtoms
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl
open SourceRecursiveIntersectionDomain
open SourceSynthesisUniversePrefixHeight (height)

set_option autoImplicit false

section Generic
variable {Symbol Guard : Type}

/-- The actual short prefixes resolve right refU or sort left refU in the same machine. -/
private theorem node_reference_prefix_steps
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (state : Machine Symbol Guard)
    (owner : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (found : lookup state.heap domain.key owner.identity = some (.mu owner body depth ordinary))
    (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (level : Nat)
    (fresh : pair entry.identity owner.identity ∉ domain.key.seen) (fuel : Nat) :
    execute emptyGuard conjoin (fuel + 1) domain (.node entry rows level [])
        (.reference (.interned owner.identity)) state =
      execute emptyGuard conjoin fuel domain (.node entry rows level []) (.mu owner body depth ordinary) state ∧
    execute emptyGuard conjoin (fuel + 1) domain (.reference (.interned owner.identity))
        (.node entry rows level []) state =
      execute emptyGuard conjoin fuel domain (.node entry rows level []) (.reference (.interned owner.identity)) state := by
  have bound : owner.identity ∈ names domain.key := by
    by_cases member : owner.identity ∈ names domain.key
    · exact member
    · simp only [lookup, member, ite_false, reduceCtorEq] at found
  have read : SourcePreparedSharedRows.read state.heap owner.identity = some (.mu owner body depth ordinary) := by
    simpa only [lookup, bound, ite_true] using found
  have forwardOrder : compare (1 : Nat) 4 = .lt := by decide
  have reverseOrder : compare (4 : Nat) 1 = .gt := by decide
  have forwardSelected : decision domain.key (.node entry rows level [])
      (.reference (.interned owner.identity)) = .rightReference := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      Value.referenceOf, Value.free, fresh, forwardOrder]
  have reverseSelected : decision domain.key (.reference (.interned owner.identity))
      (.node entry rows level []) = .swap := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag,
      Value.referenceOf, Value.free, reverseOrder]
  constructor
  · rw [execute]
    simp only [onNode, forwardSelected]
    simp only [reference, bound, ite_true, read, Bool.false_eq_true, ite_false]
  · simp only [execute, onNode, reverseSelected]

end Generic

open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

/-- Both original refU/node orders use only strictly smaller-fuel empty-domain A after the actual reset. -/
theorem current_stored_universe_reference_node_of_coupled_fuel_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (patternAvailable : Available heap pattern)
    (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId) (fuel : Nat) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
    let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
    ∀ later : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid later → Extension initial later →
    ∀ (operandEntry : Interned NodeKey) (operandRows : List (EdgeValue Symbol Guard))
      (operandDepth : Nat) (operandFree : List Reference),
      let operand : Value Symbol Guard := .node operandEntry operandRows operandDepth operandFree
      Available later.heap operand → operand.free = [] →
      (∀ atom ∈ atoms operand, atom = .mu entry.identity) → height operand < height pattern →
      (∀ smaller : Nat, smaller < fuel → ∀ current : Machine Symbol Guard,
        SourceRecursiveIntersectionKernel.Valid current → Extension later current →
        ∀ left right : Value Symbol Guard, Available current.heap left → Available current.heap right →
        left.free = [] → right.free = [] →
        (∀ atom ∈ atoms left, atom = .mu entry.identity) →
        (∀ atom ∈ atoms right, atom = .mu entry.identity) →
        Checked current
          (execute top SourceEqualityPCSNativeEdge.conjoin smaller IntersectionEmptyDomain.emptyDomain left right current)
          (fun after value => Available after.heap value ∧ value.free = [] ∧
            ∀ atom ∈ atoms value, atom = .mu entry.identity)) →
      ∀ referenceFirst : Bool,
      Checked later (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1
        (if referenceFirst then .reference (.interned entry.identity) else operand)
        (if referenceFirst then operand else .reference (.interned entry.identity)) later)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ atoms value, atom = .mu entry.identity) := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
  dsimp only
  intro later laterValid continuation operandEntry operandRows operandDepth operandFree
  intro operandAvailable operandClosed operandAtoms strict closedInduction referenceFirst
  have freeEmpty : operandFree = [] := operandClosed
  subst operandFree
  let operand : Value Symbol Guard := .node operandEntry operandRows operandDepth []
  obtain ⟨universeClosed, freshness⟩ :=
    SourceSynthesisUniverseMixedDescendantFreshness.current_stored_universe_strict_descendant_fresh_after_mixed_entry
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity
  obtain ⟨_different, _directApart, _reverseApart, _directFresh, reverseFresh, _known, found⟩ :=
    freshness later laterValid continuation operand operandAvailable operandClosed operandEntry.identity rfl strict
  have laterGrowth : Grows sourceHeap later.heap := grows_trans growth continuation.heap
  have universeAvailable : Available later.heap universeValue :=
    laterValid.1.cached.nodes key _ (laterGrowth.nodeRecords key _ stored)
  have universeAtoms : ∀ atom ∈ atoms universeValue, atom = .mu entry.identity := by
    intro atom occurrence
    exact List.mem_singleton.mp occurrence
  have prefixes := node_reference_prefix_steps top SourceEqualityPCSNativeEdge.conjoin entered.1 later
    entry body depth ordinary found operandEntry operandRows operandDepth reverseFresh
  have complete :=
    SourceSynthesisCurrentUniverseReferenceDescendantSteps.current_stored_universe_node_reference_descendant_after_mixed_entry
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity
      later laterValid continuation operandEntry operandRows operandDepth operandAvailable strict
  cases referenceFirst with
  | false =>
      change Checked later
        (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1 operand (.reference (.interned entry.identity)) later)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ atoms value, atom = .mu entry.identity)
      cases fuel with
      | zero => exact checked_failed later laterValid .exhausted _
      | succ preceding =>
          cases preceding with
          | zero =>
              have exhausted : execute top SourceEqualityPCSNativeEdge.conjoin 1 entered.1 operand
                  (.reference (.interned entry.identity)) later = .failed .exhausted later :=
                (prefixes 0).1.trans rfl
              exact exhausted.symm ▸ checked_failed later laterValid .exhausted _
          | succ smaller =>
              have checked := closedInduction smaller (by omega) later laterValid (Extension.refl later)
                operand universeValue operandAvailable universeAvailable operandClosed universeClosed operandAtoms universeAtoms
              exact (complete smaller).1.symm ▸ checked
  | true =>
      change Checked later
        (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1 (.reference (.interned entry.identity)) operand later)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ atoms value, atom = .mu entry.identity)
      cases fuel with
      | zero => exact checked_failed later laterValid .exhausted _
      | succ preceding =>
          cases preceding with
          | zero =>
              have exhausted : execute top SourceEqualityPCSNativeEdge.conjoin 1 entered.1
                  (.reference (.interned entry.identity)) operand later = .failed .exhausted later :=
                (prefixes 0).2.trans rfl
              exact exhausted.symm ▸ checked_failed later laterValid .exhausted _
          | succ remaining =>
              cases remaining with
              | zero =>
                  have exhausted : execute top SourceEqualityPCSNativeEdge.conjoin 2 entered.1
                      (.reference (.interned entry.identity)) operand later = .failed .exhausted later :=
                    ((prefixes 1).2.trans (prefixes 0).1).trans rfl
                  exact exhausted.symm ▸ checked_failed later laterValid .exhausted _
              | succ smaller =>
                  have checked := closedInduction smaller (by omega) later laterValid (Extension.refl later)
                    operand universeValue operandAvailable universeAvailable operandClosed universeClosed operandAtoms universeAtoms
                  exact (complete smaller).2.symm ▸ checked

end MicroCFTA.SourceSynthesisCurrentUniverseReferenceNodeInductionStep

#print axioms MicroCFTA.SourceSynthesisCurrentUniverseReferenceNodeInductionStep.node_reference_prefix_steps
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseReferenceNodeInductionStep.current_stored_universe_reference_node_of_coupled_fuel_induction
