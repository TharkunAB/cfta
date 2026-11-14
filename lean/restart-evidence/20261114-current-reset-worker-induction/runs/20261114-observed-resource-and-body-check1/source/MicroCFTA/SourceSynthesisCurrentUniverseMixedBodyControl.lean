import MicroCFTA.SourceSynthesisCurrentUniverseBodyChildClassification
import MicroCFTA.SourceRecursiveIntersectionDomainEquivalence

/-!
# Actual source body control before the ordinary mixed payload

Available node records cannot share the original Mu identity.
The original seen pair therefore cannot select a body and ordinary operand.
The open body and closed operand exclude reset and closed self reuse.
The actual comparison retains a swap or selects the ordinary payload.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyControl
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedBoundaryAtoms
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl
open SourceRecursiveIntersectionDomain
open SourceSynthesisUniversePrefixHeight (height)

set_option autoImplicit false

section Generic
variable {Symbol Guard : Type}

/-- Exact physical readback separates every ordinary node from an available Mu identity. -/
private theorem node_mu_identity_ne
    (heap : State Symbol Guard) (facts : Facts heap)
    (nodeEntry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (nodeDepth : Nat) (free : List Reference)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (nodeAvailable : Available heap (.node nodeEntry rows nodeDepth free))
    (universeAvailable : Available heap (.mu entry body depth ordinary)) :
    nodeEntry.identity ≠ entry.identity := by
  intro same
  have nodeRead := SourcePreparedSharedRows.read_identity heap facts
    (.node nodeEntry rows nodeDepth free) nodeAvailable entry.identity
    (by simpa only [SourcePreparedSharedRows.reference] using congrArg some same)
  have universeRead := SourcePreparedSharedRows.read_identity heap facts
    (.mu entry body depth ordinary) universeAvailable entry.identity rfl
  have impossible := Option.some.inj (nodeRead.symm.trans universeRead)
  cases impossible

/-- A pair whose two members avoid U cannot equal a pair containing U. -/
private theorem pair_apart_owner (left right owner pattern : Nat)
    (leftApart : left ≠ owner) (rightApart : right ≠ owner) :
    pair left right ≠ pair owner pattern := by
  intro same
  have lower := congrArg Prod.fst same
  have upper := congrArg Prod.snd same
  simp only [pair] at lower upper
  omega

/-- Both ordinary operand orders retain only the actual swap or ordinary control branch. -/
private theorem open_closed_node_control
    (heap : State Symbol Guard) (facts : Facts heap)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (ownerId : Nat)
    (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (operandEntry : Interned NodeKey) (operandRows : List (EdgeValue Symbol Guard))
    (operandDepth : Nat) (operandFree : List Reference)
    (bodyAvailable : Available heap (.node bodyEntry bodyRows 0 [.interned ownerId]))
    (operandAvailable : Available heap (.node operandEntry operandRows operandDepth operandFree))
    (operandClosed : (Value.node operandEntry operandRows operandDepth operandFree).free = [])
    (fresh : pair bodyEntry.identity operandEntry.identity ∉ domain.key.seen) :
    (decision domain.key (.node bodyEntry bodyRows 0 [.interned ownerId])
        (.node operandEntry operandRows operandDepth operandFree) =
      if greater (.node bodyEntry bodyRows 0 [.interned ownerId])
        (.node operandEntry operandRows operandDepth operandFree) then .swap else .ordinary) ∧
    (decision domain.key (.node operandEntry operandRows operandDepth operandFree)
        (.node bodyEntry bodyRows 0 [.interned ownerId]) =
      if greater (.node operandEntry operandRows operandDepth operandFree)
        (.node bodyEntry bodyRows 0 [.interned ownerId]) then .swap else .ordinary) := by
  let bodyValue : Value Symbol Guard := .node bodyEntry bodyRows 0 [.interned ownerId]
  let operand : Value Symbol Guard := .node operandEntry operandRows operandDepth operandFree
  have bodyOpen : bodyValue.free ≠ [] := by simp only [bodyValue, Value.free, List.cons_ne_self]
  have different : operand ≠ bodyValue := by
    intro same
    exact bodyOpen ((congrArg Value.free same).symm.trans operandClosed)
  have forwardEmpty : hasEmpty bodyValue operand = false := by
    simp [bodyValue, operand, hasEmpty, Value.referenceOf]
  have reverseEmpty : hasEmpty operand bodyValue = false := by
    simp [bodyValue, operand, hasEmpty, Value.referenceOf]
  have forwardReset : reset domain.key bodyValue operand = false := by
    simp [bodyValue, operand, reset, Value.free]
  have reverseReset : reset domain.key operand bodyValue = false := by
    simp [bodyValue, operand, reset, Value.free]
  have forwardSelf : closedSelf bodyValue operand = false := by
    simp [bodyValue, closedSelf, Value.free]
  have reverseSelf : closedSelf operand bodyValue = false := by
    cases observed : closedSelf operand bodyValue with
    | false => rfl
    | true =>
        exact False.elim (different (self_record heap facts operand bodyValue operandAvailable bodyAvailable observed))
  have reverseFresh : pair operandEntry.identity bodyEntry.identity ∉ domain.key.seen := by
    have same : pair operandEntry.identity bodyEntry.identity = pair bodyEntry.identity operandEntry.identity := by
      simp only [pair, Nat.min_comm, Nat.max_comm]
    rw [same]
    exact fresh
  constructor
  · simp [decision, forwardEmpty, forwardReset, forwardSelf,
      bodyValue, operand, identity, fresh, payload]
  · simp [decision, reverseEmpty, reverseReset, reverseSelf,
      bodyValue, operand, identity, reverseFresh, payload]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual swap spends one fuel and keeps the same machine for its reversed request. -/
theorem execute_ordinary_control_swap_step
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : Value Symbol Guard) (state : Machine Symbol Guard)
    (controlled : decision domain.key left right = if greater left right then .swap else .ordinary)
    (swap : greater left right = true) :
    execute emptyGuard conjoin (fuel + 1) domain left right state =
      execute emptyGuard conjoin fuel domain right left state := by
  have selected : decision domain.key left right = .swap := by simpa only [swap, ite_true] using controlled
  simp only [execute, onNode, selected]

/-- The actual swap uses only the atom property of its strictly lower-fuel reversed call. -/
theorem swap_atoms_of_fuel_induction
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right)
    (ownerId : Nat)
    (controlled : decision domain.key left right = if greater left right then .swap else .ordinary)
    (swap : greater left right = true)
    (fuelInduction : ∀ (value : Value Symbol Guard) (after : Machine Symbol Guard),
      execute emptyGuard conjoin fuel domain right left state = .done value after →
      ∀ atom ∈ atoms value, atom = .mu ownerId) :
    Checked state (execute emptyGuard conjoin (fuel + 1) domain left right state)
      (fun after value => Available after.heap value ∧ ∀ atom ∈ atoms value, atom = .mu ownerId) := by
  have native := execute_checked emptyGuard conjoin (fuel + 1) domain left right state
    valid known leftAvailable rightAvailable
  refine ⟨native.valid, native.extension, ?_⟩
  intro value after returned
  refine ⟨native.result value after returned, ?_⟩
  rw [execute_ordinary_control_swap_step emptyGuard conjoin fuel domain left right state controlled swap] at returned
  exact fuelInduction value after returned

end Generic

open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

/-- The same source and original mixed entry derive both actual ordinary-body control alternatives. -/
theorem current_stored_universe_body_ordinary_control_after_mixed_extension
    [DecidableEq (EdgeKey Symbol Guard)]
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
    (patternIdentity : identity pattern = some patternId) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
    let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
    ∀ later : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid later → Extension initial later →
    ∀ (operandEntry : Interned NodeKey) (operandRows : List (EdgeValue Symbol Guard))
      (operandDepth : Nat) (operandFree : List Reference),
      let operand : Value Symbol Guard := .node operandEntry operandRows operandDepth operandFree
      Available later.heap operand → operand.free = [] →
      (∀ atom ∈ atoms operand, atom = .mu entry.identity) → height operand ≤ height pattern →
      ∃ (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard)),
        body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧ Available later.heap body ∧
        bodyEntry.identity ≠ entry.identity ∧ operandEntry.identity ≠ entry.identity ∧
        pair bodyEntry.identity operandEntry.identity ∉ entered.1.key.seen ∧
        pair operandEntry.identity bodyEntry.identity ∉ entered.1.key.seen ∧
        ∀ bodyFirst : Bool,
          decision entered.1.key (if bodyFirst then body else operand) (if bodyFirst then operand else body) =
            if greater (if bodyFirst then body else operand) (if bodyFirst then operand else body)
              then .swap else .ordinary := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
  dsimp only
  intro later laterValid continuation operandEntry operandRows operandDepth operandFree
  intro operandAvailable operandClosed operandAtoms bounded
  obtain ⟨bodyEntry, bodyRows, bodyEq, bodyAvailable, _requests⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_ordinary_child_requests_after_mixed_extension
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity
      later laterValid continuation operandEntry operandRows operandDepth operandFree
      operandAvailable operandClosed operandAtoms bounded
  have originalAvailable : Available heap universeValue :=
    facts.cached.nodes key _ (growth.nodeRecords key _ stored)
  have laterUniverse : Available later.heap universeValue := continuation.available universeValue originalAvailable
  have actualBody : Available later.heap (.node bodyEntry bodyRows 0 [.interned entry.identity]) := by
    rw [← bodyEq]
    exact bodyAvailable
  have bodyApart : bodyEntry.identity ≠ entry.identity :=
    node_mu_identity_ne later.heap laterValid.1 bodyEntry bodyRows 0 [.interned entry.identity]
      entry body depth ordinary actualBody laterUniverse
  have operandApart : operandEntry.identity ≠ entry.identity :=
    node_mu_identity_ne later.heap laterValid.1 operandEntry operandRows operandDepth operandFree
      entry body depth ordinary operandAvailable laterUniverse
  have originalKey := SourceRecursiveIntersectionSchedule.entered_key domains cacheValid
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  have pairApart := pair_apart_owner bodyEntry.identity operandEntry.identity entry.identity patternId bodyApart operandApart
  have fresh : pair bodyEntry.identity operandEntry.identity ∉ entered.1.key.seen := by
    intro seen
    rw [originalKey] at seen
    rcases (extend_seen IntersectionEmptyDomain.emptyKey
      ((SourceRecursiveIntersectionEnvironment.bindings universeValue pattern).map Prod.fst)
      (pair entry.identity patternId) (pair bodyEntry.identity operandEntry.identity)).mp seen with same | old
    · exact pairApart same
    · simp only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil] at old
  have reverseFresh : pair operandEntry.identity bodyEntry.identity ∉ entered.1.key.seen := by
    have same : pair operandEntry.identity bodyEntry.identity = pair bodyEntry.identity operandEntry.identity := by
      simp only [pair, Nat.min_comm, Nat.max_comm]
    rw [same]
    exact fresh
  have control := open_closed_node_control later.heap laterValid.1 entered.1 entry.identity bodyEntry bodyRows
    operandEntry operandRows operandDepth operandFree actualBody operandAvailable operandClosed fresh
  refine ⟨bodyEntry, bodyRows, bodyEq, bodyAvailable, bodyApart, operandApart, fresh, reverseFresh, ?_⟩
  intro bodyFirst
  cases bodyFirst with
  | false => simpa only [bodyEq] using control.2
  | true => simpa only [bodyEq] using control.1

end MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyControl

#check MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyControl.node_mu_identity_ne
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyControl.node_mu_identity_ne

#check MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyControl.pair_apart_owner
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyControl.pair_apart_owner

#check MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyControl.open_closed_node_control
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyControl.open_closed_node_control

#check MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyControl.execute_ordinary_control_swap_step
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyControl.execute_ordinary_control_swap_step

#check MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyControl.swap_atoms_of_fuel_induction
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyControl.swap_atoms_of_fuel_induction

#check MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyControl.current_stored_universe_body_ordinary_control_after_mixed_extension
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyControl.current_stored_universe_body_ordinary_control_after_mixed_extension
