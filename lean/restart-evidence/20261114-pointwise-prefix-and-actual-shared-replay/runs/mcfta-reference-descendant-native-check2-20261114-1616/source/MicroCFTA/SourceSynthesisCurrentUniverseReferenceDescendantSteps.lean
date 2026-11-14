-- UNCOMPILED SOURCE DRAFT. Root owns validation.
import MicroCFTA.SourceSynthesisUniverseMixedDescendantFreshness
import MicroCFTA.SourceEqualityPCSNativeEdge

/-!
# Actual native reference requests below a mixed entry

Ordinary requests sort, resolve the original Mu, and reset the domain.
Union requests distribute before reference lookup. Both equations retain
the actual lower-fuel calls and every returned machine and failure.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseReferenceDescendantSteps
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel
open SourceSynthesisUniversePrefixHeight (height)

set_option autoImplicit false

section Generic
variable {Symbol Guard : Type}

/-- A successful physical binding read supplies membership, readback, and a nonempty map. -/
private theorem lookup_resources (heap : State Symbol Guard)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat) (value : Value Symbol Guard)
    (found : lookup heap domain.key name = some value) :
    name ∈ names domain.key ∧ SourcePreparedSharedRows.read heap name = some value ∧
      domain.key.free.isEmpty = false := by
  by_cases bound : name ∈ names domain.key
  · refine ⟨bound, ?_, ?_⟩
    · simpa only [lookup, bound, ite_true] using found
    · cases values : domain.key.free with
      | nil => simp [names, values] at bound
      | cons first rest => rfl
  · simp only [lookup, bound, ite_false, reduceCtorEq] at found

/-- An ordinary operand reaches the right-reference branch when its actual pair is fresh. -/
private theorem node_reference_branch (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (depth name : Nat)
    (fresh : pair entry.identity name ∉ domain.key.seen) :
    decision domain.key (.node entry rows depth []) (.reference (.interned name)) = .rightReference := by
  have tagOrder : compare (1 : Nat) 4 = .lt := by decide
  simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
    Value.referenceOf, Value.free, fresh, tagOrder]

/-- A union operand distributes before reference lookup when its actual pair is fresh. -/
private theorem union_reference_branch (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth name : Nat)
    (fresh : pair entry.identity name ∉ domain.key.seen) :
    decision domain.key (.union entry members depth []) (.reference (.interned name)) = .leftUnion := by
  have tagOrder : compare (3 : Nat) 4 = .lt := by decide
  simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
    Value.referenceOf, Value.free, fresh, tagOrder]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Two ordinary-prefix levels resolve U and reset; the reversed input adds one sort level. -/
private theorem node_reference_steps (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (state : Machine Symbol Guard)
    (owner : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (closed : (Value.mu owner body depth ordinary).free = [])
    (found : lookup state.heap domain.key owner.identity = some (.mu owner body depth ordinary))
    (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (level : Nat)
    (fresh : pair entry.identity owner.identity ∉ domain.key.seen) (fuel : Nat) :
    execute emptyGuard conjoin (fuel + 2) domain (.node entry rows level [])
        (.reference (.interned owner.identity)) state =
      execute emptyGuard conjoin fuel IntersectionEmptyDomain.emptyDomain
        (.node entry rows level []) (.mu owner body depth ordinary) state ∧
    execute emptyGuard conjoin (fuel + 3) domain (.reference (.interned owner.identity))
        (.node entry rows level []) state =
      execute emptyGuard conjoin fuel IntersectionEmptyDomain.emptyDomain
        (.node entry rows level []) (.mu owner body depth ordinary) state := by
  obtain ⟨bound, read, nonempty⟩ := lookup_resources state.heap domain owner.identity _ found
  have selected := node_reference_branch domain entry rows level owner.identity fresh
  have restart : reset domain.key (.node entry rows level []) (.mu owner body depth ordinary) = true := by
    unfold reset
    rw [closed]
    simp [Value.free, nonempty]
  have resetSelected := reset_first domain.key (.node entry rows level [])
    (.mu owner body depth ordinary) rfl restart
  have direct : execute emptyGuard conjoin (fuel + 2) domain (.node entry rows level [])
      (.reference (.interned owner.identity)) state =
      execute emptyGuard conjoin fuel IntersectionEmptyDomain.emptyDomain
        (.node entry rows level []) (.mu owner body depth ordinary) state := by
    rw [show fuel + 2 = (fuel + 1) + 1 by omega, execute]
    simp only [onNode, selected]
    simp only [reference, bound, ite_true, read, Bool.false_eq_true, ite_false]
    rw [execute]
    simp only [onNode, resetSelected]
  refine ⟨direct, ?_⟩
  rw [show fuel + 3 = (fuel + 2) + 1 by omega, execute]
  change execute emptyGuard conjoin (fuel + 2) domain (.node entry rows level [])
    (.reference (.interned owner.identity)) state = _
  exact direct

/-- Union execution retains the actual ordered walk and constructor continuation. -/
private theorem union_reference_steps (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (state : Machine Symbol Guard)
    (name : Nat) (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (level : Nat)
    (fresh : pair entry.identity name ∉ domain.key.seen) (fuel : Nat) :
    execute emptyGuard conjoin (fuel + 1) domain (.union entry members level [])
        (.reference (.interned name)) state =
      (walk (fun member => execute emptyGuard conjoin fuel domain member
        (.reference (.interned name))) members state).bind
        (fun values after => work (makeUnion values) after) ∧
    execute emptyGuard conjoin (fuel + 2) domain (.reference (.interned name))
        (.union entry members level []) state =
      (walk (fun member => execute emptyGuard conjoin fuel domain member
        (.reference (.interned name))) members state).bind
        (fun values after => work (makeUnion values) after) := by
  have selected := union_reference_branch domain entry members level name fresh
  have direct : execute emptyGuard conjoin (fuel + 1) domain (.union entry members level [])
      (.reference (.interned name)) state =
      (walk (fun member => execute emptyGuard conjoin fuel domain member
        (.reference (.interned name))) members state).bind
        (fun values after => work (makeUnion values) after) := by
    rw [execute]
    simp only [onNode, selected]
  refine ⟨direct, ?_⟩
  rw [show fuel + 2 = (fuel + 1) + 1 by omega, execute]
  change execute emptyGuard conjoin (fuel + 1) domain (.union entry members level [])
    (.reference (.interned name)) state = _
  exact direct

end Generic

open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

/-- The same original build derives both ordinary reference/reset equations in the original mixed domain. -/
theorem current_stored_universe_node_reference_descendant_after_mixed_entry
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (owner : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu owner body depth ordinary))
    (heap : State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (patternAvailable : Available heap pattern)
    (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId) :
    let universeValue : Value Symbol Guard := .mu owner body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern owner.identity patternId
    let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
    ∀ later : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid later → Extension initial later →
      ∀ (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (level : Nat),
      Available later.heap (.node entry rows level []) →
      height (.node entry rows level []) < height pattern →
      ∀ fuel : Nat,
      execute top SourceEqualityPCSNativeEdge.conjoin (fuel + 2) entered.1 (.node entry rows level [])
          (.reference (.interned owner.identity)) later =
        execute top SourceEqualityPCSNativeEdge.conjoin fuel IntersectionEmptyDomain.emptyDomain
          (.node entry rows level []) universeValue later ∧
      execute top SourceEqualityPCSNativeEdge.conjoin (fuel + 3) entered.1
          (.reference (.interned owner.identity)) (.node entry rows level []) later =
        execute top SourceEqualityPCSNativeEdge.conjoin fuel IntersectionEmptyDomain.emptyDomain
          (.node entry rows level []) universeValue later := by
  let universeValue : Value Symbol Guard := .mu owner body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern owner.identity patternId
  let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
  obtain ⟨universeClosed, freshness⟩ :=
    SourceSynthesisUniverseMixedDescendantFreshness.current_stored_universe_strict_descendant_fresh_after_mixed_entry
      lib query signed whole accepted rootValue sourceHeap built key owner body depth ordinary stored
      heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity
  dsimp only
  intro later laterValid continuation entry rows level available smaller fuel
  obtain ⟨_different, _directApart, _reverseApart, _directFresh, reverseFresh, _known, found⟩ :=
    freshness later laterValid continuation (.node entry rows level []) available rfl entry.identity rfl smaller
  exact node_reference_steps top SourceEqualityPCSNativeEdge.conjoin entered.1 later owner body depth ordinary
    universeClosed found entry rows level reverseFresh fuel

/-- The same original build derives both union-walk equations in the original mixed domain. -/
theorem current_stored_universe_union_reference_descendant_after_mixed_entry
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (owner : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu owner body depth ordinary))
    (heap : State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (patternAvailable : Available heap pattern)
    (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId) :
    let universeValue : Value Symbol Guard := .mu owner body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern owner.identity patternId
    let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
    ∀ later : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid later → Extension initial later →
      ∀ (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (level : Nat),
      Available later.heap (.union entry members level []) →
      height (.union entry members level []) < height pattern →
      ∀ fuel : Nat,
      execute top SourceEqualityPCSNativeEdge.conjoin (fuel + 1) entered.1 (.union entry members level [])
          (.reference (.interned owner.identity)) later =
        (walk (fun member => execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1 member
          (.reference (.interned owner.identity))) members later).bind
          (fun values after => work (makeUnion values) after) ∧
      execute top SourceEqualityPCSNativeEdge.conjoin (fuel + 2) entered.1
          (.reference (.interned owner.identity)) (.union entry members level []) later =
        (walk (fun member => execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1 member
          (.reference (.interned owner.identity))) members later).bind
          (fun values after => work (makeUnion values) after) := by
  let universeValue : Value Symbol Guard := .mu owner body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern owner.identity patternId
  let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
  obtain ⟨_universeClosed, freshness⟩ :=
    SourceSynthesisUniverseMixedDescendantFreshness.current_stored_universe_strict_descendant_fresh_after_mixed_entry
      lib query signed whole accepted rootValue sourceHeap built key owner body depth ordinary stored
      heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity
  dsimp only
  intro later laterValid continuation entry members level available smaller fuel
  obtain ⟨_different, _directApart, _reverseApart, _directFresh, reverseFresh, _known, _found⟩ :=
    freshness later laterValid continuation (.union entry members level []) available rfl entry.identity rfl smaller
  exact union_reference_steps top SourceEqualityPCSNativeEdge.conjoin entered.1 later
    owner.identity entry members level reverseFresh fuel

end MicroCFTA.SourceSynthesisCurrentUniverseReferenceDescendantSteps

#print axioms MicroCFTA.SourceSynthesisCurrentUniverseReferenceDescendantSteps.current_stored_universe_node_reference_descendant_after_mixed_entry
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseReferenceDescendantSteps.current_stored_universe_union_reference_descendant_after_mixed_entry
