import MicroCFTA.SourceSynthesisUniverseBodyReferenceControl
import MicroCFTA.SourceRecursiveIntersectionKernelStability

/-!
# The actual off-diagonal cutoff in the original body product

The reference call reads the original Mu. The next Mu call adds the
source diagonal. The repeated body/reference call returns the older
body/Mu cutoff. The unused inner Mu retains that cutoff and the exact
domain cache returned by the diagonal allocation.
-/
set_option autoImplicit false

namespace MicroCFTA.SourceSynthesisUniverseOffDiagonalReferenceControl
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel

variable {Symbol Guard : Type}

/-- Three native steps return the body/Mu cutoff and the exact reached domain cache. -/
theorem execute_ref_self_off_diagonal
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (state : Machine Symbol Guard)
    (facts : Facts state.heap) (cacheValid : Cache.Valid state.domains)
    (universeAvailable : Available state.heap
      (.mu u (.node b rows 0 [.interned u.identity]) depth ordinary))
    (bound : u.identity ∈ SourceRecursiveIntersectionDomain.names domain.key)
    (seen : pair b.identity u.identity ∈ domain.key.seen)
    (fresh : pair u.identity u.identity ∉ domain.key.seen) :
    let universeValue : Value Symbol Guard := .mu u (.node b rows 0 [.interned u.identity]) depth ordinary
    let reference : Value Symbol Guard := .reference (.interned u.identity)
    let entered := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key
      universeValue reference u.identity u.identity
    execute emptyGuard conjoin 3 domain reference reference state =
      .done (repeatedValue (pair b.identity u.identity)) {state with domains := entered.2} := by
  dsimp only
  let universeValue : Value Symbol Guard := .mu u (.node b rows 0 [.interned u.identity]) depth ordinary
  let referenceValue : Value Symbol Guard := .reference (.interned u.identity)
  let bodyValue : Value Symbol Guard := .node b rows 0 [.interned u.identity]
  let entered := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key
    universeValue referenceValue u.identity u.identity
  have different := SourceSynthesisUniverseBodyReferenceControl.body_identity_ne
    u b rows depth ordinary state facts universeAvailable
  have read := SourcePreparedSharedRows.read_identity state.heap facts universeValue universeAvailable u.identity rfl
  have enteredKey := SourceRecursiveIntersectionSchedule.entered_key state.domains cacheValid domain.key
    universeValue referenceValue u.identity u.identity
  have repeated : pair b.identity u.identity ∈ entered.1.key.seen := by
    rw [enteredKey]
    exact (SourceRecursiveIntersectionDomain.extend_seen _ _ _ _).mpr (Or.inr seen)
  have refBranch : decision domain.key referenceValue referenceValue = .leftReference := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      referenceValue, Value.referenceOf, Value.free, fresh,
      SourceRecursiveIntersectionSchedule.reference_interned]
  have tag24 : compare (2 : Nat) 4 = .lt := by decide
  have tag14 : compare (1 : Nat) 4 = .lt := by decide
  have muBranch : decision domain.key universeValue referenceValue = .leftMu := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      universeValue, bodyValue, referenceValue, Value.referenceOf, Value.free, fresh, tag24]
  have repeatedBranch : decision entered.1.key bodyValue referenceValue =
      .repeated (pair b.identity u.identity) := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      bodyValue, referenceValue, Value.referenceOf, Value.free, repeated, tag14]
  have absent : Reference.intersection (pair u.identity u.identity).1 (pair u.identity u.identity).2 ∉
      (repeatedValue (pair b.identity u.identity) : Value Symbol Guard).free := by
    intro member
    have same := List.mem_singleton.mp member
    have parts := Reference.intersection.inj same
    have lower := parts.1
    have upper := parts.2
    simp only [pair, Nat.min_self, Nat.max_self] at lower upper
    apply different
    omega
  change execute emptyGuard conjoin 3 domain referenceValue referenceValue state = _
  rw [execute]
  simp only [onNode, refBranch]
  simp only [SourceRecursiveIntersectionKernel.reference, bound, ite_true, read]
  rw [execute]
  simp only [onNode, muBranch]
  change (execute emptyGuard conjoin 1 entered.1 bodyValue referenceValue
    {state with domains := entered.2}).bind _ = _
  rw [execute]
  simp only [onNode, repeatedBranch]
  simpa only [Result.bind, SourceRecursiveIntersectionMaybeMu.unused _ _ state.heap absent, construction]

/-- The same exact reached machine is retained at the body row caller's eight-step bound. -/
theorem execute_ref_self_off_diagonal_eight
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (state : Machine Symbol Guard)
    (facts : Facts state.heap) (cacheValid : Cache.Valid state.domains)
    (universeAvailable : Available state.heap
      (.mu u (.node b rows 0 [.interned u.identity]) depth ordinary))
    (bound : u.identity ∈ SourceRecursiveIntersectionDomain.names domain.key)
    (seen : pair b.identity u.identity ∈ domain.key.seen)
    (fresh : pair u.identity u.identity ∉ domain.key.seen) :
    let universeValue : Value Symbol Guard := .mu u (.node b rows 0 [.interned u.identity]) depth ordinary
    let reference : Value Symbol Guard := .reference (.interned u.identity)
    let entered := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key
      universeValue reference u.identity u.identity
    execute emptyGuard conjoin 8 domain reference reference state =
      .done (repeatedValue (pair b.identity u.identity)) {state with domains := entered.2} := by
  have done := execute_ref_self_off_diagonal emptyGuard conjoin u b rows depth ordinary
    domain state facts cacheValid universeAvailable bound seen fresh
  exact (execute_stable emptyGuard conjoin 3 5 domain
    (.reference (.interned u.identity)) (.reference (.interned u.identity)) state
    (by rw [done]; trivial)).trans done

end MicroCFTA.SourceSynthesisUniverseOffDiagonalReferenceControl

#print axioms MicroCFTA.SourceSynthesisUniverseOffDiagonalReferenceControl.execute_ref_self_off_diagonal
#print axioms MicroCFTA.SourceSynthesisUniverseOffDiagonalReferenceControl.execute_ref_self_off_diagonal_eight
