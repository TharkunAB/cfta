import MicroCFTA.SourceSynthesisUniverseReferenceControl
import MicroCFTA.SourceSynthesisUniverseBody

/-!
# Actual universe-body/reference control

The first domain is the actual open-reference/Mu diagonal allocation.
The next Mu call adds the independently sorted body/binder identity pair.
Coherent stored records derive every pair exclusion used below.
The ordinary body product and outer Mu reconstruction remain separate.
-/
namespace MicroCFTA.SourceSynthesisUniverseBodyReferenceControl
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedProbeProvenance InternedNestedFacts InternedFreshProbeKeys
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionControl
open SourceRecursiveIntersectionDomain SourceRecursiveIntersectionKernel

variable {Symbol Guard : Type}

private abbrev bodyValue (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) : Value Symbol Guard :=
  .node b rows 0 [.interned u.identity]

private abbrev muValue (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) : Value Symbol Guard :=
  .mu u (bodyValue u b rows) depth ordinary

private abbrev refValue (u : Interned NodeKey) : Value Symbol Guard :=
  .reference (Reference.interned u.identity)

/-- Reuse the exact domain allocation of the preceding reference/Mu control theorem. -/
abbrev first (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) :=
  SourceSynthesisUniverseReferenceControl.diagonal u (bodyValue u b rows) depth ordinary state

/-- The first allocation changes the domain cache and retains the constructor heap. -/
abbrev firstState (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) : Machine Symbol Guard :=
  {state with domains := (first u b rows depth ordinary state).2}

/-- The actual right-Mu call binds U again and inserts the sorted pair of b and u. -/
def second (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) :=
  SourceRecursiveIntersectionEnvironment.enter (first u b rows depth ordinary state).2
    (first u b rows depth ordinary state).1.key (bodyValue u b rows) (muValue u b rows depth ordinary)
    b.identity u.identity

/-- The second allocation also retains the exact original constructor heap. -/
abbrev secondState (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) : Machine Symbol Guard :=
  {state with domains := (second u b rows depth ordinary state).2}

/-- A stored ordinary body and its Mu cannot share a coherent canonical identity. -/
theorem body_identity_ne (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (facts : Facts state.heap)
    (available : Available state.heap (muValue u b rows depth ordinary)) : b.identity ≠ u.identity := by
  have child : Available state.heap (bodyValue u b rows) :=
    available.children _ (by simp [children])
  intro same
  have impossible := resident_identity_unique state.heap facts.coherent
    (bodyValue u b rows) (muValue u b rows depth ordinary)
    child.resident available.resident b u rfl rfl same
  cases impossible

/-- The first entered cache is valid even when its domain was already interned. -/
theorem first_valid (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (valid : Cache.Valid state.domains) :
    Cache.Valid (first u b rows depth ordinary state).2 :=
  (IntersectionEmptyDomain.make_correct state.domains valid _).1

/-- The first actual domain has exactly its inserted diagonal cutoff. -/
theorem first_seen (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (valid : Cache.Valid state.domains)
    (key : Nat × Nat) : key ∈ (first u b rows depth ordinary state).1.key.seen ↔ key = pair u.identity u.identity := by
  rw [SourceSynthesisUniverseReferenceControl.diagonal_key u (bodyValue u b rows) depth ordinary state valid]
  simp [extend_seen, IntersectionEmptyDomain.emptyKey]

private theorem entered_seen (cache : Cache.State DomainKey) (valid : Cache.Valid cache) (source : DomainKey)
    (left right : Value Symbol Guard) (i j : Nat) (key : Nat × Nat) :
    key ∈ (SourceRecursiveIntersectionEnvironment.enter cache source left right i j).1.key.seen ↔
      key = pair i j ∨ key ∈ source.seen := by
  rw [SourceRecursiveIntersectionSchedule.entered_key cache valid source left right i j]
  exact extend_seen _ _ _ _

/-- The second actual domain has the new symmetric pair and the old diagonal only. -/
theorem second_seen (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (valid : Cache.Valid state.domains)
    (key : Nat × Nat) : key ∈ (second u b rows depth ordinary state).1.key.seen ↔
      key = pair b.identity u.identity ∨ key = pair u.identity u.identity := by
  rw [second, entered_seen _ (first_valid u b rows depth ordinary state valid),
    first_seen u b rows depth ordinary state valid]

private theorem pair_diagonal (left right target : Nat) (same : pair left right = pair target target) :
    left = target ∧ right = target := by
  have lower := congrArg Prod.fst same
  have upper := congrArg Prod.snd same
  simp only [pair, Nat.min_self, Nat.max_self] at lower upper
  omega

private theorem first_pair_absent (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (valid : Cache.Valid state.domains)
    (different : b.identity ≠ u.identity) :
    pair b.identity u.identity ∉ (first u b rows depth ordinary state).1.key.seen := by
  intro member
  exact different (pair_diagonal _ _ _ ((first_seen u b rows depth ordinary state valid _).mp member)).1

/-- The open body/reference request reaches right-reference lookup in the actual first domain. -/
theorem body_reference_branch (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (facts : Facts state.heap)
    (valid : Cache.Valid state.domains) (available : Available state.heap (muValue u b rows depth ordinary)) :
    decision (first u b rows depth ordinary state).1.key (bodyValue u b rows) (refValue u) = .rightReference := by
  have absent := first_pair_absent u b rows depth ordinary state valid
    (body_identity_ne u b rows depth ordinary state facts available)
  have tagOrder : compare (1 : Nat) 4 = .lt := by decide
  simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
    Value.referenceOf, Value.free, absent, tagOrder]

/-- The source lookup restores U in the same first-domain machine before any Mu work. -/
theorem body_reference [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (depth ordinary : Value Symbol Guard)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard →
      Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (state : Machine Symbol Guard) (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (available : Available state.heap (muValue u b rows depth ordinary)) :
    onNode emptyGuard conjoin call (first u b rows depth ordinary state).1 (bodyValue u b rows) (refValue u)
      (firstState u b rows depth ordinary state) =
      call (first u b rows depth ordinary state).1 (bodyValue u b rows) (muValue u b rows depth ordinary)
        (firstState u b rows depth ordinary state) := by
  simp only [onNode, body_reference_branch u b rows depth ordinary state facts valid available]
  exact SourceSynthesisUniverseReferenceControl.reference_entered u (bodyValue u b rows) depth ordinary
    call state facts valid available (bodyValue u b rows) false

/-- Node sorts before Mu, and the actual first domain has not cut off this pair. -/
theorem body_mu_branch (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (facts : Facts state.heap)
    (valid : Cache.Valid state.domains) (available : Available state.heap (muValue u b rows depth ordinary)) :
    decision (first u b rows depth ordinary state).1.key (bodyValue u b rows) (muValue u b rows depth ordinary) = .rightMu := by
  have absent := first_pair_absent u b rows depth ordinary state valid
    (body_identity_ne u b rows depth ordinary state facts available)
  have tagOrder : compare (1 : Nat) 2 = .lt := by decide
  simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
    Value.referenceOf, Value.free, absent, tagOrder]

/-- The actual body/Mu request selects the source Mu continuation, without swapping its operands. -/
theorem body_mu [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (depth ordinary : Value Symbol Guard)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard →
      Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (state : Machine Symbol Guard) (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (available : Available state.heap (muValue u b rows depth ordinary)) :
    onNode emptyGuard conjoin call (first u b rows depth ordinary state).1
      (bodyValue u b rows) (muValue u b rows depth ordinary) (firstState u b rows depth ordinary state) =
      mu call (first u b rows depth ordinary state).1 (bodyValue u b rows) (muValue u b rows depth ordinary)
        (firstState u b rows depth ordinary state) := by
  simp only [onNode, body_mu_branch u b rows depth ordinary state facts valid available]

/-- Two real steps expose B/B in the actual second domain and retain its optional-Mu continuation. -/
theorem execute_body_reference [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (depth ordinary : Value Symbol Guard)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (state : Machine Symbol Guard) (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (available : Available state.heap (muValue u b rows depth ordinary)) :
    execute emptyGuard conjoin (fuel + 2) (first u b rows depth ordinary state).1
      (bodyValue u b rows) (refValue u) (firstState u b rows depth ordinary state) =
      (execute emptyGuard conjoin fuel (second u b rows depth ordinary state).1
        (bodyValue u b rows) (bodyValue u b rows) (secondState u b rows depth ordinary state)).bind
        (fun value after => construction
          (SourceRecursiveIntersectionMaybeMu.maybeMu (pair b.identity u.identity) value after.heap) after) := by
  rw [execute, body_reference u b rows depth ordinary emptyGuard conjoin _ state facts valid available,
    execute, body_mu u b rows depth ordinary emptyGuard conjoin _ state facts valid available]
  rfl

/-- The actual second domain cannot contain the distinct body's own diagonal. -/
theorem body_diagonal_branch (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (facts : Facts state.heap)
    (valid : Cache.Valid state.domains) (available : Available state.heap (muValue u b rows depth ordinary)) :
    decision (second u b rows depth ordinary state).1.key (bodyValue u b rows) (bodyValue u b rows) = .ordinary := by
  have different := body_identity_ne u b rows depth ordinary state facts available
  have absent : pair b.identity b.identity ∉ (second u b rows depth ordinary state).1.key.seen := by
    intro member
    rcases (second_seen u b rows depth ordinary state valid _).mp member with new | old
    · exact different (pair_diagonal _ _ _ new.symm).2.symm
    · exact different (pair_diagonal _ _ _ old).1
  simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
    Value.referenceOf, Value.free, absent]

/-- The next actual request is the ordinary equal-symbol edge product in the second machine. -/
theorem body_diagonal_onNode [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (depth ordinary : Value Symbol Guard)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard →
      Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (state : Machine Symbol Guard) (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (available : Available state.heap (muValue u b rows depth ordinary)) :
    onNode emptyGuard conjoin call (second u b rows depth ordinary state).1
      (bodyValue u b rows) (bodyValue u b rows) (secondState u b rows depth ordinary state) =
      node emptyGuard conjoin (call (second u b rows depth ordinary state).1) rows rows
        (secondState u b rows depth ordinary state) := by
  simp only [onNode, body_diagonal_branch u b rows depth ordinary state facts valid available]

/-- Actual universe-body readback supplies all branch premises without an identity-order assumption. -/
theorem shaped_branches (top : Guard) (catalog : List (String × Nat)) (u : Interned NodeKey)
    (body depth ordinary : Value String Guard) (state : Machine String Guard) (facts : Facts state.heap)
    (valid : Cache.Valid state.domains) (available : Available state.heap (.mu u body depth ordinary))
    (shape : SourceSynthesisUniverseBody.Shape top catalog (.interned u.identity) body) :
    ∃ b rows, body = .node b rows 0 [.interned u.identity] ∧ b.identity ≠ u.identity ∧
      decision (first u b rows depth ordinary state).1.key body (refValue u) = .rightReference ∧
      decision (first u b rows depth ordinary state).1.key body (.mu u body depth ordinary) = .rightMu ∧
      decision (second u b rows depth ordinary state).1.key body body = .ordinary := by
  obtain ⟨b, marker, arrow, rest, same, _⟩ := shape
  subst body
  refine ⟨b, _, rfl, body_identity_ne u b _ depth ordinary state facts available,
    body_reference_branch u b _ depth ordinary state facts valid available,
    body_mu_branch u b _ depth ordinary state facts valid available,
    body_diagonal_branch u b _ depth ordinary state facts valid available⟩

end MicroCFTA.SourceSynthesisUniverseBodyReferenceControl
