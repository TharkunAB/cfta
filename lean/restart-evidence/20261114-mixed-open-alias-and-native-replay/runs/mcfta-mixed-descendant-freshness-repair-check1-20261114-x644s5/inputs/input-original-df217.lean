-- UNCOMPILED SOURCE DRAFT. Root owns validation.
import MicroCFTA.SourceRecursiveIntersectionKernelCalls
import MicroCFTA.SourceSynthesisCurrentUniverseOwnership
import MicroCFTA.SourceRecursiveIntersectionDomainEquivalence
import MicroCFTA.SourceSynthesisUniversePrefixHeight

/-!
# Cutoff freshness below one actual mixed entry

Strict ordinary-and-union prefix height separates complete operand identities.
The original mixed domain retains only its original seen pair after later
machine extensions. Its original Mu binding still reads the same full record.
-/
namespace MicroCFTA.SourceSynthesisUniverseMixedDescendantFreshness
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel
open SourceSynthesisUniversePrefixHeight (height)

set_option autoImplicit false
section Generic
variable {Symbol Guard : Type}

/-- Closed operands with a control identity have a complete record identity. -/
private theorem closed_reference (value : Value Symbol Guard) (closed : value.free = [])
    (name : Nat) (identified : identity value = some name) :
    SourcePreparedSharedRows.reference value = some name := by
  cases value with
  | empty => simp only [identity, reduceCtorEq] at identified
  | reference own => simp only [Value.free, List.cons_ne_self] at closed
  | node | mu | union =>
      simpa only [identity, SourcePreparedSharedRows.reference] using identified

/-- Equal identities of closed available operands select the same complete physical value. -/
theorem closed_identity_injective (heap : State Symbol Guard) (facts : Facts heap)
    (left right : Value Symbol Guard) (leftAvailable : Available heap left)
    (rightAvailable : Available heap right) (leftClosed : left.free = []) (rightClosed : right.free = [])
    (name : Nat) (leftIdentity : identity left = some name) (rightIdentity : identity right = some name) :
    left = right := by
  have leftRead := SourcePreparedSharedRows.read_identity heap facts left leftAvailable name
    (closed_reference left leftClosed name leftIdentity)
  have rightRead := SourcePreparedSharedRows.read_identity heap facts right rightAvailable name
    (closed_reference right rightClosed name rightIdentity)
  exact Option.some.inj (leftRead.symm.trans rightRead)

/-- Strict prefix descent excludes the ancestor's physical identity. -/
theorem strict_prefix_height_identity_ne (heap : State Symbol Guard) (facts : Facts heap)
    (pattern operand : Value Symbol Guard) (patternAvailable : Available heap pattern)
    (operandAvailable : Available heap operand) (patternClosed : pattern.free = [])
    (operandClosed : operand.free = []) (patternId operandId : Nat)
    (patternIdentity : identity pattern = some patternId) (operandIdentity : identity operand = some operandId)
    (smaller : height operand < height pattern) : operandId ≠ patternId := by
  intro same
  have original : identity operand = some patternId := by rw [operandIdentity, same]
  have equal := closed_identity_injective heap facts pattern operand patternAvailable operandAvailable
    patternClosed operandClosed patternId patternIdentity original
  have sameHeight := congrArg height equal
  omega

private theorem pair_cancel (common left right : Nat) (same : pair common left = pair common right) :
    left = right := by
  have lower := congrArg Prod.fst same
  have upper := congrArg Prod.snd same
  simp only [pair] at lower upper
  omega

private theorem pair_symmetric (left right : Nat) : pair left right = pair right left := by
  simp only [pair, Nat.min_comm, Nat.max_comm]

/-- A strict descendant stays fresh for both operand orders in the original mixed domain. -/
theorem mixed_entry_strict_descendant_fresh
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (universeAvailable : Available state.heap (.mu entry body depth ordinary))
    (pattern : Value Symbol Guard) (patternAvailable : Available state.heap pattern)
    (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter state.domains IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
    let initial : Machine Symbol Guard := ⟨state.heap, entered.2⟩
    ∀ later : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid later → Extension initial later →
      ∀ operand : Value Symbol Guard, Available later.heap operand → operand.free = [] →
      ∀ operandId : Nat, identity operand = some operandId → height operand < height pattern →
      operandId ≠ patternId ∧
      pair entry.identity operandId ≠ pair entry.identity patternId ∧
      pair operandId entry.identity ≠ pair entry.identity patternId ∧
      pair entry.identity operandId ∉ entered.1.key.seen ∧
      pair operandId entry.identity ∉ entered.1.key.seen ∧
      Domain later entered.1 ∧
      lookup later.heap entered.1.key entry.identity = some universeValue := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter state.domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let initial : Machine Symbol Guard := ⟨state.heap, entered.2⟩
  have allocation := SourceRecursiveIntersectionKernel.entered state valid
    IntersectionEmptyDomain.emptyDomain (empty_domain state) universeValue pattern universeAvailable patternAvailable
    entry.identity patternId
  have initialKnown : Domain initial entered.1 := allocation.2.2
  have enteredKey : entered.1.key =
      extend IntersectionEmptyDomain.emptyKey
        ((SourceRecursiveIntersectionEnvironment.bindings universeValue pattern).map Prod.fst)
        (pair entry.identity patternId) :=
    SourceRecursiveIntersectionSchedule.entered_key state.domains valid.2 IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
  intro later laterValid continuation operand operandAvailable operandClosed operandId operandIdentity smaller
  have laterPattern : Available later.heap pattern := continuation.available pattern patternAvailable
  have different := strict_prefix_height_identity_ne later.heap laterValid.1 pattern operand laterPattern
    operandAvailable patternClosed operandClosed patternId operandId patternIdentity operandIdentity smaller
  have directApart : pair entry.identity operandId ≠ pair entry.identity patternId :=
    fun same => different (pair_cancel entry.identity operandId patternId same)
  have reverseApart : pair operandId entry.identity ≠ pair entry.identity patternId := by
    rw [pair_symmetric operandId entry.identity]
    exact directApart
  have fresh : ∀ key : Nat × Nat, key ≠ pair entry.identity patternId → key ∉ entered.1.key.seen := by
    intro key differentKey seen
    rw [enteredKey] at seen
    rcases (extend_seen IntersectionEmptyDomain.emptyKey
      ((SourceRecursiveIntersectionEnvironment.bindings universeValue pattern).map Prod.fst)
      (pair entry.identity patternId) key).mp seen with same | old
    · exact differentKey same
    · simp only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil] at old
  have laterKnown : Domain later entered.1 := initialKnown.grows entered.1 continuation
  have laterUniverse : Available later.heap universeValue := continuation.available universeValue universeAvailable
  have bound : entry.identity ∈ names entered.1.key := by
    rw [enteredKey, extend_names]
    left
    simp [universeValue, SourceRecursiveIntersectionEnvironment.bindings,
      SourceRecursiveIntersectionEnvironment.binder]
  exact ⟨different, directApart, reverseApart, fresh _ directApart, fresh _ reverseApart,
    laterKnown, lookup_mu later.heap laterValid.1 entered.1.key entry body depth ordinary laterUniverse bound⟩

end Generic

open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

/-- The same original build derives U resources and strict-descendant mixed-domain freshness. -/
theorem current_stored_universe_strict_descendant_fresh_after_mixed_entry
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
    universeValue.free = [] ∧
    let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
    let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
    ∀ later : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid later → Extension initial later →
      ∀ operand : Value Symbol Guard, Available later.heap operand → operand.free = [] →
      ∀ operandId : Nat, identity operand = some operandId → height operand < height pattern →
      operandId ≠ patternId ∧
      pair entry.identity operandId ≠ pair entry.identity patternId ∧
      pair operandId entry.identity ≠ pair entry.identity patternId ∧
      pair entry.identity operandId ∉ entered.1.key.seen ∧
      pair operandId entry.identity ∉ entered.1.key.seen ∧
      Domain later entered.1 ∧
      lookup later.heap entered.1.key entry.identity = some universeValue := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  have universeAvailable : Available heap universeValue :=
    facts.cached.nodes key _ (growth.nodeRecords key _ stored)
  have universeClosed : universeValue.free = [] := by
    rcases SourceSynthesisCurrentUniverseOwnership.current_build_single_universe
        lib query signed whole accepted rootValue sourceHeap built with noMu | someMu
    · exact False.elim (noMu key entry body depth ordinary stored)
    · obtain ⟨_owner, _ownerBody, _ownerDepth, _ownerOrdinary, _ownerStored, _ownerAvailable,
          ownerClosed, _ownerReplay, unique⟩ := someMu
      have selected := unique key entry body depth ordinary stored
      change (Value.mu entry body depth ordinary).free = []
      rw [selected]
      exact ownerClosed
  refine ⟨universeClosed, ?_⟩
  exact mixed_entry_strict_descendant_fresh
    (⟨heap, domains⟩ : Machine Symbol Guard) ⟨facts, cacheValid⟩ entry body depth ordinary universeAvailable
    pattern patternAvailable patternClosed patternId patternIdentity

end MicroCFTA.SourceSynthesisUniverseMixedDescendantFreshness
