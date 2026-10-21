import MicroCFTA.SourceRecursiveIntersectionMemo

/-!
# Completed guarded edge memo provenance

Actual guarded edge executions supply completed native edge entries. The
key retains shifted domain identity and ordered raw edge identities. Hits
reuse the same physical records and exact finite execution after growth.
Pending native publication remains separate from completed observations.
-/
namespace MicroCFTA.SourceRecursiveIntersectionEdgeMemo
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel

/-- The source edge memo uses raw edge identities, without node tags. -/
def requestKey (width : Nat) (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) : Triple width :=
  edgeKey width domain left.entry.identity right.entry.identity

/-- Source edge requests retain the nonnegative first key and injective raw identity bounds. -/
def KeySafe (width : Nat) (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) : Prop :=
  0 < width ∧ domain.identity < 2 ^ (width - 1) ∧ left.entry.identity < 2 ^ width ∧ right.entry.identity < 2 ^ width

/-- Reversed edge requests retain the same source machine bounds. -/
theorem KeySafe.swap (safe : KeySafe width domain left right) : KeySafe width domain right left :=
  ⟨safe.1, safe.2.1, safe.2.2.2, safe.2.2.1⟩

/-- Actual checked edge keys satisfy the native publication first-key contract. -/
theorem requestKey_nonnegative (width : Nat) (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard)
    (safe : KeySafe width domain left right) : 0 ≤ (requestKey width domain left right).1.toInt := by
  simp only [requestKey, edgeKey, domain_word_nonnegative width safe.1 domain.identity safe.2.1]
  omega

/-- Equal checked edge triples identify the same original domain and complete physical row payloads. -/
theorem requestKey_injective (width : Nat) (state : Machine Symbol Guard) (valid : Valid state)
    (firstDomain secondDomain : Interned DomainKey) (firstLeft firstRight secondLeft secondRight : EdgeValue Symbol Guard)
    (firstKnown : Domain state firstDomain) (secondKnown : Domain state secondDomain)
    (firstSafe : KeySafe width firstDomain firstLeft firstRight) (secondSafe : KeySafe width secondDomain secondLeft secondRight)
    (firstLeftResident : EdgeResident state.heap firstLeft) (firstRightResident : EdgeResident state.heap firstRight)
    (secondLeftResident : EdgeResident state.heap secondLeft) (secondRightResident : EdgeResident state.heap secondRight)
    (same : requestKey width firstDomain firstLeft firstRight = requestKey width secondDomain secondLeft secondRight) :
    (firstDomain, firstLeft, firstRight) = (secondDomain, secondLeft, secondRight) := by
  have components := Prod.mk.inj ((IntersectionEmptyDomain.edgeKey_exact width state.domains valid.2
    firstDomain.key secondDomain.key firstDomain secondDomain firstKnown.represented secondKnown.represented
    (SourceRecursiveIntersectionMemo.domain_fits width _ firstSafe.2.1)
    (SourceRecursiveIntersectionMemo.domain_fits width _ secondSafe.2.1)
    firstLeft.entry.identity firstRight.entry.identity secondLeft.entry.identity secondRight.entry.identity
    firstSafe.2.2.1 firstSafe.2.2.2 secondSafe.2.2.1 secondSafe.2.2.2).mp same)
  have identities := Prod.mk.inj components.2
  have domainIdentities := (IntersectionEmptyDomain.identity_exact state.domains valid.2 _ _ _ _
    firstKnown.represented secondKnown.represented).mpr components.1
  have domains : firstDomain = secondDomain := by
    cases firstDomain
    cases secondDomain
    simp only [Interned.mk.injEq]
    exact ⟨domainIdentities, components.1⟩
  have left := edge_identity_unique state.heap valid.1.coherent firstLeft secondLeft firstLeftResident secondLeftResident identities.1
  have right := edge_identity_unique state.heap valid.1.coherent firstRight secondRight firstRightResident secondRightResident identities.2
  rw [domains, left, right]

/-- Swapping distinct physical rows requests a distinct checked native edge key. -/
theorem swapped_key_eq_iff (width : Nat) (state : Machine Symbol Guard) (valid : Valid state)
    (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) (known : Domain state domain)
    (safe : KeySafe width domain left right) (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right) :
    requestKey width domain left right = requestKey width domain right left ↔ left = right := by
  constructor
  · intro equal
    have same := Prod.mk.inj (requestKey_injective width state valid domain domain left right right left known known
      safe safe.swap leftResident rightResident rightResident leftResident equal)
    exact (Prod.mk.inj same.2).1
  · intro equal
    rw [equal]

/-- One typed completed edge table retains physical source edge records. -/
abbrev Memo (width : Nat) (Symbol Guard : Type) := Cache.Table (Triple width) (EdgeValue Symbol Guard)

/-- Completed edge entries retain an actual guarded source execution and later physical/domain growth. -/
def Produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (domain : Interned DomainKey) (left right value : EdgeValue Symbol Guard) : Prop :=
  ∃ (before final : Machine Symbol Guard), ∃ fuel,
    SourceRecursiveIntersectionKernel.Valid before ∧ Domain before domain ∧ EdgeResident before.heap left ∧ EdgeResident before.heap right ∧
      edge emptyGuard conjoin (execute emptyGuard conjoin fuel domain) left right before = .done value final ∧ Extension final state

/-- Each completed native edge entry retains checked original inputs and concrete guarded execution. -/
def MemoValid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (memo : Memo width Symbol Guard) : Prop :=
  ∀ key value, memo key = some value → ∃ domain left right,
    requestKey width domain left right = key ∧ KeySafe width domain left right ∧ Produced emptyGuard conjoin state domain left right value

/-- Actual edge completion constructs memo provenance at the exact returned source state. -/
theorem produced_here [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) (before final : Machine Symbol Guard)
    (valid : Valid before) (known : Domain before domain) (leftResident : EdgeResident before.heap left) (rightResident : EdgeResident before.heap right)
    (value : EdgeValue Symbol Guard)
    (done : edge emptyGuard conjoin (execute emptyGuard conjoin fuel domain) left right before = .done value final) :
    Produced emptyGuard conjoin final domain left right value :=
  ⟨before, final, fuel, valid, known, leftResident, rightResident, done, .refl final⟩

/-- Later source effects preserve actual completed edge histories. -/
theorem produced_grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (before after : Machine Symbol Guard) (growth : Extension before after) (domain : Interned DomainKey) (left right value : EdgeValue Symbol Guard)
    (produced : Produced emptyGuard conjoin before domain left right value) : Produced emptyGuard conjoin after domain left right value := by
  obtain ⟨source, final, fuel, valid, known, leftResident, rightResident, done, earlier⟩ := produced
  exact ⟨source, final, fuel, valid, known, leftResident, rightResident, done, earlier.trans growth⟩

/-- Concrete guarded execution derives the current original domain and complete resident edge payloads. -/
theorem produced_spec [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (domain : Interned DomainKey) (left right value : EdgeValue Symbol Guard)
    (produced : Produced emptyGuard conjoin state domain left right value) :
    Domain state domain ∧ EdgeResident state.heap left ∧ EdgeResident state.heap right ∧ EdgeResident state.heap value := by
  obtain ⟨before, final, fuel, valid, known, leftResident, rightResident, done, later⟩ := produced
  have checked := edge_checked emptyGuard conjoin _ (execute_checked emptyGuard conjoin fuel) domain left right before valid known leftResident rightResident
  have earlier : Extension before final := by simpa only [done, Result.state] using checked.extension
  have growth := earlier.trans later
  exact ⟨known.grows domain growth, edge_grows _ _ growth.heap left leftResident, edge_grows _ _ growth.heap right rightResident,
    edge_grows _ _ later.heap value (checked.result value final done)⟩

/-- Concrete edge provenance derives exact replay at a finite child bound and every larger child bound. -/
theorem produced_replay [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (domain : Interned DomainKey) (left right value : EdgeValue Symbol Guard)
    (produced : Produced emptyGuard conjoin state domain left right value) :
    ∃ fuel, ∀ extra, edge emptyGuard conjoin (execute emptyGuard conjoin (fuel + extra) domain) left right state = .done value state := by
  obtain ⟨before, final, fuel, valid, known, leftResident, rightResident, done, growth⟩ := produced
  have repeated := edge_replay emptyGuard conjoin _ (execute_checked emptyGuard conjoin fuel)
    (execute_replay emptyGuard conjoin fuel) domain left right before state valid known leftResident rightResident value final done growth
  refine ⟨fuel, ?_⟩
  intro extra
  have equal := edge_congr emptyGuard conjoin (execute emptyGuard conjoin fuel domain)
    (execute emptyGuard conjoin (fuel + extra) domain)
    (fun left right current reached => execute_stable emptyGuard conjoin fuel extra domain left right current reached)
    left right state (by rw [repeated]; trivial)
  exact equal.trans repeated

/-- An empty edge memo table has no assumed output correspondence. -/
theorem memo_empty [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) : MemoValid width emptyGuard conjoin state (fun _ => none) := by
  intro key value impossible
  cases impossible

/-- Completed edge memo provenance survives later constructor and domain effects. -/
theorem memo_grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (before after : Machine Symbol Guard) (growth : Extension before after) (memo : Memo width Symbol Guard)
    (valid : MemoValid width emptyGuard conjoin before memo) : MemoValid width emptyGuard conjoin after memo := by
  intro key value stored
  obtain ⟨domain, left, right, request, safe, produced⟩ := valid key value stored
  exact ⟨domain, left, right, request, safe, produced_grows emptyGuard conjoin before after growth domain left right value produced⟩

/-- A checked native edge hit has concrete resident output and stable actual guarded replay. -/
theorem memo_hit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (valid : Valid state) (memo : Memo width Symbol Guard) (memoValid : MemoValid width emptyGuard conjoin state memo)
    (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) (known : Domain state domain) (safe : KeySafe width domain left right)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right) (key : Triple width) (value : EdgeValue Symbol Guard)
    (request : requestKey width domain left right = key) (stored : memo key = some value) :
    EdgeResident state.heap value ∧ ∃ fuel, ∀ extra,
      edge emptyGuard conjoin (execute emptyGuard conjoin (fuel + extra) domain) left right state = .done value state := by
  obtain ⟨original, first, second, oldRequest, oldSafe, produced⟩ := memoValid key value stored
  have checked := produced_spec emptyGuard conjoin state original first second value produced
  have same := Prod.mk.inj (requestKey_injective width state valid original domain first second left right checked.1 known oldSafe safe
    checked.2.1 checked.2.2.1 leftResident rightResident (oldRequest.trans request.symm))
  have operands := Prod.mk.inj same.2
  rcases same.1 with rfl
  rcases operands.1 with rfl
  rcases operands.2 with rfl
  exact ⟨checked.2.2.2, produced_replay emptyGuard conjoin state original first second value produced⟩

/-- First-writer edge insertion retains actual completed guarded execution provenance. -/
theorem memo_insert [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (memo : Memo width Symbol Guard) (valid : MemoValid width emptyGuard conjoin state memo)
    (domain : Interned DomainKey) (left right value : EdgeValue Symbol Guard) (key : Triple width)
    (request : requestKey width domain left right = key) (safe : KeySafe width domain left right)
    (produced : Produced emptyGuard conjoin state domain left right value) :
    MemoValid width emptyGuard conjoin state (Cache.keepFirst memo key value) := by
  intro actual result stored
  cases found : memo key with
  | some original => exact valid actual result (by simpa only [Cache.keepFirst, found] using stored)
  | none =>
      by_cases same : actual = key
      · subst actual
        have equal : result = value := by simpa [Cache.keepFirst, found, Cache.put] using stored.symm
        subst result
        exact ⟨domain, left, right, request, safe, produced⟩
      · exact valid actual result (by simpa [Cache.keepFirst, found, Cache.put, same] using stored)

end MicroCFTA.SourceRecursiveIntersectionEdgeMemo
