import MicroCFTA.SourceRecursiveIntersectionReplay

/-!
# Completed recursive memo values from actual executions

Completed entries retain an actual guarded recursive execution and later
constructor/domain growth. Checked machine triples identify the original
complete request. A hit therefore has concrete exact replay. Native pending
publication, recursive memo scheduling, and edge memo entries remain separate.
-/
namespace MicroCFTA.SourceRecursiveIntersectionMemo
open Cache InternedConstructorTemplates InternedProbeProvenance InternedFreshProbeKeys
open InternedBinderProtocol IntersectionFlatMemoKeyDomain IntersectionFlatMemoKey
open SourceRecursiveIntersectionKernel

/-- The actual source memo key retains shifted domain identity and ordered tagged operands. -/
def requestKey (width : Nat) (domain : Interned DomainKey) (left right : Value Symbol Guard) : Option (Triple width) :=
  sourceKey width domain left.referenceOf right.referenceOf

/-- Checked requests retain the source nonnegative first-key range and both complete operand key bounds. -/
def KeySafe (width : Nat) (domain : Interned DomainKey) (left right : Value Symbol Guard) : Prop :=
  0 < width ∧ domain.identity < 2 ^ (width - 1) ∧
    ∃ first second, input left.referenceOf = some first ∧ input right.referenceOf = some second ∧
      Safe width first ∧ Safe width second

/-- The signed nonnegative source domain range also gives injective unsigned machine conversion. -/
theorem domain_fits (width identity : Nat) (bounded : identity < 2 ^ (width - 1)) : identity < 2 ^ width :=
  Nat.lt_of_lt_of_le bounded (Nat.pow_le_pow_right (by omega) (Nat.sub_le width 1))

/-- Swapping operands retains each source machine bound without normalizing the ordered request key. -/
theorem KeySafe.swap (safe : KeySafe width domain left right) : KeySafe width domain right left := by
  obtain ⟨positive, bounded, first, second, firstInput, secondInput, firstSafe, secondSafe⟩ := safe
  exact ⟨positive, bounded, second, first, secondInput, firstInput, secondSafe, firstSafe⟩

/-- A checked actual source request satisfies the nonnegative native publication first-key contract. -/
theorem requestKey_nonnegative (width : Nat) (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (safe : KeySafe width domain left right) (key : Triple width) (request : requestKey width domain left right = some key) :
    0 ≤ key.1.toInt := by
  obtain ⟨positive, bounded, first, second, firstInput, secondInput, _, _⟩ := safe
  unfold requestKey at request
  rw [sourceKey_complete width domain _ _ first second firstInput secondInput] at request
  have same := Option.some.inj request
  rw [← same]
  simp only [flatKey, domain_word_nonnegative width positive domain.identity bounded]
  omega

/-- Equal checked native triples identify the same complete operands and canonical source domain. -/
theorem requestKey_injective (width : Nat) (state : Machine Symbol Guard) (valid : Valid state)
    (firstDomain secondDomain : Interned DomainKey) (firstLeft firstRight secondLeft secondRight : Value Symbol Guard)
    (firstKnown : Domain state firstDomain) (secondKnown : Domain state secondDomain)
    (firstSafe : KeySafe width firstDomain firstLeft firstRight) (secondSafe : KeySafe width secondDomain secondLeft secondRight)
    (firstLeftAvailable : Available state.heap firstLeft) (firstRightAvailable : Available state.heap firstRight)
    (secondLeftAvailable : Available state.heap secondLeft) (secondRightAvailable : Available state.heap secondRight)
    (same : requestKey width firstDomain firstLeft firstRight = requestKey width secondDomain secondLeft secondRight) :
    (firstDomain, firstLeft, firstRight) = (secondDomain, secondLeft, secondRight) := by
  obtain ⟨_, firstFits, first, second, firstInput, secondInput, firstBound, secondBound⟩ := firstSafe
  obtain ⟨_, secondFits, third, fourth, thirdInput, fourthInput, thirdBound, fourthBound⟩ := secondSafe
  unfold requestKey at same
  rw [sourceKey_complete width firstDomain _ _ first second firstInput secondInput,
    sourceKey_complete width secondDomain _ _ third fourth thirdInput fourthInput] at same
  have components := Prod.mk.inj ((IntersectionEmptyDomain.flatKey_exact width state.domains valid.2
    firstDomain.key secondDomain.key firstDomain secondDomain firstKnown.represented secondKnown.represented
    (domain_fits width _ firstFits) (domain_fits width _ secondFits) first second third fourth
    firstBound secondBound thirdBound fourthBound).mp (Option.some.inj same))
  have operandTags := Prod.mk.inj components.2
  have domainIdentities := (IntersectionEmptyDomain.identity_exact state.domains valid.2 _ _ _ _
    firstKnown.represented secondKnown.represented).mpr components.1
  have domains : firstDomain = secondDomain := by
    cases firstDomain
    cases secondDomain
    simp only [Interned.mk.injEq]
    exact ⟨domainIdentities, components.1⟩
  have leftReferences := input_injective _ _ first third firstInput thirdInput operandTags.1
  have rightReferences := input_injective _ _ second fourth secondInput fourthInput operandTags.2
  have left := resident_reference_injective state.heap valid.1.coherent firstLeft secondLeft
    firstLeftAvailable.resident secondLeftAvailable.resident leftReferences
  have right := resident_reference_injective state.heap valid.1.coherent firstRight secondRight
    firstRightAvailable.resident secondRightAvailable.resident rightReferences
  rw [domains, left, right]

/-- A source swap requests a different memo key unless the complete operands are equal. -/
theorem swapped_key_eq_iff (width : Nat) (state : Machine Symbol Guard) (valid : Valid state)
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (known : Domain state domain)
    (safe : KeySafe width domain left right) (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right) :
    requestKey width domain left right = requestKey width domain right left ↔ left = right := by
  constructor
  · intro equal
    have same := Prod.mk.inj (requestKey_injective width state valid domain domain left right right left known known
      safe safe.swap leftAvailable rightAvailable rightAvailable leftAvailable equal)
    exact (Prod.mk.inj same.2).1
  · intro equal
    rw [equal]

/-- One typed completed table stores the actual physical values for checked native triples. -/
abbrev Memo (width : Nat) (Symbol Guard : Type) := Cache.Table (Triple width) (Value Symbol Guard)

/-- A completed memo result has an actual full recursive source execution and retained cache history. -/
def Produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (domain : Interned DomainKey) (left right value : Value Symbol Guard) : Prop :=
  ∃ (before final : Machine Symbol Guard), ∃ fuel,
    SourceRecursiveIntersectionKernel.Valid before ∧ Domain before domain ∧ Available before.heap left ∧ Available before.heap right ∧
    execute emptyGuard conjoin fuel domain left right before = .done value final ∧ Extension final state

/-- Each completed table entry retains its actual checked source request and concrete execution. -/
def MemoValid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (memo : Memo width Symbol Guard) : Prop :=
  ∀ key value, memo key = some value → ∃ domain left right,
    requestKey width domain left right = some key ∧ KeySafe width domain left right ∧
      Produced emptyGuard conjoin state domain left right value

/-- Every actual completed kernel call supplies concrete memo-result provenance at its exact returned state. -/
theorem produced_here [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (domain : Interned DomainKey) (left right : Value Symbol Guard) (before final : Machine Symbol Guard)
    (valid : Valid before) (known : Domain before domain) (leftAvailable : Available before.heap left) (rightAvailable : Available before.heap right)
    (value : Value Symbol Guard) (done : execute emptyGuard conjoin fuel domain left right before = .done value final) :
    Produced emptyGuard conjoin final domain left right value :=
  ⟨before, final, fuel, valid, known, leftAvailable, rightAvailable, done, .refl final⟩

/-- Later source effects retain each concrete completed recursive execution. -/
theorem produced_grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (before after : Machine Symbol Guard) (growth : Extension before after) (domain : Interned DomainKey) (left right value : Value Symbol Guard)
    (produced : Produced emptyGuard conjoin before domain left right value) : Produced emptyGuard conjoin after domain left right value := by
  obtain ⟨source, final, fuel, valid, known, leftAvailable, rightAvailable, done, earlier⟩ := produced
  exact ⟨source, final, fuel, valid, known, leftAvailable, rightAvailable, done, earlier.trans growth⟩

/-- Concrete full execution derives the current original domain, operand availability, and result availability. -/
theorem produced_spec [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (domain : Interned DomainKey) (left right value : Value Symbol Guard)
    (produced : Produced emptyGuard conjoin state domain left right value) :
    Domain state domain ∧ Available state.heap left ∧ Available state.heap right ∧ Available state.heap value := by
  obtain ⟨before, final, fuel, valid, known, leftAvailable, rightAvailable, done, later⟩ := produced
  have checked := execute_checked emptyGuard conjoin fuel domain left right before valid known leftAvailable rightAvailable
  have earlier : Extension before final := by simpa only [done, Result.state] using checked.extension
  have growth := earlier.trans later
  exact ⟨known.grows domain growth, growth.available left leftAvailable, growth.available right rightAvailable,
    later.available value (checked.result value final done)⟩

/-- Actual completed provenance derives exact replay at a finite bound and every larger bound. -/
theorem produced_replay [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (domain : Interned DomainKey) (left right value : Value Symbol Guard)
    (produced : Produced emptyGuard conjoin state domain left right value) :
    ∃ fuel, ∀ extra, execute emptyGuard conjoin (fuel + extra) domain left right state = .done value state := by
  obtain ⟨before, final, fuel, valid, known, leftAvailable, rightAvailable, done, growth⟩ := produced
  exact ⟨fuel, fun extra => execute_larger_replay emptyGuard conjoin fuel extra domain left right before state
    valid known leftAvailable rightAvailable value final done growth⟩

/-- The empty completed table has no assumed source output equations. -/
theorem memo_empty [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) : MemoValid width emptyGuard conjoin state (fun _ => none) := by
  intro key value impossible
  cases impossible

/-- Completed memo provenance survives all later physical and domain effects. -/
theorem memo_grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (before after : Machine Symbol Guard) (growth : Extension before after) (memo : Memo width Symbol Guard)
    (valid : MemoValid width emptyGuard conjoin before memo) : MemoValid width emptyGuard conjoin after memo := by
  intro key value stored
  obtain ⟨domain, left, right, request, safe, produced⟩ := valid key value stored
  exact ⟨domain, left, right, request, safe, produced_grows emptyGuard conjoin before after growth domain left right value produced⟩

/-- A checked native memo hit reuses the same complete physical request and its concrete stable recursive execution. -/
theorem memo_hit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (valid : Valid state) (memo : Memo width Symbol Guard) (memoValid : MemoValid width emptyGuard conjoin state memo)
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (known : Domain state domain) (safe : KeySafe width domain left right)
    (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right) (key : Triple width) (value : Value Symbol Guard)
    (request : requestKey width domain left right = some key) (stored : memo key = some value) :
    Available state.heap value ∧ ∃ fuel, ∀ extra, execute emptyGuard conjoin (fuel + extra) domain left right state = .done value state := by
  obtain ⟨original, first, second, oldRequest, oldSafe, produced⟩ := memoValid key value stored
  have checked := produced_spec emptyGuard conjoin state original first second value produced
  have same := Prod.mk.inj (requestKey_injective width state valid original domain first second left right checked.1 known oldSafe safe
    checked.2.1 checked.2.2.1 leftAvailable rightAvailable (oldRequest.trans request.symm))
  have operands := Prod.mk.inj same.2
  rcases same.1 with rfl
  rcases operands.1 with rfl
  rcases operands.2 with rfl
  exact ⟨checked.2.2.2, produced_replay emptyGuard conjoin state original first second value produced⟩

/-- First-writer completed insertion retains concrete execution provenance. -/
theorem memo_insert [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (memo : Memo width Symbol Guard) (valid : MemoValid width emptyGuard conjoin state memo)
    (domain : Interned DomainKey) (left right value : Value Symbol Guard) (key : Triple width)
    (request : requestKey width domain left right = some key) (safe : KeySafe width domain left right)
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

end MicroCFTA.SourceRecursiveIntersectionMemo
