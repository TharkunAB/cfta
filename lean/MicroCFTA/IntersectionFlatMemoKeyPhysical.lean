import MicroCFTA.IntersectionFlatMemoKeyDomain
import MicroCFTA.InternedNestedFacts

/-!
# Flat memo keys of available physical source records

The actual issued node counter supplies a uniform safe range. Coherent
resident records then connect key equality with complete source payloads.
No bound on the runtime identity supply is inferred from finite typing.
-/
namespace MicroCFTA.IntersectionFlatMemoKeyPhysical
open InternedConstructorTemplates InternedBinderProtocol InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedFreshProbeKeys
open IntersectionFlatMemoKey IntersectSchedule

/-- Every available complete constructor identity was issued below the actual source counter. -/
theorem entry_bounded (state : State Symbol Guard) (facts : Facts state)
    (value : Value Symbol Guard) (available : Available state value)
    (entry : Cache.Interned NodeKey) (field : entryOf value = some entry) : entry.identity < state.nodes.next := by
  obtain ⟨actual, stored, fields⟩ := facts.coherent.nodes entry.key value (available.resident entry field)
  have same : actual = entry := Option.some.inj ((fields_entry _ _ _ fields).symm.trans field)
  subst actual
  exact facts.coherent.valid.2.1 entry.identity entry.key ((facts.coherent.valid.2.2 entry.key entry stored).2)

/-- Available RecInt leaves retain an actual earlier reservation in the source identity supply. -/
theorem reference_bounded (state : State Symbol Guard) (facts : Facts state)
    (identity : Nat) (available : Available state (.reference (.interned identity))) : identity < state.nodes.next := by
  obtain ⟨key, issued⟩ := available.issued identity (by simp [Value.free])
  exact facts.coherent.valid.2.1 identity key issued

/-- A bounded actual issued counter makes every memoizable available source input safe. -/
theorem available_safe (bits : Nat) (state : State Symbol Guard) (facts : Facts state)
    (supply : state.nodes.next < 2 ^ bits)
    (value : Value Symbol Guard) (available : Available state value) (request : Input)
    (complete : input value.referenceOf = some request) : Safe (bits + 2) request := by
  cases value with
  | empty => cases complete; trivial
  | node entry edges depth free =>
      cases complete
      exact (uniform_range bits entry.identity (by have := entry_bounded state facts _ available entry rfl; omega)).1
  | union entry members depth free =>
      cases complete
      exact (uniform_range bits entry.identity (by have := entry_bounded state facts _ available entry rfl; omega)).2.2.1
  | mu entry body depth ordinary =>
      cases complete
      exact (uniform_range bits entry.identity (by have := entry_bounded state facts _ available entry rfl; omega)).2.1
  | reference name =>
      cases name with
      | interned identity =>
          cases complete
          exact (uniform_range bits identity (by have := reference_bounded state facts identity available; omega)).2.2.2
      | uninterned | depth | intersection | state => cases complete

/-- Physical memo-key equality is exact payload equality under the actual supply bound and source record invariants. -/
theorem physical_key_eq_iff (bits : Nat) (state : State Symbol Guard) (facts : Facts state)
    (supply : state.nodes.next < 2 ^ bits)
    (left right : Value Symbol Guard) (leftAvailable : Available state left) (rightAvailable : Available state right)
    (first second : Input) (leftInput : input left.referenceOf = some first) (rightInput : input right.referenceOf = some second) :
    key (bits + 2) left.referenceOf = key (bits + 2) right.referenceOf ↔ left = right := by
  constructor
  · intro same
    have references := (key_eq_iff (bits + 2) left.referenceOf right.referenceOf first second leftInput rightInput
      (available_safe bits state facts supply left leftAvailable first leftInput)
      (available_safe bits state facts supply right rightAvailable second rightInput)).mp same
    exact resident_reference_injective state facts.coherent left right leftAvailable.resident rightAvailable.resident references
  · rintro rfl
    rfl

end MicroCFTA.IntersectionFlatMemoKeyPhysical
