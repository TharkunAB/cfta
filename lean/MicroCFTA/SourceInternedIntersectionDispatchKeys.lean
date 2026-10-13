import MicroCFTA.SourceInternedIntersectionDispatchMemo

/-!
# Native flat keys for completed plain intersection requests

The source memoizes before it sorts operands. This adapter keeps that order,
the tagged machine words, and the canonical domain identity. The existing
issued-counter bound excludes modular key collisions. Completed memo hits
then use concrete execution provenance, not a computation-purity premise.
-/
namespace MicroCFTA.SourceInternedIntersectionDispatch
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceInternedIntersectionRows IntersectionFlatMemoKeyDomain

/-- Plain records use exactly the EmptyNode and ordinary-node source memo tags. -/
def memoInput : Value Symbol Unit → IntersectSchedule.Input
  | .empty => .empty
  | .node entry .. => .node entry.identity
  | _ => .empty

/-- Every plain operand enters the source memo path with its actual constructor tag. -/
theorem memoInput_exact (value : Value Symbol Unit) (plain : Plain value) :
    IntersectionFlatMemoKey.input value.referenceOf = some (memoInput value) := by
  cases plain <;> rfl

/-- The native triple uses the domain identity and the original ordered operand words. -/
def nativeKey (width : Nat) (domain : Cache.Interned DomainKey)
    (pair : Value Symbol Unit × Value Symbol Unit) : Triple width :=
  flatKey width domain (memoInput pair.1) (memoInput pair.2)

/-- Within the checked issued range, native triples identify complete available operand pairs. -/
theorem nativeKey_injective (bits : Nat) (domain : Cache.Interned DomainKey)
    (state : State Symbol Unit) (facts : Facts state) (supply : state.nodes.next < 2 ^ bits)
    (first second : Value Symbol Unit × Value Symbol Unit)
    (firstInputs : Inputs state first) (secondInputs : Inputs state second)
    (firstPlain : Plain first.1 ∧ Plain first.2) (secondPlain : Plain second.1 ∧ Plain second.2)
    (same : nativeKey (bits + 2) domain first = nativeKey (bits + 2) domain second) : first = second := by
  have words := (Prod.mk.inj same).2
  have components := Prod.mk.inj words
  have leftKey : IntersectionFlatMemoKey.key (bits + 2) first.1.referenceOf =
      IntersectionFlatMemoKey.key (bits + 2) second.1.referenceOf := by
    simpa only [IntersectionFlatMemoKey.key, memoInput_exact first.1 firstPlain.1,
      memoInput_exact second.1 secondPlain.1, Option.map_some] using congrArg some components.1
  have rightKey : IntersectionFlatMemoKey.key (bits + 2) first.2.referenceOf =
      IntersectionFlatMemoKey.key (bits + 2) second.2.referenceOf := by
    simpa only [IntersectionFlatMemoKey.key, memoInput_exact first.2 firstPlain.2,
      memoInput_exact second.2 secondPlain.2, Option.map_some] using congrArg some components.2
  apply Prod.ext
  · exact (IntersectionFlatMemoKeyPhysical.physical_key_eq_iff bits state facts supply _ _ firstInputs.1 secondInputs.1
      _ _ (memoInput_exact _ firstPlain.1) (memoInput_exact _ secondPlain.1)).mp leftKey
  · exact (IntersectionFlatMemoKeyPhysical.physical_key_eq_iff bits state facts supply _ _ firstInputs.2 secondInputs.2
      _ _ (memoInput_exact _ firstPlain.2) (memoInput_exact _ secondPlain.2)).mp rightKey

/-- Completed execution provenance also retains the plain input restriction. -/
theorem produced_plain [DecidableEq Symbol] (state : State Symbol Unit) (pair : Value Symbol Unit × Value Symbol Unit)
    (value : Value Symbol Unit) (produced : Produced state pair value) : Plain pair.1 ∧ Plain pair.2 := by
  obtain ⟨_, _, _, left, right, _⟩ := produced
  exact ⟨left, right⟩

/-- A native keyed completed table records actual dispatched executions. -/
def NativeValid [DecidableEq Symbol] (width : Nat) (domain : Cache.Interned DomainKey)
    (state : State Symbol Unit) (memo : Cache.Table (Triple width) (Value Symbol Unit)) : Prop :=
  ∀ key value, memo key = some value → ∃ pair, nativeKey width domain pair = key ∧ Produced state pair value

/-- Native machine-key hits derive the exact callback result from the original completed execution. -/
theorem native_hit [DecidableEq Symbol] (bits : Nat) (domain : Cache.Interned DomainKey)
    (state : State Symbol Unit) (facts : Facts state) (supply : state.nodes.next < 2 ^ bits)
    (memo : Cache.Table (Triple (bits + 2)) (Value Symbol Unit)) (valid : NativeValid (bits + 2) domain state memo)
    (pair : Value Symbol Unit × Value Symbol Unit) (inputs : Inputs state pair) (plain : Plain pair.1 ∧ Plain pair.2)
    (value : Value Symbol Unit) (present : memo (nativeKey (bits + 2) domain pair) = some value) :
    Available state value ∧ Plain value ∧ ChildExact pair value := by
  obtain ⟨original, same, produced⟩ := valid _ value present
  have checked := produced_spec state original value produced
  have equal := nativeKey_injective bits domain state facts supply original pair checked.1 inputs
    (produced_plain state original value produced) plain same
  subst original
  exact checked.2

/-- Atomic first-writer insertion keeps the actual native triple and concrete execution history. -/
theorem native_insert [DecidableEq Symbol] (width : Nat) (domain : Cache.Interned DomainKey)
    (state : State Symbol Unit) (memo : Cache.Table (Triple width) (Value Symbol Unit))
    (valid : NativeValid width domain state memo) (pair : Value Symbol Unit × Value Symbol Unit) (value : Value Symbol Unit)
    (produced : Produced state pair value) :
    NativeValid width domain state (Cache.keepFirst memo (nativeKey width domain pair) value) := by
  intro key result present
  cases found : memo (nativeKey width domain pair) with
  | some earlier => exact valid key result (by simpa only [Cache.keepFirst, found] using present)
  | none =>
      by_cases same : key = nativeKey width domain pair
      · subst key
        have equal : result = value := by simpa [Cache.keepFirst, found, Cache.put] using present.symm
        subst result
        exact ⟨pair, rfl, produced⟩
      · exact valid key result (by simpa [Cache.keepFirst, found, Cache.put, same] using present)

/-- Completed native entries retain their concrete histories after later constructor effects. -/
theorem native_grows [DecidableEq Symbol] (width : Nat) (domain : Cache.Interned DomainKey)
    (before after : State Symbol Unit) (growth : Grows before after)
    (history : Cache.Extends before.nodes.issued after.nodes.issued)
    (memo : Cache.Table (Triple width) (Value Symbol Unit)) (valid : NativeValid width domain before memo) :
    NativeValid width domain after memo := by
  intro key value present
  obtain ⟨pair, same, produced⟩ := valid key value present
  exact ⟨pair, same, produced_grows before after growth history pair value produced⟩

/-- Completed native lookup runs the concrete caller only on a missing machine triple. -/
noncomputable def nativeRun [DecidableEq Symbol] (width : Nat) (domain : Cache.Interned DomainKey)
    (pair : Value Symbol Unit × Value Symbol Unit) (state : State Symbol Unit)
    (memo : Cache.Table (Triple width) (Value Symbol Unit)) :
    Value Symbol Unit × State Symbol Unit × Cache.Table (Triple width) (Value Symbol Unit) :=
  match memo (nativeKey width domain pair) with
  | some value => (value, state, memo)
  | none =>
      let result := run (dispatch (bound pair) pair) state
      (result.1, result.2, Cache.keepFirst memo (nativeKey width domain pair) result.1)

/-- Both native hit and miss branches derive the callback contract from checked actual execution. -/
theorem nativeRun_correct [DecidableEq Symbol] (bits : Nat) (domain : Cache.Interned DomainKey)
    (pair : Value Symbol Unit × Value Symbol Unit) (plain : Plain pair.1 ∧ Plain pair.2)
    (state : State Symbol Unit) (facts : Facts state) (inputs : Inputs state pair) (supply : state.nodes.next < 2 ^ bits)
    (memo : Cache.Table (Triple (bits + 2)) (Value Symbol Unit)) (valid : NativeValid (bits + 2) domain state memo) :
    let result := nativeRun (bits + 2) domain pair state memo
    Facts result.2.1 ∧ NativeValid (bits + 2) domain result.2.1 result.2.2 ∧
      Grows state result.2.1 ∧ Cache.Extends state.nodes.issued result.2.1.nodes.issued ∧
      Available result.2.1 result.1 ∧ Plain result.1 ∧ ChildExact pair result.1 := by
  cases found : memo (nativeKey (bits + 2) domain pair) with
  | some value =>
      have checked := native_hit bits domain state facts supply memo valid pair inputs plain value found
      simp only [nativeRun, found]
      exact ⟨facts, valid, grows_refl _, Cache.extends_refl _, checked⟩
  | none =>
      have result := finite_exact pair plain.1 plain.2 state facts inputs
      have growth := (InternedConstructorTemplates.run_correct (dispatch (bound pair) pair) state facts.coherent.valid).2
      have history := run_issued_extends (dispatch (bound pair) pair) state facts.coherent.valid
      have produced : Produced (run (dispatch (bound pair) pair) state).2 pair (run (dispatch (bound pair) pair) state).1 :=
        ⟨state, facts, inputs, plain.1, plain.2, rfl, grows_refl _, Cache.extends_refl _⟩
      have retained := native_grows (bits + 2) domain state _ growth history memo valid
      simp only [nativeRun, found]
      exact ⟨result.1, native_insert _ domain _ memo retained pair _ produced, growth, history, result.2.1, result.2.2⟩

/-- The existing physical flat table returns a derived correct winner under its vacancy invariant. -/
theorem native_flat_insert [DecidableEq Symbol] (bits : Nat) (domain : Cache.Interned DomainKey)
    (state : State Symbol Unit) (facts : Facts state) (supply : state.nodes.next < 2 ^ bits)
    (memo : Cache.Table (Triple (bits + 2)) (Value Symbol Unit)) (valid : NativeValid (bits + 2) domain state memo)
    (hash : Triple (bits + 2) → Fin capacity)
    (slots : FlatMemoProbe.Slots capacity (Triple (bits + 2)) (Value Symbol Unit))
    (represented : FlatMemoTable.Represents hash slots memo)
    (pair : Value Symbol Unit × Value Symbol Unit) (inputs : Inputs state pair) (plain : Plain pair.1 ∧ Plain pair.2)
    (candidate : Value Symbol Unit) (produced : Produced state pair candidate)
    (half : 2 * FlatMemoProbe.occupied slots ≤ capacity) :
    ∃ result after, FlatMemoTable.insert hash slots (nativeKey (bits + 2) domain pair) candidate = some (result, after) ∧
      FlatMemoTable.Represents hash after (Cache.keepFirst memo (nativeKey (bits + 2) domain pair) candidate) ∧
      Available state result ∧ Plain result ∧ ChildExact pair result := by
  obtain ⟨result, after, done⟩ := FlatMemoTable.insert_complete hash slots (nativeKey (bits + 2) domain pair) candidate half
  have inserted := FlatMemoTable.insert_correct hash slots memo represented _ _ _ _ done
  have retained := native_insert (bits + 2) domain state memo valid pair candidate produced
  exact ⟨result, after, done, inserted.1,
    native_hit bits domain state facts supply _ retained pair inputs plain result inserted.2⟩

end MicroCFTA.SourceInternedIntersectionDispatch
