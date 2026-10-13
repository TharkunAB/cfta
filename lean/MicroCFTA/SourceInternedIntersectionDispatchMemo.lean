import MicroCFTA.SourceInternedIntersectionDispatchCompletion
import MicroCFTA.FlatMemoPublication

/-!
# Completed memo values from concrete ordinary executions

A memo certificate records an actual dispatched execution and later cache
growth. It does not assume an arbitrary computation is pure. A hit reuses
the complete available result of that execution. A miss executes the checked
ordinary caller. This is the completed-value layer of source memoization.
Native lazy publication and forcing of a pending thunk are separate steps.
-/
namespace MicroCFTA.SourceInternedIntersectionDispatch
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedFreshProbeKeys SourceInternedIntersectionRows

/-- Operand order is retained in the source outer memo key. -/
abbrev MemoKey := InternedBinderProtocol.NodeRef × InternedBinderProtocol.NodeRef

/-- A single empty-domain typed memo family retains completed physical records. -/
abbrev Memo (Symbol : Type) := Cache.Table MemoKey (Value Symbol Unit)

/-- Key the actual ordered operands before any source swap branch. -/
def requestKey (pair : Value Symbol Unit × Value Symbol Unit) : MemoKey :=
  (pair.1.referenceOf, pair.2.referenceOf)

/-- A completed entry has concrete execution provenance and retained physical records. -/
def Produced [DecidableEq Symbol] (state : State Symbol Unit)
    (pair : Value Symbol Unit × Value Symbol Unit) (value : Value Symbol Unit) : Prop :=
  ∃ before, Facts before ∧ Inputs before pair ∧ Plain pair.1 ∧ Plain pair.2 ∧
    value = (run (dispatch (bound pair) pair) before).1 ∧
    Grows (run (dispatch (bound pair) pair) before).2 state ∧
    Cache.Extends (run (dispatch (bound pair) pair) before).2.nodes.issued state.nodes.issued

/-- Each completed table entry was obtained from an actual checked source request. -/
def MemoValid [DecidableEq Symbol] (state : State Symbol Unit) (memo : Memo Symbol) : Prop :=
  ∀ key value, memo key = some value → ∃ pair, requestKey pair = key ∧ Produced state pair value

/-- The empty completed table has no assumed result equations. -/
theorem memo_empty [DecidableEq Symbol] (state : State Symbol Unit) : MemoValid state (fun _ => none) := by
  intro key value impossible
  cases impossible

/-- Concrete provenance persists under later physical constructor effects. -/
theorem produced_grows [DecidableEq Symbol] (before after : State Symbol Unit)
    (growth : Grows before after) (history : Cache.Extends before.nodes.issued after.nodes.issued)
    (pair : Value Symbol Unit × Value Symbol Unit) (value : Value Symbol Unit) (produced : Produced before pair value) :
    Produced after pair value := by
  obtain ⟨original, facts, inputs, leftPlain, rightPlain, result, earlier, issued⟩ := produced
  exact ⟨original, facts, inputs, leftPlain, rightPlain, result, grows_trans earlier growth, Cache.extends_trans issued history⟩

/-- The exact caller theorem derives both a memo result's language and its availability. -/
theorem produced_spec [DecidableEq Symbol] (state : State Symbol Unit)
    (pair : Value Symbol Unit × Value Symbol Unit) (value : Value Symbol Unit) (produced : Produced state pair value) :
    Inputs state pair ∧ Available state value ∧ Plain value ∧ ChildExact pair value := by
  obtain ⟨before, facts, inputs, leftPlain, rightPlain, rfl, growth, history⟩ := produced
  have result := finite_exact pair leftPlain rightPlain before facts inputs
  have beforeGrowth := (InternedConstructorTemplates.run_correct (dispatch (bound pair) pair) before facts.coherent.valid).2
  have beforeHistory := run_issued_extends (dispatch (bound pair) pair) before facts.coherent.valid
  exact ⟨inputs_stable before state (grows_trans beforeGrowth growth) (Cache.extends_trans beforeHistory history) pair inputs,
    result.2.1.grows _ state growth history, result.2.2.1, result.2.2.2⟩

/-- Earlier complete memo entries retain their actual execution histories. -/
theorem memo_grows [DecidableEq Symbol] (before after : State Symbol Unit)
    (growth : Grows before after) (history : Cache.Extends before.nodes.issued after.nodes.issued)
    (memo : Memo Symbol) (valid : MemoValid before memo) : MemoValid after memo := by
  intro key value present
  obtain ⟨pair, same, produced⟩ := valid key value present
  exact ⟨pair, same, produced_grows before after growth history pair value produced⟩

/-- Equal physical operand keys identify the original completed request at the current coherent cache. -/
theorem requestKey_injective (state : State Symbol Unit) (facts : Facts state)
    (first second : Value Symbol Unit × Value Symbol Unit) (firstInputs : Inputs state first) (secondInputs : Inputs state second)
    (same : requestKey first = requestKey second) : first = second := by
  have components := Prod.mk.inj same
  apply Prod.ext
  · exact resident_reference_injective state facts.coherent _ _ firstInputs.1.resident secondInputs.1.resident components.1
  · exact resident_reference_injective state facts.coherent _ _ firstInputs.2.resident secondInputs.2.resident components.2

/-- A completed hit's semantic contract follows from its stored concrete execution. -/
theorem memo_hit [DecidableEq Symbol] (state : State Symbol Unit) (facts : Facts state)
    (memo : Memo Symbol) (valid : MemoValid state memo) (pair : Value Symbol Unit × Value Symbol Unit)
    (inputs : Inputs state pair) (value : Value Symbol Unit) (present : memo (requestKey pair) = some value) :
    Available state value ∧ Plain value ∧ ChildExact pair value := by
  obtain ⟨original, same, produced⟩ := valid (requestKey pair) value present
  have checked := produced_spec state original value produced
  have equal := requestKey_injective state facts original pair checked.1 inputs same
  subst original
  exact checked.2

/-- First-writer insertion preserves concrete execution provenance. -/
theorem memo_insert [DecidableEq Symbol] (state : State Symbol Unit) (memo : Memo Symbol)
    (valid : MemoValid state memo) (pair : Value Symbol Unit × Value Symbol Unit) (value : Value Symbol Unit)
    (produced : Produced state pair value) : MemoValid state (Cache.keepFirst memo (requestKey pair) value) := by
  intro key result present
  cases found : memo (requestKey pair) with
  | some earlier => exact valid key result (by simpa only [Cache.keepFirst, found] using present)
  | none =>
      by_cases same : key = requestKey pair
      · subst key
        have equal : result = value := by simpa [Cache.keepFirst, found, Cache.put] using present.symm
        subst result
        exact ⟨pair, rfl, produced⟩
      · exact valid key result (by simpa [Cache.keepFirst, found, Cache.put, same] using present)

/-- The completed-value evaluator bypasses physical construction on a hit. -/
noncomputable def memoRun [DecidableEq Symbol] (pair : Value Symbol Unit × Value Symbol Unit)
    (state : State Symbol Unit) (memo : Memo Symbol) : Value Symbol Unit × State Symbol Unit × Memo Symbol :=
  match memo (requestKey pair) with
  | some value => (value, state, memo)
  | none =>
      let result := run (dispatch (bound pair) pair) state
      (result.1, result.2, Cache.keepFirst memo (requestKey pair) result.1)

/-- Completed hits and actual constructor misses both derive the same common language. -/
theorem memoRun_correct [DecidableEq Symbol] (pair : Value Symbol Unit × Value Symbol Unit)
    (leftPlain : Plain pair.1) (rightPlain : Plain pair.2)
    (state : State Symbol Unit) (facts : Facts state) (inputs : Inputs state pair)
    (memo : Memo Symbol) (valid : MemoValid state memo) :
    let result := memoRun pair state memo
    Facts result.2.1 ∧ MemoValid result.2.1 result.2.2 ∧ Available result.2.1 result.1 ∧
      Plain result.1 ∧ ChildExact pair result.1 := by
  cases found : memo (requestKey pair) with
  | some value =>
      have checked := memo_hit state facts memo valid pair inputs value found
      simp only [memoRun, found]
      exact ⟨facts, valid, checked⟩
  | none =>
      have result := finite_exact pair leftPlain rightPlain state facts inputs
      have growth := (InternedConstructorTemplates.run_correct (dispatch (bound pair) pair) state facts.coherent.valid).2
      have history := run_issued_extends (dispatch (bound pair) pair) state facts.coherent.valid
      have produced : Produced (run (dispatch (bound pair) pair) state).2 pair (run (dispatch (bound pair) pair) state).1 :=
        ⟨state, facts, inputs, leftPlain, rightPlain, rfl, grows_refl _, Cache.extends_refl _⟩
      have retained := memo_grows state _ growth history memo valid
      simp only [memoRun, found]
      exact ⟨result.1, memo_insert _ memo retained pair _ produced, result.2.1, result.2.2⟩

/-- Once completed, a repeated lookup returns the exact resident result without any new constructor effects. -/
theorem memoRun_hit [DecidableEq Symbol] (pair : Value Symbol Unit × Value Symbol Unit)
    (state : State Symbol Unit) (memo : Memo Symbol) (value : Value Symbol Unit)
    (present : memo (requestKey pair) = some value) : memoRun pair state memo = (value, state, memo) := by
  simp only [memoRun, present]

/-- Actual flat-table first-writer publication retains the derived completed-entry invariant. -/
theorem flat_insert [DecidableEq Symbol] (state : State Symbol Unit) (memo : Memo Symbol) (valid : MemoValid state memo)
    (hash : MemoKey → Fin capacity) (slots : FlatMemoProbe.Slots capacity MemoKey (Value Symbol Unit))
    (represented : FlatMemoTable.Represents hash slots memo)
    (pair : Value Symbol Unit × Value Symbol Unit) (candidate : Value Symbol Unit) (produced : Produced state pair candidate)
    (half : 2 * FlatMemoProbe.occupied slots ≤ capacity) :
    ∃ result after, FlatMemoTable.insert hash slots (requestKey pair) candidate = some (result, after) ∧
      FlatMemoTable.Represents hash after (Cache.keepFirst memo (requestKey pair) candidate) ∧
      MemoValid state (Cache.keepFirst memo (requestKey pair) candidate) := by
  obtain ⟨result, after, done⟩ := FlatMemoTable.insert_complete hash slots (requestKey pair) candidate half
  exact ⟨result, after, done, (FlatMemoTable.insert_correct hash slots memo represented _ _ _ _ done).1,
    memo_insert state memo valid pair candidate produced⟩

end MicroCFTA.SourceInternedIntersectionDispatch
