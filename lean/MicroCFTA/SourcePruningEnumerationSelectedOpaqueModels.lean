import MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationNativeLanguage

/-!
# Models of the actual selected opaque allocation and captured write

The operational producer runs once before the semantic observer.
The observer extends only the fresh variable. Its value is the original
selected term. The fresh opaque slot has an empty suspended bucket.
The original selected constraints remain true in the original state.
This theorem does not claim that the deferred bucket is stored at the hole.

The runtime retains stopped child observations. A successful child followed
by a failed finalizer returns none, as in the original captured worker.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open EnumerationProgress
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

private theorem finalized_core
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel target : Nat)
    (fragment : Fragments.Fragment Symbol) (before after : Cached)
    (observed : SourcePruningEnumerationFinalize.run heap fuel target fragment before = some after) :
    after.core = {before.core with
      values := before.core.values.set target (.enumerated fragment)
      expansionAncestry := []} := by
  simp only [SourcePruningEnumerationFinalize.run, Option.bind_eq_some_iff] at observed
  obtain ⟨_old, _stored, written⟩ := observed
  simp only [SourcePruningEnumerationNativeIndex.write, Option.bind_eq_some_iff, Option.some.injEq] at written
  obtain ⟨_flag, _classified, _removed, _removedCounts, _saved, _savedCounts, same⟩ := written
  subst after
  rfl

private theorem written_satisfies
    (language : NodeLanguage Symbol) (meaning : Constraint → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (before after : EnumerationState.State Symbol Constraint)
    (target : Nat) (fragment : Fragments.Fragment Symbol)
    (satisfied : Satisfies language meaning assignment before)
    (inside : target < before.values.length)
    (filled : Fragments.fill assignment fragment = assignment target)
    (written : after = {before with
      values := before.values.set target (.enumerated fragment)
      expansionAncestry := []}) : Satisfies language meaning assignment after := by
  subst after
  refine ⟨⟨satisfied.1.1, ?_⟩, satisfied.2⟩
  rw [heap_set language before.values target (.enumerated fragment) inside]
  intro uv
  by_cases same : uv = target
  · subst uv
    simpa only [Fragments.setSlot, ↓reduceIte, slot, Fragments.slotSatisfies] using filled
  · simpa only [Fragments.setSlot, ite_eq_right same] using satisfied.1.2 uv

variable {Typing : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original acceptance constructs a model of the actual opaque result after the original producer. -/
theorem opaque_complete_models
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached) (checkEmpty : Bool) (target originalHandle : Nat) (scs : List Suspended)
    (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready target before.core)
    (stored : before.core.values[target]? = some (.unenumerated (some originalHandle) scs))
    (proper : ProperState before.core)
    (incoming : EnumerationReferences.IncomingAvoid target before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    ∃ (bound childHandle : Nat) (middle after : Cached),
      (encodeNode value = some childHandle ∧
      lookupNode caller.checked.native.machine.heap childHandle = some value ∧
      middle.core = allocated (some childHandle) before.core ∧
      middle.core.values[before.core.counter]? = some (.unenumerated (some childHandle) []) ∧
      middle.expandable = before.expandable ∧ middle.waiting = before.waiting ∧
      (∀ r n p h extra,
        SourcePruningEnumerationChildDispatch.run checkEmpty r n p h (bound + extra)
          scs value caller before memos.query =
          ((.ok (some [.ok (.hole before.core.counter, middle.core)]), caller, memos.query,
            before.core, before.waiting), some middle)) ∧
      (∀ r n p h extra, run checkEmpty r n p h (bound + extra) target scs value caller before memos.query =
        some (.complete (.hole before.core.counter) caller memos.query after)) ∧
      after.core.counter = before.core.counter + 1 ∧
      after.core.values[target]? = some (.enumerated (.hole before.core.counter)) ∧
      after.core.values[before.core.counter]? = some (.unenumerated (some childHandle) []) ∧
      after.core.expansionAncestry = [] ∧
      Packet formulas solver inventory caller memos metadata after ∧ ProperState after.core ∧
      Post formulas solver inventory caller caller memos) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol),
        Satisfies (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
          residualMeaning assignment before.core →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient value (assignment target) →
        ∃ extended : Nat → Term Symbol,
          (∀ uv < before.core.counter, extended uv = assignment uv) ∧
          Satisfies (SourcePruningEnumerationNativeLanguage.handles
            (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
            residualMeaning extended before.core ∧
          Fragments.fill extended (.hole before.core.counter : Fragments.Fragment Symbol) = assignment target ∧
          Satisfies (SourcePruningEnumerationNativeLanguage.handles
            (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
            residualMeaning extended after.core := by
  obtain ⟨bound, childHandle, middle, after, encoded, decoded, middleCore, freshStored,
    flagsSame, waitingSame, childRun, completed, counter, capturedStored, holeStored,
    ancestry, afterPacket, afterProper, post⟩ :=
    opaque_complete formulas solver inventory caller memos metadata before checkEmpty target originalHandle
      scs value packet ready stored proper incoming available closed boundary
  have actualFinalized : SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap
      (bound + 0) target (.hole before.core.counter) middle = some after := by
    have actual := completed 0 0 0 0 0
    cases value <;> cases boundary
    all_goals
      simp only [run, reduceCtorEq, ↓reduceIte, childRun 0 0 0 0 0] at actual
      obtain ⟨finished, finalized, same⟩ := Option.map_eq_some_iff.mp actual
      have cacheSame : finished = after :=
        (SourcePruningEnumerationSelectedEdge.Result.complete.inj same).2.2.2
      simpa only [cacheSame] using finalized
  have finalCore := finalized_core caller.checked.native.machine.heap (bound + 0) target
    (.hole before.core.counter) middle after actualFinalized
  refine ⟨bound, childHandle, middle, after,
    ⟨encoded, decoded, middleCore, freshStored, flagsSame, waitingSame, childRun, completed,
      counter, capturedStored, holeStored, ancestry, afterPacket, afterProper, post⟩, ?_⟩
  intro ambient residualMeaning assignment satisfied accepted
  let extended := EnumerationCorrectness.install assignment before.core.counter [assignment target]
  have agree : ∀ uv < before.core.counter, extended uv = assignment uv :=
    EnumerationCorrectness.install_before assignment before.core.counter [assignment target]
  have fresh : extended before.core.counter = assignment target := by
    simp only [extended, EnumerationCorrectness.install, ↓reduceIte]
  let language := SourcePruningEnumerationNativeLanguage.handles
    (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap
  have originalExtended : Satisfies language residualMeaning extended before.core :=
    (state_assignment_congr language residualMeaning before.core packet.safe.1 extended assignment agree).mpr satisfied
  have preparedAccepted : Fragments.permits ((some childHandle).map language)
      (extended before.core.counter) := by
    change language childHandle (extended before.core.counter)
    rw [fresh]
    exact ⟨value, decoded, accepted⟩
  have middleSatisfied : Satisfies language residualMeaning extended middle.core := by
    rw [middleCore]
    exact (allocation_semantics language residualMeaning extended (some childHandle) before.core
      packet.safe.1.aligned).mpr ⟨originalExtended, preparedAccepted⟩
  have filled : Fragments.fill extended (.hole before.core.counter : Fragments.Fragment Symbol) =
      assignment target := by simpa only [Fragments.fill] using fresh
  have targetFilled : Fragments.fill extended (.hole before.core.counter : Fragments.Fragment Symbol) =
      extended target := filled.trans (agree target ready.inside).symm
  have inside : target < middle.core.values.length := by
    rw [middleCore]
    simp only [allocated, List.length_append, List.length_singleton]
    have bounded := ready.inside
    have aligned := packet.safe.1.aligned
    change before.core.counter = before.core.values.length at aligned
    omega
  exact ⟨extended, agree, originalExtended, filled,
    written_satisfies language residualMeaning extended middle.core after.core target
      (.hole before.core.counter) middleSatisfied inside targetFilled finalCore⟩

end MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
