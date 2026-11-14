import MicroCFTA.FiniteSlotProgress
import MicroCFTA.SourceCurrentSelectedEligibility
import MicroCFTA.SourcePruningEnumerationSelectedOrdinary
import MicroCFTA.SourcePruningEnumerationSelectedStep
import MicroCFTA.SourceCurrentNativeSlotIndex

/-! The actual repeated prefix strictly reduces the number of expandable slots. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentSelectedRepeatedProgress
open Cache EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
private theorem lookup_set_other {α : Type} (values : List α) (target slot : Nat)
    (value : α) (different : slot ≠ target) :
    (values.set target value)[slot]? = values[slot]? := by
  induction values generalizing target slot with
  | nil => simp
  | cons head tail ih =>
      cases target <;> cases slot <;> simp_all

variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Original selection and the literal parked execution derive strict finite count descent. -/
theorem selected_repeated_progress
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (memos : Memos)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (preference : List Nat → Option Nat) (uv : Nat) (roots : Nat → Nat)
    (initial : Context formulas solver inventory caller memos)
    (safe : Safe before.core)
    (pending : EnumerationReferences.PendingReferences before.core)
    (selection : EnumerationPureSelection.next preference before = .expand uv)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ (readFuel oldHandle : Nat) (scs : List Suspended)
      (readAfter : EnumerationState.State Symbol Constraint) (checkFuel : Nat) (repeated : Bool)
      (checked : EnumerationExpandableIndex.Cached Symbol Constraint),
      before.core.values[uv]? = some (.unenumerated (some oldHandle) scs) ∧
      (∀ extra, ExceptT.run (getValue (readFuel + extra) uv before.core) =
        [.ok (.unenumerated (some oldHandle) scs, readAfter)]) ∧
      (∀ extra, ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
        (checkFuel + extra) uv oldHandle scs readAfter) = [.ok (repeated, checked.core)]) ∧
      (repeated = true →
        ∃ countFuel,
          (∀ er ec ei nativeFuel representativeFuel callbackFuel,
            SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
              (readFuel + er) (checkFuel + ec) nativeFuel representativeFuel (countFuel + ei) callbackFuel
              uv caller before memos.query =
              .parked checked.core (some checked)
                (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata checked checked.core)))) ∧
          uv < before.core.counter ∧ checked.core.counter = before.core.counter ∧
          checked.core.values = before.core.values.set uv (.unenumerated (some oldHandle) []) ∧
          checked.expandable uv = false ∧
          (∀ slot, slot ≠ uv →
            checked.core.values[slot]? = before.core.values[slot]? ∧
              checked.expandable slot = before.expandable slot) ∧
          (List.range checked.core.counter).countP checked.expandable <
            (List.range before.core.counter).countP before.expandable) := by
  -- These decisions are used only to obtain the auxiliary existence facts.
  letI : DecidableEq Symbol := by
    classical
    exact inferInstance
  letI : DecidableEq Node := by
    classical
    exact inferInstance
  obtain ⟨readFuel, oldHandle, scs, oldValue, readAfter, checkFuel, repeated, checked, stored,
    _decoded, _available, _closed, readExact, checkExact, _ready, _paths, _realized,
    _counts, checkedFlags, _avoid, _pending, parked, _continued⟩ :=
    SourcePruningEnumerationSelectedOrdinary.complete_with_history formulas solver inventory caller memos
      holeKey fits admits metadata graph templates checkEmpty edgesOf before preference uv roots
      initial safe pending selection realized paths counts flags
  refine ⟨readFuel, oldHandle, scs, readAfter, checkFuel, repeated, checked,
    stored, readExact, checkExact, ?_⟩
  intro repeatedEq
  obtain ⟨_boundary, _cleared, disabled, _waiting, resolved, countFuel, frame, _reading,
    _seen, written, indexed⟩ := parked repeatedEq
  have updated := SourceCurrentNativeSlotIndex.write_core caller.checked.native.machine.heap
    (EnumerationExpandableIndex.frame resolved before) checked countFuel uv
    (.unenumerated (some oldHandle) []) [] scs (by simpa using indexed 0)
  change checked.core = {resolved with values := resolved.values.set uv (.unenumerated (some oldHandle) [])}
    at updated
  have counterSame : checked.core.counter = before.core.counter :=
    (congrArg (fun state : EnumerationState.State Symbol Constraint => state.counter) updated).trans frame.counter
  have valuesSame : checked.core.values = before.core.values.set uv (.unenumerated (some oldHandle) []) :=
    (congrArg (fun state : EnumerationState.State Symbol Constraint => state.values) updated).trans
      (congrArg (fun values => values.set uv (.unenumerated (some oldHandle) [])) frame.values)
  have inside : uv < before.core.counter := by
    have insideValues := (List.getElem?_eq_some_iff.mp stored).1
    rw [safe.1.aligned]
    exact insideValues
  have otherSlots : ∀ slot, slot ≠ uv →
      checked.core.values[slot]? = before.core.values[slot]? ∧
        checked.expandable slot = before.expandable slot := by
    intro slot different
    have same : checked.core.values[slot]? = before.core.values[slot]? := by
      rw [valuesSame]
      exact lookup_set_other before.core.values uv slot (.unenumerated (some oldHandle) []) different
    have checkedFlag := checkedFlags slot
    rw [same] at checkedFlag
    exact ⟨same, Option.some.inj (checkedFlag.symm.trans (flags slot))⟩
  have eligible := SourceCurrentSelectedEligibility.next_expand_eligible preference before uv selection
  have decreased := FiniteSlotProgress.countP_lt_of_target_cleared
    (List.range before.core.counter) before.expandable checked.expandable uv
    (List.mem_range.mpr eligible.1) eligible.2 disabled (by
      intro slot _member different
      exact (otherSlots slot different).2)
  refine ⟨countFuel, ?_, inside, counterSame, valuesSame, disabled, otherSlots, ?_⟩
  · intro er ec ei nativeFuel representativeFuel callbackFuel
    have adapted := SourcePruningEnumerationParkedRestart.adapt_after_write caller.checked.native.machine.heap
      (countFuel + ei) uv oldHandle scs before checked resolved checked.core written (indexed ei) rfl
    simp only [SourcePruningEnumerationSelectedStep.runPrefix,
      SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, readExact er, checkExact ec,
      repeatedEq, adapted, Option.map_some]
  · simpa only [counterSame] using decreased

end MicroCFTA.SourceCurrentSelectedRepeatedProgress
