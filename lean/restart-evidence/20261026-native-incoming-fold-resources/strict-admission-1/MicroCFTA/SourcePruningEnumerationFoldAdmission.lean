import MicroCFTA.SourcePruningEnumerationDispatchResources
import MicroCFTA.SourcePruningEnumerationDispatchUnique
import MicroCFTA.SourcePruningEnumerationIncomingReservation
import MicroCFTA.SourcePruningEnumerationFold

/-!
# Original reservations derive every actual fold entry

An arbitrary successful singleton agrees with the constructed dispatch.
Its same returned caller and enumeration core supply the next current facts.
The original mixed reservation therefore derives the full old range predicate.
-/
namespace MicroCFTA.SourcePruningEnumerationFold
open EnumerationState EnumerationCorrectness EnumerationCompleteness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationIncomingReservation (Seed step advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {EnumGuard : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual singleton retains the complete next entry facts at its own returned states. -/
theorem observed_singleton (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (before : EnumerationState.State Symbol EnumGuard) (source target : Nat) (rest : List Nat)
    (checkEmpty : Bool) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (targetPending : PendingAt before target)
    (selected : ∀ slot ∈ source :: rest, PendingOrEliminated before slot)
    (fits : Fits seed.2 beforeCaller.checked)
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits seed.2)
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    {n p h : Nat} {action : EnumerateM Symbol EnumGuard Unit} {afterCaller : Caller (bits + 2)}
    {saved : Queries} {after : EnumerationState.State Symbol EnumGuard}
    (observed : SourcePruningEnumerationDispatch.dispatch checkEmpty n p h beforeCaller before source target memos.query =
      (.ok (some action), afterCaller, saved))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    ∃ next final, Post formulas solver next beforeCaller afterCaller final ∧ final.query = saved ∧
      PendingRealized afterCaller.checked.native.machine.heap after ∧ PendingAt after target ∧
      (∀ slot ∈ rest, PendingOrEliminated after slot) ∧
      Fits (step seed).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (step seed).1) afterCaller.checked.native.machine.heap := by
  have ranges := SourcePruningEnumerationDispatch.initial_ranges seed.2 beforeCaller before source target
    initial.ready realized fits room
  have slots : source = target ∨ before.values[source]? = some .eliminated ∨
      ∃ (sourceNode targetNode : Option Nat) (sourceScs targetScs : List Suspended),
        before.values[source]? = some (.unenumerated sourceNode sourceScs) ∧
        before.values[target]? = some (.unenumerated targetNode targetScs) := by
    rcases selected source (by simp) with ⟨sourceNode, sourceScs, sourceStored⟩ | eliminated
    · obtain ⟨targetNode, targetScs, targetStored⟩ := targetPending
      exact .inr (.inr ⟨sourceNode, targetNode, sourceScs, targetScs, sourceStored, targetStored⟩)
    · exact .inr (.inl eliminated)
  obtain ⟨fuel, P, H, produced, reached, queries, final, next, stable, post, querySame,
    unchangedRealized, noop, changed⟩ := SourcePruningEnumerationDispatch.dispatch_complete
      formulas solver inventory beforeCaller before checkEmpty source target memos initial realized slots ranges
  have actual := stable 0 P H (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at actual
  obtain ⟨actionSame, callerSame, queriesSame⟩ :=
    SourcePruningEnumerationDispatch.ok_unique checkEmpty actual observed
  cases Option.some.inj actionSame
  subst reached
  subst queries
  have bounded := SourcePruningEnumerationDispatch.observed_resources seed.1 seed.2 formulas solver inventory
    beforeCaller before checkEmpty n p h source target memos initial realized fits room known observed
  have nextFacts : PendingRealized afterCaller.checked.native.machine.heap after ∧ PendingAt after target ∧
      ∀ slot ∈ rest, PendingOrEliminated after slot := by
    by_cases same : source = target
    · have raw := (noop (.inl same)).1
      have afterSame : before = after := by
        simpa only [raw, List.cons.injEq, Except.ok.injEq, Prod.mk.injEq, true_and, and_true] using completed
      subst after
      exact ⟨unchangedRealized, targetPending, fun slot member => selected slot (by simp [member])⟩
    · by_cases eliminated : before.values[source]? = some .eliminated
      · have raw := (noop (.inr eliminated)).1
        have afterSame : before = after := by
          simpa only [raw, List.cons.injEq, Except.ok.injEq, Prod.mk.injEq, true_and, and_true] using completed
        subst after
        exact ⟨unchangedRealized, targetPending, fun slot member => selected slot (by simp [member])⟩
      · obtain ⟨sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored,
          raw, surviving, _optional, _present⟩ := changed same eliminated
        have nonempty : merged ≠ some 0 := by
          intro empty
          rw [raw, ite_eq_left empty] at completed
          cases completed
        rw [raw, ite_eq_right nonempty] at completed
        have afterSame : assimilated before target source (.unenumerated merged (sourceScs ++ targetScs)) = after := by
          simpa only [List.cons.injEq, Except.ok.injEq, Prod.mk.injEq, true_and, and_true] using completed
        subst after
        obtain ⟨_targetStored, _sourceStored, nextRealized⟩ := surviving nonempty
        have pending := assimilated_pending before target source merged (sourceScs ++ targetScs) (Ne.symm same)
          (List.getElem?_eq_some_iff.mp targetStored).1 (List.getElem?_eq_some_iff.mp sourceStored).1
        exact ⟨nextRealized, pending.1, fun slot member => pending.2 slot (selected slot (by simp [member]))⟩
  exact ⟨next, final, post, querySame, nextFacts.1, nextFacts.2.1, nextFacts.2.2, bounded.1, bounded.2⟩

/-- An original mixed reservation derives ranges for every successful path of the actual fold. -/
theorem initial_ranges (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (before : EnumerationState.State Symbol EnumGuard) (sources : List Nat)
    (checkEmpty : Bool) (target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (targetPending : PendingAt before target)
    (selected : ∀ source ∈ sources, PendingOrEliminated before source)
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed sources.length)
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap) :
    Ranges checkEmpty sources beforeCaller before target memos.query := by
  induction sources generalizing seed inventory beforeCaller before memos with
  | nil => trivial
  | cons source rest ih =>
      refine ⟨SourcePruningEnumerationDispatch.initial_ranges seed.2 beforeCaller before source target
        initial.ready realized fits reserved.head, ?_⟩
      intro n p h action afterCaller saved after observed completed
      obtain ⟨next, final, post, querySame, afterRealized, afterTarget, afterSelected, afterFits, afterKnown⟩ :=
        observed_singleton seed formulas solver inventory beforeCaller before source target rest checkEmpty memos
          initial realized targetPending selected fits reserved.head known observed completed
      rw [← querySame]
      exact ih (step seed) next afterCaller after final post.context afterRealized afterTarget afterSelected
        afterFits reserved.tail afterKnown

end MicroCFTA.SourcePruningEnumerationFold
