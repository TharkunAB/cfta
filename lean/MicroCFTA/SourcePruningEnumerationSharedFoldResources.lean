import MicroCFTA.SourcePruningEnumerationSharedDispatchResources
import MicroCFTA.SourcePruningEnumerationSharedDispatchUnique
import MicroCFTA.SourcePruningEnumerationSharedIncomingReservation
import MicroCFTA.SourcePruningEnumerationSharedCachedTerminal

/-!
# Resources at the actual shared fold return

Each completed singleton supplies the next current caller and memo bundle.
The ordered shared reservation admits that entry. Early successful outer
stops retain the reached native state and fit the unused schedule.
The cache fold has the same actual raw observation. These laws do not bound
arbitrary failed native calls or prove an adequate recursive driver depth.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
open EnumerationState EnumerationCorrectness EnumerationCompleteness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationSharedIncomingReservation (Seed step advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual singleton retains the complete next entry facts at its own returned states. -/
theorem observed_singleton (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (before : EnumerationState.State Symbol Constraint) (source target : Nat) (rest : List Nat)
    (checkEmpty : Bool) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (targetPending : PendingAt before target)
    (selected : ∀ slot ∈ source :: rest, PendingOrEliminated before slot)
    (fits : Fits seed.2 beforeCaller.checked)
    (room : SourceCurrentAllocatedNativeCreditProfile.Admits bits seed.2)
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    {n p h : Nat} {action : EnumerateM Symbol Constraint Unit} {afterCaller : Caller (bits + 2)}
    {saved : Queries} {after : EnumerationState.State Symbol Constraint}
    (observed : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty n p h beforeCaller before source target memos.query =
      (.ok (some action), afterCaller, saved))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    ∃ next final, Post formulas solver next beforeCaller afterCaller final ∧ final.query = saved ∧
      PendingRealized afterCaller.checked.native.machine.heap after ∧ PendingAt after target ∧
      (∀ slot ∈ rest, PendingOrEliminated after slot) ∧
      Fits (step seed).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (step seed).1) afterCaller.checked.native.machine.heap := by
  have ranges := SourcePruningEnumerationSharedDispatch.initial_ranges seed.2 beforeCaller before source target
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
    unchangedRealized, noop, changed⟩ := SourcePruningEnumerationSharedDispatch.dispatch_complete
      formulas solver inventory beforeCaller before checkEmpty source target memos initial realized slots ranges
  have actual := stable 0 P H (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at actual
  obtain ⟨actionSame, callerSame, queriesSame⟩ :=
    SourcePruningEnumerationSharedDispatch.ok_unique checkEmpty actual observed
  cases Option.some.inj actionSame
  subst reached
  cases queriesSame
  have bounded := SourcePruningEnumerationSharedDispatch.observed_resources seed.1 seed.2 formulas solver inventory
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

/-- Shared reservations bound the exact returned caller of every outer successful raw fold. -/
theorem rawFold_observed_resources (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (before : EnumerationState.State Symbol Constraint) (sources : List Nat)
    (checkEmpty : Bool) (n p h target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (targetPending : PendingAt before target)
    (selected : ∀ source ∈ sources, PendingOrEliminated before source)
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed sources.length)
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    {result : Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint)))}
    {afterCaller : Caller (bits + 2)} {saved : Queries} {after : EnumerationState.State Symbol Constraint}
    (observed : rawFold checkEmpty n p h sources beforeCaller before target memos.query =
      (.ok result, afterCaller, saved, after)) :
    Fits (advance seed sources.length).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed sources.length).1) afterCaller.checked.native.machine.heap := by
  induction sources generalizing seed inventory beforeCaller before memos with
  | nil =>
      simp only [rawFold] at observed
      have same := congrArg (fun output => output.2.1) observed
      dsimp only at same
      rw [← same]
      exact ⟨fits, known⟩
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty n p h
        beforeCaller before source target memos.query with ⟨outcome, reachedCaller, queries⟩
      cases outcome with
      | error fault =>
          simp only [rawFold, dispatchObserved] at observed
          cases observed
      | ok possible =>
          have bounded := SourcePruningEnumerationSharedDispatch.observed_resources seed.1 seed.2 formulas solver inventory
            beforeCaller before checkEmpty n p h source target memos initial realized fits reserved.head known dispatchObserved
          have padded : Fits (advance seed (source :: rest).length).2 reachedCaller.checked ∧
              Heap (fun guard => guard ∈ (advance seed (source :: rest).length).1)
                reachedCaller.checked.native.machine.heap := by
            refine ⟨bounded.1.mono (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge (step seed) rest.length), ?_⟩
            intro key edge found
            exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge (step seed) rest.length
              (bounded.2 key edge found)
          cases possible with
          | none =>
              simp only [rawFold, dispatchObserved] at observed
              have same := congrArg (fun output => output.2.1) observed
              dsimp only at same
              rw [← same]
              exact padded
          | some action =>
              cases raw : ExceptT.run (action before) with
              | nil =>
                  simp only [rawFold, dispatchObserved, raw] at observed
                  have same := congrArg (fun output => output.2.1) observed
                  dsimp only at same
                  rw [← same]
                  exact padded
              | cons first tail =>
                  cases first with
                  | error fault =>
                      simp only [rawFold, dispatchObserved, raw] at observed
                      have same := congrArg (fun output => output.2.1) observed
                      dsimp only at same
                      rw [← same]
                      exact padded
                  | ok pair =>
                      rcases pair with ⟨valueUnit, middle⟩
                      cases valueUnit
                      cases tail with
                      | cons second remaining =>
                          simp only [rawFold, dispatchObserved, raw] at observed
                          have same := congrArg (fun output => output.2.1) observed
                          dsimp only at same
                          rw [← same]
                          exact padded
                      | nil =>
                          obtain ⟨next, final, post, querySame, middleRealized, middleTarget,
                            middleSelected, middleFits, middleKnown⟩ :=
                            observed_singleton seed formulas solver inventory beforeCaller before source target rest checkEmpty memos
                              initial realized targetPending selected fits reserved.head known dispatchObserved raw
                          simp only [rawFold, dispatchObserved, raw] at observed
                          rw [← querySame] at observed
                          exact ih (step seed) next reachedCaller middle final post.context middleRealized middleTarget
                            middleSelected middleFits reserved.tail middleKnown observed

/-- The cached fold returns the same actual resource-bounded raw observation. -/
theorem fold_observed_resources (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) (sources : List Nat)
    (checkEmpty : Bool) (n p h target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (targetPending : PendingAt before.core target)
    (selected : ∀ source ∈ sources, PendingOrEliminated before.core source)
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed sources.length)
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    {result : Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint)))}
    {afterCaller : Caller (bits + 2)} {saved : Queries} {after : EnumerationState.State Symbol Constraint}
    (observed : (fold checkEmpty n p h sources beforeCaller before target memos.query).1 =
      (.ok result, afterCaller, saved, after)) :
    Fits (advance seed sources.length).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed sources.length).1) afterCaller.checked.native.machine.heap := by
  apply rawFold_observed_resources seed formulas solver inventory beforeCaller before.core sources
    checkEmpty n p h target memos initial realized targetPending selected fits reserved known
  rw [← fold_erase checkEmpty n p h sources beforeCaller before target memos.query]
  exact observed

end MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
