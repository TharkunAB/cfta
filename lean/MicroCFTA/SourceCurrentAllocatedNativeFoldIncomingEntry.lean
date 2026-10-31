import MicroCFTA.SourceCurrentAllocatedNativeRawFoldKnown
import MicroCFTA.SourceCurrentAllocatedNativeStoredFold
import MicroCFTA.SourcePruningEnumerationFoldResources
import MicroCFTA.SourcePruningEnumerationFoldUnique
import MicroCFTA.SourcePruningEnumerationCachedFold

/-!
# Actual fold endpoint admission for the next incoming call

The original terminal reservation includes one incoming step.
The proof derives endpoint facts from the literal successful singleton branch.
The arbitrary incoming value's ordinary domain and height cap remain separate.
-/
set_option autoImplicit false

namespace MicroCFTA.SourceCurrentAllocatedNativeFoldIncomingEntry
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentAllocatedNativeResourceForecast (Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
open SourceSizedPrefixKnownOrdinary (KnownOrdinary)
open EnumerationCompleteness (PendingAt PendingOrEliminated)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable [DecidableEq (EdgeKey Symbol Constraint)]

open scoped Classical in
/-- The actual singleton fold derives the next incoming admission and original value availability. -/
theorem fold_incoming_entry (bits bound : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached) (sources : List Nat)
    (checkEmpty : Bool) (n p h target : Nat) (memos : Memos) (incoming : Node)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (targetPending : PendingAt before.core target)
    (selected : ∀ source ∈ sources, PendingOrEliminated before.core source)
    (fits : Fits seed.2 beforeCaller.checked) (reserved : Reserved bits seed (sources.length + 1))
    (annotated : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (stored : Stored beforeCaller.checked.native)
    (known : KnownOrdinary bound beforeCaller.checked.native.machine.heap before)
    (available : Available beforeCaller.checked.native.machine.heap incoming) :
    let actual := SourcePruningEnumerationFold.run checkEmpty n p h sources
      beforeCaller before.core target memos.query
    match actual.1 with
    | .ok (some [.ok ((), after)]) => ∃ next final,
        Post formulas solver next beforeCaller actual.2.1 final ∧ final.query = actual.2.2.1 ∧
        PendingRealized actual.2.1.checked.native.machine.heap after ∧ PendingAt after target ∧
        Fits (advance seed sources.length).2 actual.2.1.checked ∧
        Room bits (advance seed sources.length).2 ∧
        Heap (fun guard => guard ∈ (advance seed sources.length).1) actual.2.1.checked.native.machine.heap ∧
        Stored actual.2.1.checked.native ∧
        KnownOrdinary bound actual.2.1.checked.native.machine.heap {before with core := after} ∧
        Available actual.2.1.checked.native.machine.heap incoming
    | _ => True := by
  classical
  have foldReservation : Reserved bits seed sources.length := reserved.prefix (Nat.le_succ _)
  have room := (SourcePruningEnumerationIncomingReservation.reserved_iff_last bits seed sources.length).mp reserved
  have ranges := SourcePruningEnumerationFold.initial_ranges seed formulas solver inventory beforeCaller
    before.core sources checkEmpty target memos initial realized targetPending selected fits foldReservation annotated
  have rawCaps := SourceCurrentAllocatedNativeRawFoldKnown.fold_known bits bound seed formulas solver inventory
    beforeCaller before sources checkEmpty n p h target memos initial realized targetPending selected
    fits foldReservation annotated stored known
  have nativeStored := SourceCurrentAllocatedNativeStoredFold.fold_native_stored seed formulas solver inventory
    beforeCaller before.core sources checkEmpty n p h target memos initial realized targetPending selected
    fits foldReservation annotated stored
  have selectedForComplete : ∀ source ∈ sources, before.core.values[source]? = some .eliminated ∨
      ∃ node scs, before.core.values[source]? = some (.unenumerated node scs) := by
    intro source member
    rcases selected source member with pending | eliminated
    · exact .inr pending
    · exact .inl eliminated
  obtain ⟨fuel, P, H, rows, later, result, queries, final, next, stable, post, querySame,
    finalRealized, shape, singletonFields, _rest⟩ :=
    SourcePruningEnumerationFold.run_complete formulas solver inventory beforeCaller before.core sources
      checkEmpty target memos initial realized targetPending selectedForComplete ranges
  dsimp only
  generalize observed : SourcePruningEnumerationFold.run checkEmpty n p h sources
    beforeCaller before.core target memos.query = actual
  rcases actual with ⟨tag, reachedCaller, savedQueries, outer⟩
  cases tag with
  | error _fault => trivial
  | ok possible =>
      cases possible with
      | none => trivial
      | some actualRows =>
          cases actualRows with
          | nil => trivial
          | cons first tail =>
              cases first with
              | error _rowError => trivial
              | ok pair =>
                  rcases pair with ⟨valueUnit, after⟩
                  cases valueUnit
                  cases tail with
                  | cons _second _remaining => trivial
                  | nil =>
                      have completed := stable 0 P H (Nat.le_refl _) (Nat.le_refl _)
                      simp only [Nat.add_zero] at completed
                      obtain ⟨sameRows, sameCaller, sameQueries, _sameOuter⟩ :=
                        SourcePruningEnumerationFold.ok_unique checkEmpty observed completed
                      subst reachedCaller
                      subst savedQueries
                      have rawSame : rows = [.ok ((), after)] := (Option.some.inj sameRows).symm
                      have afterSame : after = result := by
                        rcases shape with rejected | singleton
                        · rw [rawSame] at rejected
                          cases rejected
                        · exact congrArg Prod.snd (Except.ok.inj (List.cons.inj (rawSame.symm.trans singleton)).1)
                      subst after
                      have bounds := SourcePruningEnumerationFold.observed_resources seed formulas solver inventory
                        beforeCaller before.core sources checkEmpty n p h target memos initial realized
                        targetPending selected fits foldReservation annotated observed
                      have storedAfter : Stored later.checked.native := by
                        simpa only [observed] using nativeStored
                      simp only [observed] at rawCaps
                      exact ⟨next, final, post, querySame, finalRealized, (singletonFields rawSame).1,
                        bounds.1, room, bounds.2, storedAfter, rawCaps result (by simp),
                        post.effects.keeps.available incoming available⟩

open scoped Classical in
/-- Erasure gives the same incoming entry at the actual cached-fold endpoint, including cache none. -/
theorem cached_fold_incoming_entry (bits bound : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached) (sources : List Nat)
    (checkEmpty : Bool) (n p h target : Nat) (memos : Memos) (incoming : Node)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (targetPending : PendingAt before.core target)
    (selected : ∀ source ∈ sources, PendingOrEliminated before.core source)
    (fits : Fits seed.2 beforeCaller.checked) (reserved : Reserved bits seed (sources.length + 1))
    (annotated : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (stored : Stored beforeCaller.checked.native)
    (known : KnownOrdinary bound beforeCaller.checked.native.machine.heap before)
    (available : Available beforeCaller.checked.native.machine.heap incoming) :
    let actual := SourcePruningEnumerationCachedFold.run checkEmpty n p h sources
      beforeCaller before target memos.query
    match actual.1.1 with
    | .ok (some [.ok ((), after)]) => ∃ next final,
        Post formulas solver next beforeCaller actual.1.2.1 final ∧ final.query = actual.1.2.2.1 ∧
        PendingRealized actual.1.2.1.checked.native.machine.heap after ∧ PendingAt after target ∧
        Fits (advance seed sources.length).2 actual.1.2.1.checked ∧
        Room bits (advance seed sources.length).2 ∧
        Heap (fun guard => guard ∈ (advance seed sources.length).1) actual.1.2.1.checked.native.machine.heap ∧
        Stored actual.1.2.1.checked.native ∧
        KnownOrdinary bound actual.1.2.1.checked.native.machine.heap {before with core := after} ∧
        Available actual.1.2.1.checked.native.machine.heap incoming
    | _ => True := by
  have raw := fold_incoming_entry bits bound seed formulas solver inventory beforeCaller before sources
    checkEmpty n p h target memos incoming initial realized targetPending selected fits reserved
    annotated stored known available
  simpa only [SourcePruningEnumerationCachedFold.erase] using raw

end MicroCFTA.SourceCurrentAllocatedNativeFoldIncomingEntry
