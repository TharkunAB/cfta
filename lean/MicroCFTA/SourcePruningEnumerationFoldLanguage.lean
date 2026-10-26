import MicroCFTA.SourcePruningEnumerationFoldObservedLanguage

/-!
# Assignment meaning of the completed native fold

The original completion producer runs once. Every receipt remains available.
The semantic clause uses the actual raw list and reached native heap.
It requires each recorded source to share the target's original class.
-/

namespace MicroCFTA.SourcePruningEnumerationFold
open EnumerationState EnumerationCorrectness
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- Retain every fold receipt and interpret its actual raw branches under the original class equalities. -/
theorem run_complete_semantics
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationState.State Symbol EnumGuard) (sources : List Nat)
    (checkEmpty : Bool) (target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (targetPending : ∃ (node : Option Nat) (scs : List EnumerationState.Suspended),
      before.values[target]? = some (.unenumerated node scs))
    (selected : ∀ source ∈ sources, before.values[source]? = some .eliminated ∨
      ∃ (node : Option Nat) (scs : List EnumerationState.Suspended),
        before.values[source]? = some (.unenumerated node scs))
    (ranges : Ranges checkEmpty sources beforeCaller before target memos.query) :
    ∃ (fuel p h : Nat)
      (raw : List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard)))
      (afterCaller : Caller width) (after : EnumerationState.State Symbol EnumGuard)
      (savedQueries : Queries) (final : Memos) (next : Inventory),
      (∀ extra P H, p ≤ P → h ≤ H →
        run checkEmpty (fuel + extra) P H sources beforeCaller before target memos.query =
          (.ok (some raw), afterCaller, savedQueries, after)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      PendingRealized afterCaller.checked.native.machine.heap after ∧
      (raw = [] ∨ raw = [.ok ((), after)]) ∧
      (raw = [.ok ((), after)] →
        (∃ (node : Option Nat) (scs : List EnumerationState.Suspended),
          after.values[target]? = some (.unenumerated node scs)) ∧
        ∀ source ∈ sources, source ≠ target → after.values[source]? = some .eliminated) ∧
      (∀ (slot : Nat), before.values[slot]? = some .eliminated → after.values[slot]? = some .eliminated) ∧
      after.values.length = before.values.length ∧
      after.representatives = before.representatives ∧ after.counter = before.counter ∧
      after.obligations = before.obligations ∧ after.expansionAncestry = before.expansionAncestry ∧
      (∀ slot, slot ≠ target → after.recursionAncestry slot = before.recursionAncestry slot) ∧
      (raw = [] →
        ∃ («prefix» : List Nat) (source : Nat) (suffix : List Nat)
          (prefixCaller : Caller width) (prefixEnum : EnumerationState.State Symbol EnumGuard)
          (prefixQueries : Queries) (action : EnumerateM Symbol EnumGuard Unit),
          sources = «prefix» ++ source :: suffix ∧
          (∀ extra P H, p ≤ P → h ≤ H →
            run checkEmpty (fuel + extra) P H «prefix» beforeCaller before target memos.query =
              (.ok (some [.ok ((), prefixEnum)]), prefixCaller, prefixQueries, prefixEnum)) ∧
          (∀ extra P H, p ≤ P → h ≤ H →
            SourcePruningEnumerationDispatch.dispatch checkEmpty (fuel + extra) P H
              prefixCaller prefixEnum source target prefixQueries =
                (.ok (some action), afterCaller, savedQueries)) ∧
          ExceptT.run (action prefixEnum) = [] ∧ after = prefixEnum) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : EnumGuard → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol),
        (∀ source ∈ sources, UnionFind.SameClass before.representatives source target) →
          ((∃ output : EnumerationState.State Symbol EnumGuard,
            Except.ok ((), output) ∈ raw ∧
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient afterCaller.checked.native.machine.heap) residualMeaning assignment output) ↔
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before) := by
  obtain ⟨fuel, p, h, raw, afterCaller, after, savedQueries, final, next,
    running, post, querySame, afterRealized, shape, completed, eliminated, lengths,
    representatives, counter, obligations, expansion, ancestry, rejected⟩ :=
      run_complete formulas solver inventory beforeCaller before sources checkEmpty target memos
        initial realized targetPending selected ranges
  refine ⟨fuel, p, h, raw, afterCaller, after, savedQueries, final, next,
    running, post, querySame, afterRealized, shape, completed, eliminated, lengths,
    representatives, counter, obligations, expansion, ancestry, rejected, ?_⟩
  have observed :
      run checkEmpty fuel p h sources beforeCaller before target memos.query =
        (.ok (some raw), afterCaller, savedQueries, after) := by
    simpa only [Nat.add_zero] using running 0 p h (Nat.le_refl _) (Nat.le_refl _)
  exact observed_semantics formulas solver inventory beforeCaller before sources checkEmpty target memos
    initial realized targetPending selected ranges observed

end MicroCFTA.SourcePruningEnumerationFold
