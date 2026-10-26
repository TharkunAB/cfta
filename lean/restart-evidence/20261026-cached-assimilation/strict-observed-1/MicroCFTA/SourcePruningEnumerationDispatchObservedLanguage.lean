import MicroCFTA.SourcePruningEnumerationDispatchLanguage
import MicroCFTA.SourcePruningEnumerationDispatchUnique

/-! The actual successful observation retains the canonical native and assignment receipts. -/
namespace MicroCFTA.SourcePruningEnumerationDispatch
open EnumerationState EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
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

/-- Transport one canonical semantic receipt to the same actual successful dispatcher observation. -/
theorem observed_semantics
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationState.State Symbol EnumGuard)
    (checkEmpty : Bool) (source target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (slots : source = target ∨ before.values[source]? = some .eliminated ∨
      ∃ (sourceNode targetNode : Option Nat) (sourceScs targetScs : List EnumerationState.Suspended),
        before.values[source]? = some (.unenumerated sourceNode sourceScs) ∧
        before.values[target]? = some (.unenumerated targetNode targetScs))
    (ranges : if source = target then True else
      match before.values[source]?, before.values[target]? with
      | some (.unenumerated (some left) _), some (.unenumerated (some right) _) =>
          match lookupNode beforeCaller.checked.native.machine.heap left,
              lookupNode beforeCaller.checked.native.machine.heap right with
          | some first, some second => SourceCurrentAllocatedNativeRequestBounds.WordRanges
              (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain first second))
              beforeCaller.checked
          | _, _ => True
      | _, _ => True)
    {n p h : Nat} {action : EnumerateM Symbol EnumGuard Unit}
    {reachedCaller : Caller width} {savedQueries : Queries}
    (observed : dispatch checkEmpty n p h beforeCaller before source target memos.query =
      (.ok (some action), reachedCaller, savedQueries)) :
    ∃ (next : Inventory) (final : Memos),
      Post formulas solver next beforeCaller reachedCaller final ∧ final.query = savedQueries ∧
      PendingRealized reachedCaller.checked.native.machine.heap before ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : EnumGuard → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol),
        UnionFind.SameClass before.representatives source target →
          ((∃ after : EnumerationState.State Symbol EnumGuard,
            Except.ok ((), after) ∈ ExceptT.run (action before) ∧
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient reachedCaller.checked.native.machine.heap) residualMeaning assignment after) ↔
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before) := by
  obtain ⟨fuel, minimumP, minimumH, canonical, afterCaller, returnedQueries, final, next,
    stable, post, querySame, afterRealized, _noop, _live, semantic⟩ :=
      dispatch_complete_semantics formulas solver inventory beforeCaller before checkEmpty source target memos
        initial realized slots ranges
  have canonicalObserved : dispatch checkEmpty fuel minimumP minimumH
      beforeCaller before source target memos.query =
      (.ok (some canonical), afterCaller, returnedQueries) := by
    simpa only [Nat.add_zero] using
      stable 0 minimumP minimumH (Nat.le_refl minimumP) (Nat.le_refl minimumH)
  obtain ⟨actionsSame, callerSame, queriesSame⟩ := ok_unique checkEmpty observed canonicalObserved
  have actionSame : action = canonical := Option.some.inj actionsSame
  subst canonical
  subst afterCaller
  subst returnedQueries
  exact ⟨next, final, post, querySame, afterRealized, semantic⟩

end MicroCFTA.SourcePruningEnumerationDispatch
