import MicroCFTA.SourcePruningEnumerationFold
import MicroCFTA.SourcePruningEnumerationDispatchObservedNeutral

/-!
# Neutral assignments through an actual native fold observation

Each surviving head supplies the original admission for its actual suffix.
Every returned row uses its own reached native heap. A rejected head has
no satisfying branch. No future successful call or final assignment is an input.
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

/-- The whole actual fold preserves assignments already equated at every selected source. -/
theorem observed_neutral_semantics
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
    (ranges : Ranges checkEmpty sources beforeCaller before target memos.query)
    (held : Nat) (targetOther : target ≠ held)
    (sourcesOther : ∀ source ∈ sources, source ≠ held)
    {n p h : Nat}
    {raw : List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard))}
    {afterCaller : Caller width} {after : EnumerationState.State Symbol EnumGuard} {savedQueries : Queries}
    (observed : run checkEmpty n p h sources beforeCaller before target memos.query =
      (.ok (some raw), afterCaller, savedQueries, after)) :
    ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (residualMeaning : EnumGuard → Language.Term Symbol → Prop)
      (assignment : Nat → Language.Term Symbol),
      (∀ source ∈ sources, UnionFind.SameClass before.representatives source target) →
        ((∃ output : EnumerationState.State Symbol EnumGuard,
          Except.ok ((), output) ∈ raw ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held output)) ↔
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held before)) := by
  induction sources generalizing inventory beforeCaller before memos with
  | nil =>
      simp only [run, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at observed
      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
      intro ambient residualMeaning assignment _joined
      simp
  | cons source rest ih =>
      rcases dispatched : SourcePruningEnumerationDispatch.dispatch checkEmpty n p h
          beforeCaller before source target memos.query with ⟨result, reachedCaller, saved⟩
      cases result with
      | error fault =>
          simp only [run, dispatched] at observed
          cases observed
      | ok possible =>
          cases possible with
          | none =>
              simp only [run, dispatched] at observed
              cases observed
          | some action =>
              have slots : source = target ∨ before.values[source]? = some .eliminated ∨
                  ∃ (sourceNode targetNode : Option Nat) (sourceScs targetScs : List EnumerationState.Suspended),
                    before.values[source]? = some (.unenumerated sourceNode sourceScs) ∧
                    before.values[target]? = some (.unenumerated targetNode targetScs) := by
                rcases selected source (List.mem_cons_self) with eliminated | ⟨sourceNode, sourceScs, sourceStored⟩
                · exact .inr (.inl eliminated)
                · obtain ⟨targetNode, targetScs, targetStored⟩ := targetPending
                  exact .inr (.inr ⟨sourceNode, targetNode, sourceScs, targetScs, sourceStored, targetStored⟩)
              obtain ⟨headInventory, headMemos, headPost, querySame, _oldRealized,
                singleton, headMeaning⟩ := SourcePruningEnumerationDispatch.observed_neutral_packet
                  formulas solver inventory beforeCaller before checkEmpty source target memos initial
                  realized slots ranges.1 targetPending dispatched
              cases rawObserved : ExceptT.run (action before) with
              | nil =>
                  simp only [run, dispatched, rawObserved, Prod.mk.injEq, Except.ok.injEq,
                    Option.some.injEq] at observed
                  rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                  intro ambient residualMeaning assignment joined
                  simpa only [rawObserved] using
                    headMeaning held (sourcesOther source (List.mem_cons_self)) targetOther ambient residualMeaning assignment (joined source (List.mem_cons_self))
              | cons first tail =>
                  cases first with
                  | error fault =>
                      simp only [run, dispatched, rawObserved, Prod.mk.injEq, Except.ok.injEq,
                        Option.some.injEq] at observed
                      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                      intro ambient residualMeaning assignment joined
                      simpa only [rawObserved] using
                        headMeaning held (sourcesOther source (List.mem_cons_self)) targetOther ambient residualMeaning assignment (joined source (List.mem_cons_self))
                  | ok pair =>
                      rcases pair with ⟨valueUnit, middle⟩
                      cases valueUnit
                      cases tail with
                      | cons next remaining =>
                          simp only [run, dispatched, rawObserved, Prod.mk.injEq, Except.ok.injEq,
                            Option.some.injEq] at observed
                          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                          intro ambient residualMeaning assignment joined
                          simpa only [rawObserved] using
                            headMeaning held (sourcesOther source (List.mem_cons_self)) targetOther ambient residualMeaning assignment (joined source (List.mem_cons_self))
                      | nil =>
                          obtain ⟨middleRealized, middlePending, forestSame, preserved⟩ := singleton middle rawObserved
                          have tailSelected : ∀ remaining ∈ rest,
                              middle.values[remaining]? = some .eliminated ∨
                                ∃ (node : Option Nat) (scs : List EnumerationState.Suspended),
                                  middle.values[remaining]? = some (.unenumerated node scs) := by
                            intro remaining member
                            exact preserved remaining (selected remaining (List.mem_cons_of_mem source member))
                          have tailRanges : Ranges checkEmpty rest reachedCaller middle target headMemos.query := by
                            rw [querySame]
                            exact ranges.2 n p h action reachedCaller saved middle dispatched rawObserved
                          have tailObserved : run checkEmpty n p h rest reachedCaller middle target headMemos.query =
                              (.ok (some raw), afterCaller, savedQueries, after) := by
                            rw [querySame]
                            simpa only [run, dispatched, rawObserved] using observed
                          intro ambient residualMeaning assignment joined
                          have tailJoined : ∀ remaining ∈ rest,
                              UnionFind.SameClass middle.representatives remaining target := by
                            intro remaining member
                            rw [forestSame]
                            exact joined remaining (List.mem_cons_of_mem source member)
                          have tailMeaning := ih headInventory reachedCaller middle headMemos
                            headPost.context middleRealized middlePending tailSelected tailRanges
                            (fun remaining member => sourcesOther remaining (List.mem_cons_of_mem source member)) tailObserved
                            ambient residualMeaning assignment tailJoined
                          have singleMeaning :
                              Satisfies
                                (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                                  ambient reachedCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held middle) ↔
                              Satisfies
                                (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                                  ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held before) := by
                            simpa [rawObserved] using
                              headMeaning held (sourcesOther source (List.mem_cons_self)) targetOther ambient residualMeaning assignment (joined source (List.mem_cons_self))
                          exact tailMeaning.trans singleMeaning

end MicroCFTA.SourcePruningEnumerationFold
