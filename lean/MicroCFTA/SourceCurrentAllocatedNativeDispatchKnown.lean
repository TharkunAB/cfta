import MicroCFTA.SourceSizedPrefixKnownOrdinaryHeap
import MicroCFTA.SourcePruningEnumerationDispatchResources
import MicroCFTA.SourcePruningEnumerationDispatchUnique
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetResult

/-!
# Current admitted dispatch preserves the common ordinary height cap

The outer error branch has no returned-cache claim.
The current slot-shape gate is the existing dispatch completion admission.
The proof derives receipts from current inputs and aligns actual successful outputs.
-/
set_option autoImplicit false

namespace MicroCFTA.SourceCurrentAllocatedNativeDispatchKnown
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceSizedPrefixKnownOrdinary (KnownOrdinary)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "NodeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

private theorem assimilated_known (bound : Nat) (heap : State Symbol Constraint)
    (before : Cached) (source target : Nat) (merged : Option Nat)
    (scs : List EnumerationState.Suspended) (known : KnownOrdinary bound heap before)
    (replacement : ∀ handle, merged = some handle →
      ∃ value, lookupNode heap handle = some value ∧ NodeDomain value ∧
        MergedOrdinaryHeight.height value ≤ bound) :
    KnownOrdinary bound heap
      {before with core := EnumerationCorrectness.assimilated before.core target source (.unenumerated merged scs)} := by
  intro handle currentScs member
  change EnumerationState.UVarValue.unenumerated (some handle) currentScs ∈
    (before.core.values.set target (.unenumerated merged scs)).set source .eliminated at member
  rcases List.mem_or_eq_of_mem_set member with targetMember | impossible
  · rcases List.mem_or_eq_of_mem_set targetMember with old | same
    · exact known handle currentScs old
    · have mergedSame : merged = some handle :=
        (EnumerationState.UVarValue.unenumerated.inj same).1.symm
      exact replacement handle mergedSame
  · cases impossible

variable [DecidableEq (EdgeKey Symbol Constraint)]

open scoped Classical in
/-- Every actual successful dispatch retains old handles and certifies each returned Core. -/
theorem dispatch_known (bits bound : Nat) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (nativeFuel p h source target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (slots : source = target ∨ before.core.values[source]? = some .eliminated ∨
      ∃ (sourceNode targetNode : Option Nat) (sourceScs targetScs : List EnumerationState.Suspended),
        before.core.values[source]? = some (.unenumerated sourceNode sourceScs) ∧
        before.core.values[target]? = some (.unenumerated targetNode targetScs))
    (known : KnownOrdinary bound beforeCaller.checked.native.machine.heap before)
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    (stored : SourceCurrentAllocatedFiniteOrdinaryStored.Stored beforeCaller.checked.native) :
    let actual := SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h beforeCaller
      before.core source target memos.query
    match actual.1 with
    | .error _ => True
    | .ok possible =>
        KnownOrdinary bound actual.2.1.checked.native.machine.heap before ∧
        ∀ action, possible = some action → ∀ after : Core,
          Except.ok ((), after) ∈ ExceptT.run (action before.core) →
            KnownOrdinary bound actual.2.1.checked.native.machine.heap {before with core := after} := by
  classical
  have ranges := SourcePruningEnumerationDispatch.initial_ranges profile beforeCaller before.core source target
    initial.ready realized fits room
  obtain ⟨fuel, P, H, prepared, later, saved, final, next, stable, post, _query, _realized, noop, changed⟩ :=
    SourcePruningEnumerationDispatch.dispatch_complete formulas solver inventory beforeCaller before.core
      checkEmpty source target memos initial realized slots ranges
  dsimp only
  generalize observed : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h beforeCaller
    before.core source target memos.query = actual
  rcases actual with ⟨tag, reached, actualQueries⟩
  cases tag with
  | error _ => trivial
  | ok possible =>
      have completed := stable 0 P H (Nat.le_refl _) (Nat.le_refl _)
      simp only [Nat.add_zero] at completed
      obtain ⟨sameAction, sameCaller, _sameQueries⟩ :=
        SourcePruningEnumerationDispatch.ok_unique checkEmpty observed completed
      subst reached
      have oldKnown := SourceSizedPrefixKnownOrdinaryHeap.post_known post known
      refine ⟨oldKnown, ?_⟩
      intro action selected after returned
      have actionSame : action = prepared := Option.some.inj (selected.symm.trans sameAction)
      subst action
      by_cases idle : source = target ∨ before.core.values[source]? = some .eliminated
      · rw [(noop idle).1] at returned
        have same : after = before.core := congrArg Prod.snd (Except.ok.inj (List.mem_singleton.mp returned))
        simpa only [same] using oldKnown
      · have different : source ≠ target := fun same => idle (Or.inl same)
        have live : before.core.values[source]? ≠ some .eliminated := fun same => idle (Or.inr same)
        obtain ⟨sourceNode, targetNode, merged, sourceScs, targetScs, sourceRead, targetRead,
          raw, _targetWrite, copied, queried⟩ := changed different live
        rw [raw] at returned
        split at returned
        · simp only [List.not_mem_nil] at returned
        · have same : after = EnumerationCorrectness.assimilated before.core target source
              (.unenumerated merged (sourceScs ++ targetScs)) :=
            congrArg Prod.snd (Except.ok.inj (List.mem_singleton.mp returned))
          subst after
          apply assimilated_known bound later.checked.native.machine.heap before source target merged
            (sourceScs ++ targetScs) oldKnown
          intro handle mergedRead
          cases sourceNode with
          | none =>
              have copyRead := (copied (Or.inl rfl)).1.symm.trans mergedRead
              change targetNode = some handle at copyRead
              rw [copyRead] at targetRead
              exact oldKnown handle targetScs (List.mem_of_getElem? targetRead)
          | some leftHandle =>
              cases targetNode with
              | none =>
                  have copyRead := (copied (Or.inr rfl)).1.symm.trans mergedRead
                  change some leftHandle = some handle at copyRead
                  cases Option.some.inj copyRead
                  exact oldKnown handle sourceScs (List.mem_of_getElem? sourceRead)
              | some rightHandle =>
                  obtain ⟨left, right, query, replacement, queryHeap, produced,
                    leftRead, rightRead, _source, _roots, receipt, producedRead, _encoded,
                    replacementRead, _available, _closed, _meaning, disabled, enabled⟩ :=
                    queried leftHandle rightHandle rfl rfl
                  have producedSame : produced = handle := Option.some.inj (producedRead.symm.trans mergedRead)
                  subst produced
                  obtain ⟨leftValue, leftLookup, leftDomain, leftHeight⟩ :=
                    known leftHandle sourceScs (List.mem_of_getElem? sourceRead)
                  have leftSame : leftValue = left := Option.some.inj (leftLookup.symm.trans leftRead)
                  subst leftValue
                  obtain ⟨rightValue, rightLookup, rightDomain, _rightHeight⟩ :=
                    known rightHandle targetScs (List.mem_of_getElem? targetRead)
                  have rightSame : rightValue = right := Option.some.inj (rightLookup.symm.trans rightRead)
                  subst rightValue
                  obtain ⟨_stored, queryDomain, queryLeft, _queryRight, _physical⟩ :=
                    SourceCurrentAllocatedFiniteOrdinaryTargetResult.receipt_result
                      initial.ready stored leftDomain rightDomain receipt
                  have queryHeight : MergedOrdinaryHeight.height query ≤ bound := Nat.le_trans queryLeft leftHeight
                  refine ⟨replacement, replacementRead, ?_⟩
                  cases checkEmpty with
                  | false => rw [(disabled rfl).1]; exact ⟨queryDomain, queryHeight⟩
                  | true =>
                      obtain ⟨reachedQuery, answer, guardSaved, _memo, _checked, _stable,
                        _saved, replacementSame, _miss, _hit⟩ := enabled rfl
                      rw [replacementSame]
                      split
                      · exact ⟨.empty, by simp [MergedOrdinaryHeight.height]⟩
                      · exact ⟨queryDomain, queryHeight⟩

end MicroCFTA.SourceCurrentAllocatedNativeDispatchKnown
