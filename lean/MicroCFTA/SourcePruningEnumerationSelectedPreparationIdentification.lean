import MicroCFTA.SourcePruningEnumerationSelectedPreparation

/-!
# Identify the actual stable selected preparation

The original producer fixes its witnesses before semantic use.
A common sufficient bound identifies the observed preparation with them.
The actual core uses the original cached indexes through frame.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedPreparation
open EnumerationState EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Original resources identify every field of the same actual stable preparation. -/
theorem identify_complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (bound : Nat) (decoded result : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Core)
    (running : ∀ extra, run (bound + extra) (bound + extra) uv caller before =
      ([.ok ((uv, handle, scs, decoded), entered)], some (.done result heap))) :
    (∀ extra, run (bound + extra) (bound + extra) uv caller before =
      ([.ok ((uv, handle, scs, decoded), entered)], some (.done result heap))) ∧
    lookupNode caller.checked.native.machine.heap handle = some decoded ∧
    Post formulas solver inventory caller
      (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos ∧
    Packet formulas solver inventory
      (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos metadata
      (EnumerationExpandableIndex.frame entered before) ∧
    EnumerationDriver.RenderStable before.core entered ∧
    EnumerationDriver.Ready uv entered ∧
    entered.values[uv]? = some (.unenumerated (some handle) scs) ∧
    entered.counter = before.core.counter ∧ entered.values = before.core.values ∧
    (EnumerationExpandableIndex.frame entered before).expandable = before.expandable ∧
    (EnumerationExpandableIndex.frame entered before).waiting = before.waiting ∧
    Available heap result ∧ result.free = [] ∧
    (∀ holds ambient term,
      InternedGuardedLanguage.meaning holds ambient result term ↔
        InternedGuardedLanguage.meaning holds ambient decoded term) ∧
    ∀ holds ambient residualMeaning assignment,
      (Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap)
        residualMeaning assignment entered ↔
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
        caller.checked.native.machine.heap) residualMeaning assignment before.core) ∧
      (Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
        caller.checked.native.machine.heap) residualMeaning assignment before.core →
        InternedGuardedLanguage.meaning holds ambient result (assignment uv)) := by
  obtain ⟨canonicalBound, canonicalDecoded, canonicalResult, canonicalHeap, canonicalCache,
    produced, decodedLookup, post, returnedPacket, stable, enteredReady, enteredStored,
    counter, values, flags, waiting, available, closed, exactLanguage, exactModel⟩ :=
    complete formulas solver inventory caller memos metadata before uv handle scs packet ready stored
  have common := (running canonicalBound).symm.trans (by
    simpa only [Nat.add_comm] using produced bound)
  have rawSame := Except.ok.inj (List.cons.inj (Prod.mk.inj common).1).1
  have decodedSame : decoded = canonicalDecoded :=
    congrArg (fun input : Nat × Nat × List Suspended × Node => input.2.2.2) (Prod.mk.inj rawSame).1
  have coreSame : entered = canonicalCache.core := (Prod.mk.inj rawSame).2
  have resultSame := MergedSourceComparison.Result.done.inj (Option.some.inj (Prod.mk.inj common).2)
  obtain ⟨rfl, rfl⟩ := resultSame
  subst canonicalDecoded
  have cacheSame : canonicalCache = EnumerationExpandableIndex.frame entered before := by
    cases canonicalCache with
    | mk core expandable waitingIndex =>
        change entered = core at coreSame
        change expandable = before.expandable at flags
        change waitingIndex = before.waiting at waiting
        subst core
        subst expandable
        subst waitingIndex
        rfl
  rw [cacheSame] at returnedPacket stable enteredReady enteredStored counter values exactModel
  exact ⟨running, decodedLookup, post, returnedPacket, stable, enteredReady, enteredStored,
    counter, values, rfl, rfl, available, closed, exactLanguage, exactModel⟩

end MicroCFTA.SourcePruningEnumerationSelectedPreparation
