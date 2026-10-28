import MicroCFTA.SourcePruningEnumerationReceiptContinuation
import MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationSelectedPreparationResources

/-!
# Hook-aware selected dispatch after one actual preparation

The ordinary branch invokes each hook before the next sibling. The captured
cache stays fixed through that scan. Opaque and terminal branches continue
one actual receipt. The complete preparation pair remains in every result.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedContinuations
open EnumerationState EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error ((Nat × Nat × List Suspended × Node) × Core))
local notation "Preparation" => Raw × Option (MergedSourceComparison.Result Symbol Constraint Node)
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "Fold" => SourcePruningEnumerationNativeContinuations.Result
universe u v
variable {Typing : Type} {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Prepare once and run the actual branch with its hook in source order. -/
noncomputable def run
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) : Preparation × Option (Fold Output Reason width) :=
  let observation := SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before
  (observation, match observation.2 with
    | some (.done value heap) =>
        match observation.1 with
        | [.ok ((target, _handle, scs, _decoded), entered)] =>
            some (if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then
              SourcePruningEnumerationReceiptContinuation.run hook
                (SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value
                  (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
                  (EnumerationExpandableIndex.frame entered before) queries)
            else match value with
              | parent@(.node ..) =>
                  SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k target scs
                    (EnumerationExpandableIndex.frame entered before) (edgesOf parent)
                    (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
              | _ =>
                  SourcePruningEnumerationReceiptContinuation.run hook
                    (SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value
                      (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
                      (EnumerationExpandableIndex.frame entered before) queries))
        | _ => none
    | _ => none)

/-- Every actual entry row and native preparation outcome remains exact. -/
theorem preparation_readback
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    (run hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries).1 =
      SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before := rfl

/-- Ordinary siblings run at each preceding hook's actual returned native endpoint. -/
theorem ordinary
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv target handle : Nat)
    (scs : List Suspended) (decoded : Node)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Core)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries)
    (observed : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
      ([.ok ((target, handle, scs, decoded), entered)], some (.done (.node entry edges depth free) heap)))
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    run hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      (([.ok ((target, handle, scs, decoded), entered)], some (.done (.node entry edges depth free) heap)),
        some (SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k target scs
          (EnumerationExpandableIndex.frame entered before) (edgesOf (.node entry edges depth free))
          (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries)) := by
  simp only [run, observed, nonterminal, Bool.false_eq_true, ↓reduceIte]

/-- Terminal dispatch continues the exact actual child receipt at the captured target. -/
theorem terminal
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv target handle : Nat)
    (scs : List Suspended) (decoded value : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Core)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries)
    (observed : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
      ([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)))
    (here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true) :
    run hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      (([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)),
        some (SourcePruningEnumerationReceiptContinuation.run hook
          (SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value
            (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
            (EnumerationExpandableIndex.frame entered before) queries))) := by
  simp only [run, observed, here, ↓reduceIte]

/-- Native preparation failure retains its actual fault heap and does not invoke a hook. -/
theorem failed
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) (raw : Raw)
    (fault : MergedSourceComparison.Fault) (heap : InternedConstructorTemplates.State Symbol Constraint)
    (observed : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
      (raw, some (.failed fault heap))) :
    run hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      ((raw, some (.failed fault heap)), none) := by
  simp only [run, observed]

/-- Missing native preparation retains the complete actual entry observation. -/
theorem entry_only
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) (raw : Raw)
    (observed : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before = (raw, none)) :
    run hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      ((raw, none), none) := by
  simp only [run, observed]

/-- Original resources fix the full preparation before all hooks and branch fuels. -/
theorem complete_resources
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (profile : SourceCurrentAllocatedNativeResourceForecast.Profile)
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked) :
    ∃ (bound : Nat) (decoded result : Node) (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Cached),
      (((∀ extra, SourcePruningEnumerationSelectedPreparation.run (bound + extra) (bound + extra) uv caller before =
        ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done result heap))) ∧
      lookupNode caller.checked.native.machine.heap handle = some decoded ∧
      Post formulas solver inventory caller
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos ∧
      Packet formulas solver inventory
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos metadata entered ∧
      EnumerationDriver.RenderStable before.core entered.core ∧
      EnumerationDriver.Ready uv entered.core ∧
      entered.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
      entered.core.counter = before.core.counter ∧ entered.core.values = before.core.values ∧
      entered.expandable = before.expandable ∧ entered.waiting = before.waiting ∧
      Available heap result ∧ result.free = [] ∧
      (∀ holds ambient term,
        InternedGuardedLanguage.meaning holds ambient result term ↔
          InternedGuardedLanguage.meaning holds ambient decoded term) ∧
      ∀ holds ambient residualMeaning assignment,
        (Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap)
          residualMeaning assignment entered.core ↔
        Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
          caller.checked.native.machine.heap) residualMeaning assignment before.core) ∧
        (Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
          caller.checked.native.machine.heap) residualMeaning assignment before.core →
          InternedGuardedLanguage.meaning holds ambient result (assignment uv))) ∧
      SourceCurrentConstrainedCapGeneratedQueryResources.Fits
        (SourcePruningEnumerationSelectedValueCaller.normalizationProfile profile)
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap).checked ∧
      InternedValueMass.value result ≤
        (SourcePruningEnumerationSelectedValueCaller.normalizationProfile profile).mass) ∧
      ∀ (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
        (checkEmpty : Bool) (r n p h k : Nat)
        (edgesOf : Node → List (EdgeValue Symbol Constraint)) (queries : Queries) (extra : Nat),
        run hook checkEmpty (bound + extra) (bound + extra) r n p h k uv edgesOf caller before queries =
          (([.ok ((uv, handle, scs, decoded), entered.core)], some (.done result heap)),
            some (if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then
              SourcePruningEnumerationReceiptContinuation.run hook
                (SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k uv scs result
                  (SourcePruningEnumerationSelectedValueCaller.advance caller heap) entered queries)
            else match result with
              | parent@(.node ..) =>
                  SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k uv scs entered
                    (edgesOf parent) (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
              | _ =>
                  SourcePruningEnumerationReceiptContinuation.run hook
                    (SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k uv scs result
                      (SourcePruningEnumerationSelectedValueCaller.advance caller heap) entered queries))) := by
  obtain ⟨bound, decoded, result, heap, entered, packet⟩ :=
    SourcePruningEnumerationSelectedPreparation.complete_resources formulas solver inventory caller memos metadata
      before uv handle scs packet ready stored profile fits
  have retained := packet
  rcases packet with ⟨prepared, _fits, _mass⟩
  rcases prepared with ⟨running, _lookup, _post, _enteredPacket, _stable, _ready, _stored,
    _counter, _values, sameFlags, sameWaiting, _available, _closed, _language, _models⟩
  have framed : EnumerationExpandableIndex.frame entered.core before = entered := by
    cases entered with
    | mk core expandable waiting =>
        simp only [EnumerationExpandableIndex.frame] at *
        congr 1
        · exact sameFlags.symm
        · exact sameWaiting.symm
  refine ⟨bound, decoded, result, heap, entered, retained, ?_⟩
  intro hook checkEmpty r n p h k edgesOf queries extra
  by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
  · simp only [run, running extra, framed, terminal, ↓reduceIte]
  · cases result <;>
      simp only [run, running extra, framed, terminal, Bool.false_eq_true, ↓reduceIte]

/-- An actual opaque prepared value continues its exact receipt at the captured target. -/
theorem opaque_step
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv target handle : Nat)
    (scs : List Suspended) (decoded value : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Core)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries)
    (observed : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
      ([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)))
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    run hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      (([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)),
        some (SourcePruningEnumerationReceiptContinuation.run hook
          (SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value
            (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
            (EnumerationExpandableIndex.frame entered before) queries))) := by
  cases value <;> cases boundary <;> simp only [run, observed, ite_self]

end MicroCFTA.SourcePruningEnumerationSelectedContinuations
