import MicroCFTA.SourcePruningEnumerationSelectedOrdinaryDispatch
import MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationSelectedPreparationResources

/-!
# Actual selected dispatch after one native preparation

The ordinary worker prepares once. Its retained observation supplies the
opaque or terminal branch when ordinary scanning does not apply. The result
keeps the exact native scan or the exact optional captured receipt. It keeps
all entry observations and native fault heaps in the first component.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedDispatch
open EnumerationState EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error ((Nat × Nat × List Suspended × Node) × Core))
local notation "Preparation" => Raw × Option (MergedSourceComparison.Result Symbol Constraint Node)
variable {Typing : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain one preparation and execute its actual ordinary, opaque or terminal branch. -/
noncomputable def run (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    Preparation × Sum (SourcePruningEnumerationNativeBranches.Result width)
      (Option (SourcePruningEnumerationSelectedEdge.Result width)) :=
  let ordinary := SourcePruningEnumerationSelectedOrdinaryDispatch.run checkEmpty
    entryFuel nativeFuel r n p h k uv edgesOf caller before queries
  (ordinary.1, match ordinary.2 with
    | .inr result => .inl result
    | .inl () =>
        match ordinary.1.2 with
        | some (.done value heap) =>
            match ordinary.1.1 with
            | [.ok ((target, _handle, scs, _decoded), entered)] =>
                .inr (SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value
                  (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
                  (EnumerationExpandableIndex.frame entered before) queries)
            | _ => .inr none
        | _ => .inr none)

/-- The complete entry and native preparation observation remains exact. -/
theorem preparation_readback (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    (run checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries).1 =
      SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before := rfl

/-- The entire ordinary scan result remains exact, including every stopped prefix. -/
theorem ordinary (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) (preparation : Preparation)
    (result : SourcePruningEnumerationNativeBranches.Result width)
    (observed : SourcePruningEnumerationSelectedOrdinaryDispatch.run checkEmpty entryFuel nativeFuel
      r n p h k uv edgesOf caller before queries = (preparation, .inr result)) :
    run checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      (preparation, .inl result) := by
  simp only [run, observed]

/-- The deferred observation supplies the actual captured target and prepared heap. -/
theorem deferred (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv target handle : Nat)
    (scs : List Suspended) (decoded value : Node) (entered : Core)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries)
    (observed : SourcePruningEnumerationSelectedOrdinaryDispatch.run checkEmpty entryFuel nativeFuel
      r n p h k uv edgesOf caller before queries =
        (([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)), .inl ())) :
    run checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      (([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)),
        .inr (SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value
          (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
          (EnumerationExpandableIndex.frame entered before) queries)) := by
  simp only [run, observed]

/-- Original packet and profile fix the preparation before every actual branch. -/
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
      ∀ (checkEmpty : Bool) (r n p h k : Nat)
        (edgesOf : Node → List (EdgeValue Symbol Constraint)) (queries : Queries) (extra : Nat),
        run checkEmpty (bound + extra) (bound + extra) r n p h k uv edgesOf caller before queries =
          (([.ok ((uv, handle, scs, decoded), entered.core)], some (.done result heap)),
            if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then
              .inr (SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k uv scs result
                (SourcePruningEnumerationSelectedValueCaller.advance caller heap) entered queries)
            else match result with
              | parent@(.node ..) =>
                  .inl (SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k uv scs entered
                    (edgesOf parent) (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries)
              | _ =>
                  .inr (SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k uv scs result
                    (SourcePruningEnumerationSelectedValueCaller.advance caller heap) entered queries)) := by
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
  intro checkEmpty r n p h k edgesOf queries extra
  by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
  · simp only [run, SourcePruningEnumerationSelectedOrdinaryDispatch.run, running extra,
      framed, terminal, ↓reduceIte]
  · cases result <;>
      simp only [run, SourcePruningEnumerationSelectedOrdinaryDispatch.run, running extra,
        framed, terminal, ↓reduceIte]

end MicroCFTA.SourcePruningEnumerationSelectedDispatch
