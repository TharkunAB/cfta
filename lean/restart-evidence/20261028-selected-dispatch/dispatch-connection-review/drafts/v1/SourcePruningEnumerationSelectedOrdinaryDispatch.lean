import MicroCFTA.SourcePruningEnumerationSelectedPreparation
import MicroCFTA.SourcePruningEnumerationNativeBranches

/-!
# Ordinary dispatch after actual selected-value preparation

The result retains the complete entry and native preparation observation.
The ordinary branch scans the actual prepared rows at the advanced caller.
The left Sum branch retains the preparation for the separate opaque or
terminal dispatcher. It does not claim that those branches have completed.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedOrdinaryDispatch
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

/-- Prepare once and scan only the actual ordinary nonterminal result. -/
noncomputable def run (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    Preparation × Sum Unit (SourcePruningEnumerationNativeBranches.Result width) :=
  let observation := SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before
  (observation, match observation.2 with
    | some (.done value heap) =>
        match observation.1 with
        | [.ok ((target, _handle, scs, _decoded), entered)] =>
            if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then .inl ()
            else match value with
              | parent@(.node ..) =>
                  .inr (SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k target scs
                    (EnumerationExpandableIndex.frame entered before) (edgesOf parent)
                    (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries)
              | _ => .inl ()
        | _ => .inl ()
    | _ => .inl ())

/-- Every entry row and native fault heap remains in the complete first component. -/
theorem preparation_readback (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    (run checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries).1 =
      SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before := rfl

/-- The ordinary branch uses prepared rows and the actual returned native heap. -/
theorem ordinary (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv target handle : Nat)
    (scs : List Suspended) (decoded : Node)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Core)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries)
    (observed : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
      ([.ok ((target, handle, scs, decoded), entered)], some (.done (.node entry edges depth free) heap)))
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    run checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      (([.ok ((target, handle, scs, decoded), entered)], some (.done (.node entry edges depth free) heap)),
        .inr (SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k target scs
          (EnumerationExpandableIndex.frame entered before) (edgesOf (.node entry edges depth free))
          (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries)) := by
  simp only [run, observed, nonterminal, Bool.false_eq_true, ↓reduceIte]

/-- A failed native preparation retains its exact fault and reached heap. -/
theorem failed (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) (raw : Raw)
    (fault : MergedSourceComparison.Fault) (heap : InternedConstructorTemplates.State Symbol Constraint)
    (observed : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
      (raw, some (.failed fault heap))) :
    run checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      ((raw, some (.failed fault heap)), .inl ()) := by
  simp only [run, observed]

/-- A missing native result retains the exact original entry observation. -/
theorem entry_only (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) (raw : Raw)
    (observed : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before = (raw, none)) :
    run checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      ((raw, none), .inl ()) := by
  simp only [run, observed]

/-- Original selected storage fixes the complete preparation before every actual scan. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs)) :
    ∃ (bound : Nat) (decoded result : Node) (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Cached),
      ((∀ extra, run (bound + extra) (bound + extra) uv caller before =
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
      ∀ (checkEmpty : Bool) (r n p h k : Nat)
        (edgesOf : Node → List (EdgeValue Symbol Constraint)) (queries : Queries) (extra : Nat),
        run checkEmpty (bound + extra) (bound + extra) r n p h k uv edgesOf caller before queries =
          (([.ok ((uv, handle, scs, decoded), entered.core)], some (.done result heap)),
            if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then .inl ()
            else match result with
              | parent@(.node ..) =>
                  .inr (SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k uv scs entered
                    (edgesOf parent) (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries)
              | _ => .inl ()) := by
  obtain ⟨bound, decoded, result, heap, entered, packet⟩ :=
    SourcePruningEnumerationSelectedPreparation.complete formulas solver inventory caller memos metadata
      before uv handle scs packet ready stored
  have retained := packet
  rcases packet with ⟨running, _lookup, _post, _enteredPacket, _stable, _ready, _stored,
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
  simp only [run, running extra, framed]

end MicroCFTA.SourcePruningEnumerationSelectedOrdinaryDispatch
