import MicroCFTA.SourcePruningEnumerationPreparedPrefixPointResources
import MicroCFTA.SourcePruningEnumerationSelectedPreparationIdentification
import MicroCFTA.SourcePruningEnumerationSelectedOpaqueStability
import MicroCFTA.SourcePruningEnumerationPreparedOpaqueLanguage

/-!
# Backward meaning from an actual prepared opaque point

The actual history admission pays the narrowed preparation and opaque call.
The selected receipt supplies its actual preparation and completed opaque point.
Point stability supplies the opaque family at larger bounds.
Preparation identification restores the original narrowed input model.
The prepared value and decoded source value remain separate.
The full stored bucket requires the stated retention condition.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open Language EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
attribute [local irreducible] SourcePruningEnumerationSelectedValueCaller.normalizationProfile

/-- The literal opaque receipt arm restores its original narrowed input model. -/
theorem HistoryAdmission.prepared_opaque_sound_retained
    {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
    {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
    {checkEmpty : Bool} {edgesOf : Node → List (EdgeValue Symbol Constraint)}
    {stop : Option (Metadata Typing → Nat → Bool)} {order : Metadata Typing → List Nat → Option Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos} {metadata : Metadata Typing}
    {before : Cached} {recursiveFuel workFuel uv : Nat} {seed : Seed} {ceiling : Nat}
    (admission : HistoryAdmission formulas solver inventory caller memos metadata before
      (recursiveFuel + 1) seed ceiling)
    (observed : SourcePruningEnumerationSelectedStep.Result (bits + 2) Typing)
    (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
      stop order metadata formulas solver inventory workFuel uv caller before memos observed)
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query = observed) :
    match observed with
    | .narrowed _ _ nextCaller _ _ (some narrowed) _ _ =>
        ∀ (nextInventory : Inventory) (nextMemos : Memos) (nextMetadata : Metadata Typing),
          Packet formulas solver nextInventory nextCaller nextMemos nextMetadata narrowed →
          ∀ (handle : Nat) (scs : List Suspended) (decoded prepared : Node)
            (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Cached)
            (preparationBound : Nat),
            EnumerationDriver.Ready uv narrowed.core →
            narrowed.core.values[uv]? = some (.unenumerated (some handle) scs) →
            (∀ extra, SourcePruningEnumerationSelectedPreparation.run (preparationBound + extra)
              (preparationBound + extra) uv nextCaller narrowed =
                ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done prepared heap))) →
            SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv nextCaller narrowed =
              ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done prepared heap)) →
            Packet formulas solver nextInventory
              (SourcePruningEnumerationSelectedValueCaller.advance nextCaller heap)
              nextMemos nextMetadata entered →
            (match (generalizing := false) prepared with
              | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
              | _ => false) = false →
            ∀ (fragment : Fragment) (afterCaller : Caller (bits + 2)) (after : Cached)
              (returnedMemos : Memos),
              SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty
                workFuel workFuel workFuel workFuel workFuel uv scs prepared
                (SourcePruningEnumerationSelectedValueCaller.advance nextCaller heap)
                entered nextMemos.query = some (.complete fragment afterCaller returnedMemos.query after) →
              ((match (generalizing := false) prepared with | .node _ _ _ _ => True | _ => False) ∨
                scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ scs = []) →
              ∀ (ambient : InternedGuardedLanguage.Env Symbol)
                (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol),
                Satisfies (SourcePruningEnumerationNativeLanguage.handles
                  (SourceEqualityPCSGuard.holds formulas solver) ambient afterCaller.checked.native.machine.heap)
                  residualMeaning assignment after.core →
                Satisfies (SourcePruningEnumerationNativeLanguage.handles
                  (SourceEqualityPCSGuard.holds formulas solver) ambient nextCaller.checked.native.machine.heap)
                  residualMeaning assignment narrowed.core ∧
                InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
                  ambient prepared (assignment uv) ∧
                InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
                  ambient decoded (assignment uv) ∧
                (∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) ∧
                Fragments.fill assignment fragment = assignment uv
    | _ => True := by
  have resources := admission.prepared_opaque_resources observed valid actual
  cases observed with
  | stopped _ _ | parked _ _ _ => trivial
  | narrowed checked prefixPrepared nextCaller queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some narrowed =>
          intro nextInventory nextMemos nextMetadata originalPacket handle scs decoded prepared heap entered
            preparationBound ready stored preparing point enteredPacket dispatch fragment afterCaller after
            returnedMemos completed retained
          obtain ⟨_preparing, sourceLookup, preparationPost, _preparedPacket, _render, enteredReady,
            enteredStored, _counter, _values, _flags, _waiting, available, closed, language, exactModel⟩ :=
            SourcePruningEnumerationSelectedPreparation.identify_complete formulas solver nextInventory
              nextCaller nextMemos nextMetadata narrowed uv handle scs originalPacket ready stored
              preparationBound decoded prepared heap entered.core preparing
          have preparedResources := resources nextInventory nextMemos nextMetadata originalPacket
            handle scs decoded prepared heap entered.core stored sourceLookup point
          have preparedLookup : lookupNode
              (SourcePruningEnumerationSelectedValueCaller.advance nextCaller heap).checked.native.machine.heap
              handle = some decoded :=
            lookupNode_keeps _ _ preparationPost.effects.keeps handle decoded sourceLookup
          have stable : ∀ extra, SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty
              (workFuel + extra) (workFuel + extra) (workFuel + extra) (workFuel + extra) (workFuel + extra)
              uv scs prepared (SourcePruningEnumerationSelectedValueCaller.advance nextCaller heap)
              entered nextMemos.query = some (.complete fragment afterCaller returnedMemos.query after) := by
            intro extra
            have enough : workFuel ≤ workFuel + extra := Nat.le_add_right _ _
            exact SourcePruningEnumerationSelectedOpaqueDispatch.complete_stable completed
              enough enough enough enough enough
          have sound := SourcePruningEnumerationSelectedOpaqueDispatch.stable_complete_sound_retained_resources
            (SourcePruningEnumerationPreparedReservation.preparedSeed seed) formulas solver nextInventory
            (SourcePruningEnumerationSelectedValueCaller.advance nextCaller heap) nextMemos nextMetadata
            entered checkEmpty uv handle scs decoded prepared enteredPacket enteredReady enteredStored
            preparedLookup (language (SourceEqualityPCSGuard.holds formulas solver)) available closed dispatch
            preparedResources.1 preparedResources.2.2 preparedResources.2.1 retained stable
          intro ambient residualMeaning assignment satisfied
          obtain ⟨preparedSatisfied, preparedAccepted, sourceAccepted, suspended, equation⟩ :=
            sound ambient residualMeaning assignment satisfied
          exact ⟨(exactModel (SourceEqualityPCSGuard.holds formulas solver)
              ambient residualMeaning assignment).1.mp preparedSatisfied,
            preparedAccepted, sourceAccepted, suspended, equation⟩

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
