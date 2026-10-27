import MicroCFTA.SourcePruningEnumerationInitialRendering
import MicroCFTA.SourcePruningEnumerationResourceHistoryProper

/-!
# Proper actual outputs from the complete original native startup contract

The entire original finite rendered-soundness packet remains.
Literal startup derives proper storage without a new admission.
Each retained actual output history preserves that storage.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationValidity InternedConstructorTemplates
open SourcePruningEnumerationNodes
open InternedProbeProvenance (Available)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Keep the entire original startup result and derive proper storage for every actual emitted output. -/
theorem run_initial_finite_render_sound_proper
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing) (value : Node)
    (seed : Seed) (ceiling : Nat)
    (context : Context formulas solver inventory caller memos)
    (available : Available caller.checked.native.machine.heap value)
    (closed : value.free = []) (emptyPending : metadata.pending = [])
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling)
    (arity : SourcePruningEnumerationArityOrigins.Heap caller.checked.native.machine.heap) :
    ∃ handle,
      encodeNode value = some handle ∧
      lookupNode caller.checked.native.machine.heap handle = some value ∧
      let before : Cached :=
        ⟨EnumerationState.initial handle,
          fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
          fun _ => none⟩
    ∃ bound outcome,
      ((∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) recursiveFuel inventory caller memos metadata before seed ceiling
          (SourcePruningEnumerationRestart.decision stop order metadata before) output) ∧
      (∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome, Canonical output.cache.core) ∧
      ∀ (_extra : Nat) output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ∀ (ambient : InternedGuardedLanguage.Env Symbol) (marker : Symbol) (fuel : Nat)
          (after : Core) (term : Language.Term Symbol) (pending : List (Constraint × Language.Term Symbol)),
        SourcePruningEnumerationRendering.Discharged output.cache.core →
        Success (SourcePruningEnumerationRendering.render output.caller.checked.native.machine.heap marker fuel 0)
          output.cache.core (term, pending) after →
        (∀ obligation ∈ pending, SourceEqualityPCSGuard.holds formulas solver obligation.1 obligation.2 = true) →
        ∃ assignment : Nat → Language.Term Symbol,
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
            assignment before.core ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term ∧
          (∀ sc ∈ ([] : List Suspended), Suspended.Holds assignment term sc) ∧ term = assignment 0 ∧
          EnumerationCompressionFrame.Frame output.cache.core after ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient output.caller.checked.native.machine.heap)
            (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
            assignment output.cache.core ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient output.caller.checked.native.machine.heap)
            (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
            assignment after) ∧
      (∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
        EnumerationProgress.ProperState output.cache.core) := by
  obtain ⟨handle, encoded, decoded, bound, outcome, packet⟩ :=
    run_initial_finite_render_sound holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel inventory caller memos metadata value seed ceiling context available
      closed emptyPending bounded known selectionMembers selectionLength reserved arity
  refine ⟨handle, encoded, decoded, bound, outcome, packet, ?_⟩
  intro output member
  exact (packet.2.2.1 0 output member).proper_output (EnumerationProgress.initial_proper handle)

end MicroCFTA.SourcePruningEnumerationRecursive
