import MicroCFTA.SourcePruningEnumerationFiniteHistoryResourcesArity
import MicroCFTA.SourcePruningEnumerationHistoryRenderingSoundness
import MicroCFTA.SourcePruningEnumerationFiniteHistoryCanonical
import MicroCFTA.SourcePruningEnumerationFiniteHistoryResources

/-!
# Finite checked rendering from genuine initial arity

The original finite resource admission derives every actual arity history.
The same output's checked native rendering implies original acceptance.
No supplied arity history or desired final satisfaction is an input.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationValidity InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
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

/-- Original finite resources and genuine initial arity derive checked rendered acceptance at each own output. -/
theorem run_finite_complete_resources_render_sound_from_initial_arity
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling)
    (canonical : Canonical before.core)
    (arity : SourcePruningEnumerationArityOrigins.Heap caller.checked.native.machine.heap) :
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) recursiveFuel inventory caller memos metadata before seed ceiling
          (SourcePruningEnumerationRestart.decision stop order metadata before) output) ∧
      (∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome, Canonical output.cache.core) ∧
      ∀ (_extra : Nat) output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ∀ (ambient : InternedGuardedLanguage.Env Symbol) (marker : Symbol) (fuel uv : Nat)
          (after : Core) (term : Language.Term Symbol) (pending : List (Constraint × Language.Term Symbol))
          (handle : Nat) (bucket : List Suspended) (value : Node),
        SourcePruningEnumerationRendering.Discharged output.cache.core →
        Success (SourcePruningEnumerationRendering.render output.caller.checked.native.machine.heap marker fuel uv)
          output.cache.core (term, pending) after →
        (∀ obligation ∈ pending, SourceEqualityPCSGuard.holds formulas solver obligation.1 obligation.2 = true) →
        before.core.values[uv]? = some (.unenumerated (some handle) bucket) →
        lookupNode caller.checked.native.machine.heap handle = some value →
        ∃ assignment : Nat → Language.Term Symbol,
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
            assignment before.core ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term ∧
          (∀ sc ∈ bucket, Suspended.Holds assignment term sc) ∧ term = assignment uv ∧
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
            assignment after := by
  obtain ⟨bound, outcome, running, resources, histories, _arityResources, arityHistories⟩ :=
    run_finite_complete_resources_with_history_arity holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved arity
  have outputCanonical : ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
      Canonical output.cache.core := by
    intro output member
    exact (histories 0 output member).canonical_output canonical
  refine ⟨bound, outcome, running, resources, histories, outputCanonical, ?_⟩
  intro extra output member ambient marker fuel uv after term pending handle bucket value
    discharged observed checked stored decoded
  exact (arityHistories extra output member).render_sound rfl canonical discharged ambient marker fuel uv
    after term pending observed checked handle bucket value stored decoded

end MicroCFTA.SourcePruningEnumerationRecursive
