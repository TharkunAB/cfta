import MicroCFTA.SourcePruningEnumerationPreparedFiniteHistoryCanonicalArity
import MicroCFTA.SourcePruningEnumerationPreparedHistoryRenderingSoundness

/-!
# Original finite inputs and sound actual prepared outputs

Original input arity derives the same actual output arity.
Each discharged output model satisfies the original cached restrictions.
Checked rendering supplies the complete final assignment.
The original stored root then supplies its native language and suspended constraints.
The original bound, outcome, resources, histories and canonical storage remain unchanged.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open Language EnumerationState EnumerationCorrectness EnumerationValidity InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original finite inputs derive output arity and backward meaning for every discharged actual output. -/
theorem run_finite_complete_resources_with_history_canonical_sound
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
    (reserved : SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling)
    (canonical : Canonical before.core)
    (initialArity : SourcePruningEnumerationArityOrigins.Heap caller.checked.native.machine.heap) :
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) recursiveFuel inventory caller memos metadata before seed ceiling
          (SourcePruningEnumerationRestart.decision stop order metadata before) output) ∧
      (∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
        Canonical output.cache.core) ∧
      OutcomeResourcesWithArity formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
        SourcePruningEnumerationArityOrigins.Heap output.caller.checked.native.machine.heap ∧
        (SourcePruningEnumerationRendering.Discharged output.cache.core →
          ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Term Symbol),
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient output.caller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              assignment output.cache.core →
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient caller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              assignment before.core)) := by
  obtain ⟨bound, outcome, running, resources, histories, canonicalOutputs, strengthened⟩ :=
    run_finite_complete_resources_with_history_canonical_arity
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
      inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved canonical initialArity
  have outputHeaps : ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
      SourcePruningEnumerationArityOrigins.Heap output.caller.checked.native.machine.heap := by
    obtain ⟨_reached, _next, _final, _post, _bounded, _known, _arity, shape⟩ := strengthened
    cases outcome with
    | complete outputs reached queries => exact fun output member => (shape.2.2 output member).2
    | stopped outputs reason endpoint => exact fun output member => (shape.2 output member).2
  refine ⟨bound, outcome, running, resources, histories, canonicalOutputs, strengthened, ?_⟩
  intro output member
  refine ⟨outputHeaps output member, ?_⟩
  intro discharged ambient assignment satisfied
  exact (histories 0 output member).sound rfl canonical (outputHeaps output member)
    discharged ambient assignment satisfied

/-- Checked rendering of a discharged finite output satisfies the original stored native root. -/
theorem run_finite_complete_resources_with_history_canonical_render_sound
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
    (reserved : SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling)
    (canonical : Canonical before.core)
    (initialArity : SourcePruningEnumerationArityOrigins.Heap caller.checked.native.machine.heap) :
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) recursiveFuel inventory caller memos metadata before seed ceiling
          (SourcePruningEnumerationRestart.decision stop order metadata before) output) ∧
      (∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
        Canonical output.cache.core) ∧
      OutcomeResourcesWithArity formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
        SourcePruningEnumerationArityOrigins.Heap output.caller.checked.native.machine.heap ∧
        (SourcePruningEnumerationRendering.Discharged output.cache.core →
          ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Term Symbol),
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient output.caller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              assignment output.cache.core →
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient caller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              assignment before.core)) ∧
      (∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
        SourcePruningEnumerationRendering.Discharged output.cache.core →
        ∀ (ambient : InternedGuardedLanguage.Env Symbol) (marker : Symbol) (fuel uv : Nat)
          (after : Core) (term : Term Symbol) (pending : List (Constraint × Term Symbol)),
          Success
            (SourcePruningEnumerationRendering.render output.caller.checked.native.machine.heap marker fuel uv)
            output.cache.core (term, pending) after →
          (∀ obligation ∈ pending,
            SourceEqualityPCSGuard.holds formulas solver obligation.1 obligation.2 = true) →
          ∀ (handle : Nat) (bucket : List Suspended) (value : Node),
            before.core.values[uv]? = some (.unenumerated (some handle) bucket) →
            lookupNode caller.checked.native.machine.heap handle = some value →
            ∃ assignment : Nat → Term Symbol,
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
                assignment after) := by
  obtain ⟨bound, outcome, running, resources, histories, canonicalOutputs, strengthened, meanings⟩ :=
    run_finite_complete_resources_with_history_canonical_sound
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
      inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved canonical initialArity
  refine ⟨bound, outcome, running, resources, histories, canonicalOutputs, strengthened, meanings, ?_⟩
  intro output member discharged ambient marker fuel uv after term pending observed checked
    handle bucket value stored decoded
  exact (histories 0 output member).render_sound rfl canonical (meanings output member).1 discharged
    ambient marker fuel uv after term pending observed checked handle bucket value stored decoded

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
