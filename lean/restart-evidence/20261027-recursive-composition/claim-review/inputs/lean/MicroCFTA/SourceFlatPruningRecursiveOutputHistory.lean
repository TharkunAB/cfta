import MicroCFTA.SourceFlatPruningRecursiveOutputCompletion
import MicroCFTA.SourcePruningEnumerationOutputHistory

/-!
# Original recursive histories for actual flat outputs

Ordered output correspondence identifies an actual earlier output.
Its operation path starts at the original caller, metadata and cache.
The original finite producer retains its entire output certificate packet.
-/
namespace MicroCFTA.SourceFlatPruningRecursive
open EnumerationState InternedConstructorTemplates
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
local notation "oldOutputs" => SourcePruningEnumerationHookInvocation.hookOutputs
local notation "flatOutputs" => SourceFlatPruningOutputFlow.hookOutputs
variable {Typing Key : Type} {width bits : Nat}

private theorem ordered_output_member
    {outputs : List (Output width Typing)}
    {earlier : List (SourcePruningEnumerationRecursive.Output width Typing)}
    (related : SourceFlatPruningNativeBranches.OrderedRelated OutputRelated outputs earlier) :
    ∀ output ∈ outputs, ∃ original ∈ earlier, OutputRelated output original := by
  induction related with
  | nil => intro output member; cases member
  | cons head _tail ih =>
      intro output member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨original, listed, compared⟩ := ih output later
        exact ⟨original, List.mem_cons_of_mem _ listed, compared⟩

/-- Each related flat output identifies an actual earlier output at the same emission endpoint. -/
theorem related_output_member
    (flat : SourceFlatPruningNativeContinuations.HookResult
      (Output width Typing) (Failure width Typing) width)
    (earlier : SourcePruningEnumerationNativeContinuations.HookResult
      (SourcePruningEnumerationRecursive.Output width Typing)
      (SourcePruningEnumerationRecursive.Failure width Typing) width)
    (related : ResultRelated flat earlier) :
    ∀ output ∈ flatOutputs flat, ∃ original ∈ oldOutputs earlier, OutputRelated output original := by
  cases flat <;> cases earlier <;>
    simp only [ResultRelated, SourceFlatPruningNativeContinuations.HookResultRelated] at related
  all_goals first | contradiction | exact ordered_output_member related.1

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual related outputs retain their operation history from the literal earlier driver input. -/
theorem related_output_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) (caller : Caller width)
    (queries : SourceEndpointMemo.Memos) (before : Cached)
    (flat : SourceFlatPruningNativeContinuations.HookResult
      (Output width Typing) (Failure width Typing) width)
    (earlier : SourcePruningEnumerationNativeContinuations.HookResult
      (SourcePruningEnumerationRecursive.Output width Typing)
      (SourcePruningEnumerationRecursive.Failure width Typing) width)
    (actual : SourcePruningEnumerationRecursive.run holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveFuel metadata caller queries before = earlier)
    (related : ResultRelated flat earlier) :
    ∀ output ∈ flatOutputs flat, ∃ original ∈ oldOutputs earlier,
      OutputRelated output original ∧
      SourcePruningEnumerationRecursive.OutputHistory holeKey fits admits graph templates checkEmpty edgesOf
        stop order workFuel recursiveFuel metadata caller queries before
          (SourcePruningEnumerationRestart.decision stop order metadata before) original := by
  have histories := SourcePruningEnumerationRecursive.run_output_history holeKey fits admits graph templates
    checkEmpty edgesOf stop order workFuel recursiveFuel metadata caller queries before
  rw [actual] at histories
  intro output member
  obtain ⟨original, listed, compared⟩ := related_output_member flat earlier related output member
  exact ⟨original, listed, compared, histories original listed⟩

/-- The whole original output-certificate producer also derives each actual output's recursive path. -/
theorem run_finite_complete_output_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling) :
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationRecursive.run holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) recursiveFuel metadata caller memos.query before = outcome) ∧
      SourcePruningEnumerationRecursive.OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      ∀ (flat : EnumerationFlatCached.Cached Symbol Constraint), EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ (flatOutcome : SourceFlatPruningNativeContinuations.HookResult
          (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
          run holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) recursiveFuel metadata caller memos.query flat = flatOutcome ∧
          ResultRelated flatOutcome outcome ∧
          ∀ output ∈ flatOutputs flatOutcome,
            OutputResources formulas solver caller
              (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) output ∧
            OutputOrigin stop order output ∧
            ∃ original ∈ oldOutputs outcome, OutputRelated output original ∧
              SourcePruningEnumerationRecursive.OutputHistory holeKey fits admits graph templates checkEmpty edgesOf
                stop order (bound + extra) recursiveFuel metadata caller memos.query before
                  (SourcePruningEnumerationRestart.decision stop order metadata before) original := by
  obtain ⟨bound, outcome, running, resources, flatRunning⟩ := run_finite_complete_output_certificates
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel inventory
    caller memos before metadata seed ceiling packet bounded known selectionMembers selectionLength initialMass reserved
  refine ⟨bound, outcome, running, resources, ?_⟩
  intro flat compared extra
  obtain ⟨flatOutcome, actual, related, certificates⟩ := flatRunning flat compared extra
  have histories := related_output_history holeKey fits admits graph templates checkEmpty edgesOf stop order
    (bound + extra) recursiveFuel metadata caller memos.query before flatOutcome outcome (running extra) related
  refine ⟨flatOutcome, actual, related, ?_⟩
  intro output member
  exact ⟨(certificates output member).1, (certificates output member).2, histories output member⟩

end MicroCFTA.SourceFlatPruningRecursive
