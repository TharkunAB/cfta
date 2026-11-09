import MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteResources
import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot
import MicroCFTA.SourcePruningEnumerationSharedPreparedRunCounter

/-!
# Counters along actual prepared shared callbacks

The resource hypothesis keeps its current input and output packet.
Literal callback counter laws add the counter bound at that same output.
The proof does not require a positive input counter.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedNativeBranchCompletion (Admitted Pending FragmentHistory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "advance" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance
local notation "mass" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)

/-- The local finite induction keeps one input counter and its same actual output package. -/
def ResumeCounterComplete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Typing) (seed : Seed) (ceiling : Nat),
    Packet formulas solver inventory caller memos metadata before →
    Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    mass before.core ≤ ceiling →
    SourcePruningEnumerationSharedPreparedReservation.Reserved bits recursiveDepth seed ceiling →
    ∃ bound outcome,
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) recursiveDepth metadata caller memos.query before
        (SourcePruningEnumerationRestart.decision stop order metadata before) = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final recursiveDepth seed ceiling) outcome ∧
      ∀ output ∈ emitted outcome, before.core.counter ≤ output.cache.core.counter

/-- Erasing the counter clause retains the same finite resource hypothesis. -/
theorem ResumeCounterComplete.resources
    {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
    {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
    {checkEmpty : Bool} {edgesOf : Node → List (EdgeValue Symbol Constraint)}
    {stop : Option (Metadata Typing → Nat → Bool)} {order : Metadata Typing → List Nat → Option Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {recursiveDepth : Nat}
    (prior : ResumeCounterComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveDepth) :
    ResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveDepth := by
  intro inventory caller memos before metadata seed ceiling packet bounded known members length initial reserved
  obtain ⟨bound, outcome, running, resources, _counters⟩ := prior
    inventory caller memos before metadata seed ceiling packet bounded known members length initial reserved
  exact ⟨bound, outcome, running, resources⟩

/-- The base of the counter induction follows the literal depth-zero execution. -/
theorem zero_counter_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ResumeCounterComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver 0 := by
  intro inventory caller memos before metadata seed ceiling packet bounded known members length initial reserved
  obtain ⟨bound, outcome, running, resources⟩ := zero_complete
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
    inventory caller memos before metadata seed ceiling packet bounded known members length initial reserved
  refine ⟨bound, outcome, running, resources, ?_⟩
  intro output member
  have same := resume_zero_output holeKey fits admits graph templates checkEmpty edgesOf stop order
    (bound + 0) metadata caller memos.query before
    (SourcePruningEnumerationRestart.decision stop order metadata before) output
    (by rw [running 0]; exact member)
  rw [same.1]
  exact Nat.le_refl _

/-- The actual callback transfers the local counter induction at its returned packet. -/
theorem callback_counter_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveDepth : Nat)
    (recursive : ResumeCounterComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveDepth)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : mass before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits recursiveDepth seed ceiling) :
    ∃ (fuel : Nat) (outcome : Result),
      (∀ extra, continueWith
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final recursiveDepth seed ceiling) outcome ∧
      ∀ output ∈ emitted outcome, before.core.counter ≤ output.cache.core.counter := by
  obtain ⟨fuel, _result, _after, outcome, _packet, _stable, _frame, _types, _holes, _typing,
    _callback, running, resources⟩ := callback_induction_complete_resources
    holeKey fits admits formulas solver inventory graph templates metadata uv fragment caller memos before
    checkEmpty edgesOf stop order recursiveDepth recursive.resources seed ceiling packet allocated
    bounded known selectionMembers selectionLength initialMass reserved
  refine ⟨fuel, outcome, running, resources, ?_⟩
  have base := running 0
  simp only [Nat.add_zero] at base
  intro output member
  exact continueWith_output_counter holeKey fits admits graph templates checkEmpty edgesOf stop order
    fuel recursiveDepth metadata uv fragment caller memos.query before output
    (by rw [base]; exact member)

/-- A genuine completed head transfers its current history through the actual callback. -/
theorem receipt_counter_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original next : Inventory) (caller reached : Caller (bits + 2)) (memos final : Memos) (before : Cached)
    (uv : Nat) (receipt : Receipt (bits + 2))
    (packet : Packet formulas solver original caller memos metadata before)
    (post : Post formulas solver next caller reached final)
    (advanced : advance receipt = some (reached, final.query))
    (admitted : Admitted uv receipt) (pending : Pending receipt) (history : FragmentHistory before.core receipt)
    (recursiveDepth : Nat)
    (recursive : ResumeCounterComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveDepth)
    (seed : Seed) (ceiling : Nat)
    (bounded : Fits seed.2 reached.checked)
    (known : Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (currentMass : match receipt with
      | .complete _ _ _ current => mass current.core ≤ ceiling
      | _ => True)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits recursiveDepth seed ceiling) :
    ∃ (fuel : Nat) (outcome : Result),
      (∀ extra, match (generalizing := false) receipt with
        | .complete fragment actual saved after =>
            continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
              (fuel + extra) recursiveDepth)
              graph templates stop order (fuel + extra) metadata uv fragment actual saved after = outcome
        | _ => outcome = .complete [] reached final.query) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final recursiveDepth seed ceiling) outcome ∧
      ∀ output ∈ emitted outcome, before.core.counter ≤ output.cache.core.counter := by
  obtain ⟨fuel, outcome, running, resources⟩ :=
    SourcePruningEnumerationSharedPreparedNativeHookResources.receipt_induction_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver
      original next caller reached memos final before uv receipt packet post advanced admitted pending history
      recursiveDepth recursive.resources seed ceiling bounded known selectionMembers selectionLength currentMass reserved
  refine ⟨fuel, outcome, running, resources, ?_⟩
  cases receipt with
  | unhandled | finalizeStopped _ _ _ _ => cases advanced
  | rejected actual saved after | stopped fragments observation candidate =>
    have empty : outcome = .complete [] reached final.query := running 0
    intro output member
    rw [empty] at member
    cases member
  | complete fragment actual saved after =>
    have base := running 0
    simp only [Nat.add_zero] at base
    intro output member
    exact Nat.le_trans history.1 (continueWith_output_counter
      holeKey fits admits graph templates checkEmpty edgesOf stop order fuel recursiveDepth metadata uv
      fragment actual saved after output (by rw [base]; exact member))

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
