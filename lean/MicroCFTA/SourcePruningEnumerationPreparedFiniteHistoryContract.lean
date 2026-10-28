import MicroCFTA.SourcePruningEnumerationPreparedFiniteContract
import MicroCFTA.SourcePruningEnumerationPreparedOutputHistory
import MicroCFTA.SourcePruningEnumerationPreparedHeadAdmission
import MicroCFTA.SourcePruningEnumerationPreparedZeroOutcomeResources

/-!
# Original resource admission along actual finite output histories

Each recursive input retains its full memo state and original resource plan.
Each selected transition retains actual prefix validity and execution.
A selected transition retains its actual preparation and full callback input.
The contract chooses its common work bound before all emitted histories.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationRecursive (Packet Output)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The original finite input data at one actual recursive cache and native caller. -/
def HistoryAdmission
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
    (recursiveFuel : Nat) (seed : Seed) (ceiling : Nat) : Prop :=
  Packet formulas solver inventory caller memos metadata before ∧
  Fits seed.2 caller.checked ∧
  Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
  suspendedBound before.core ≤ ceiling ∧
  SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling

/-- The exact callback input retains its original finite resource plan. -/
def RecursiveCallbackAdmission
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
    (_uv : Nat) (fragment : Fragment) (recursiveFuel : Nat) (seed : Seed) (ceiling : Nat) : Prop :=
  Packet formulas solver inventory caller memos metadata before ∧
  EnumerationCorrectness.FragmentBound before.core.counter fragment ∧
  Fits seed.2 caller.checked ∧
  Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
  suspendedBound before.core ≤ ceiling ∧
  SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling

/-- A selected invocation retains one actual preparation and its ordinary or opaque completed receipt. -/
def SelectedHistoryReceipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (metadata : Metadata Typing) (checkEmpty : Bool) (workFuel uv : Nat)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (fragment : Fragment) (reached : Caller (bits + 2)) (after : Cached)
    (returnedInventory : Inventory) (returnedMemos : Memos) : Prop :=
  ∃ (entered : Cached) (handle : Nat) (scs : List Suspended) (decoded prepared : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (preparationBound : Nat),
    Packet formulas solver inventory caller memos metadata before ∧
    EnumerationDriver.Ready uv before.core ∧
    before.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
    (∀ extra, SourcePruningEnumerationSelectedPreparation.run (preparationBound + extra)
      (preparationBound + extra) uv caller before =
        ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done prepared heap))) ∧
    SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before =
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done prepared heap)) ∧
    SourcePruningEnumerationNodes.lookupNode caller.checked.native.machine.heap handle = some decoded ∧
    Post formulas solver inventory caller
      (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos ∧
    Packet formulas solver inventory
      (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos metadata entered ∧
    EnumerationDriver.RenderStable before.core entered.core ∧
    EnumerationDriver.Ready uv entered.core ∧
    entered.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
    entered.core.counter = before.core.counter ∧ entered.core.values = before.core.values ∧
    entered.expandable = before.expandable ∧ entered.waiting = before.waiting ∧
    Available heap prepared ∧ prepared.free = [] ∧
    (∀ holds ambient term,
      InternedGuardedLanguage.meaning holds ambient prepared term ↔
        InternedGuardedLanguage.meaning holds ambient decoded term) ∧
    ((∃ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
        (edges : List (EdgeValue Symbol Constraint)) (depth : Nat)
        (free : List InternedBinderProtocol.Reference) (edge : EdgeValue Symbol Constraint)
        (headSeed : Seed) (inherited : Nat) (headInventory : Inventory)
        (headCaller : Caller (bits + 2)) (headMemos : Memos) (headBound : Nat),
        prepared = .node parentEntry edges depth free ∧
        scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false ∧
        Post formulas solver headInventory
          (SourcePruningEnumerationSelectedValueCaller.advance caller heap) headCaller headMemos ∧
        SourcePruningEnumerationCapturedEdge.run checkEmpty workFuel workFuel workFuel workFuel workFuel
          uv scs edge headCaller entered headMemos.query =
            some (.complete fragment reached returnedMemos.query after) ∧
        SourcePruningEnumerationPreparedNativeHookResources.CompletedHeadReceipt headSeed inherited formulas solver
          headInventory headCaller headMemos metadata entered checkEmpty uv handle scs parentEntry edges depth free edge
          headBound fragment reached returnedMemos.query after returnedInventory returnedMemos) ∨
      ((match (generalizing := false) prepared with
        | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
        | _ => false) = false ∧
        SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty workFuel workFuel workFuel workFuel workFuel
          uv scs prepared (SourcePruningEnumerationSelectedValueCaller.advance caller heap) entered memos.query =
            some (.complete fragment reached returnedMemos.query after) ∧
        Post formulas solver returnedInventory
          (SourcePruningEnumerationSelectedValueCaller.advance caller heap) reached returnedMemos ∧
        Packet formulas solver returnedInventory reached returnedMemos metadata entered ∧
        Packet formulas solver returnedInventory reached returnedMemos metadata after ∧
        SourcePruningEnumerationNativeBranchCompletion.Admitted uv
          (.complete fragment reached returnedMemos.query after) ∧
        SourcePruningEnumerationNativeBranchCompletion.Pending
          (.complete fragment reached returnedMemos.query after) ∧
        SourcePruningEnumerationNativeBranchCompletion.FragmentHistory entered.core
          (.complete fragment reached returnedMemos.query after)))

/-- Every operation tag retains its actual original resource inputs and reached callback input. -/
inductive ResourceHistory
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (workFuel : Nat) :
    Nat → Inventory → Caller (bits + 2) → Memos → Metadata Typing → Cached → Seed → Nat →
      Option Next → Output (bits + 2) Typing → Prop where
  /-- A supplied stop retains its own admitted cache and metadata. -/
  | stopped {fuel inventory caller memos metadata before seed ceiling}
      (admission : HistoryAdmission formulas solver inventory caller memos metadata before fuel seed ceiling) :
      ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        fuel inventory caller memos metadata before seed ceiling none ⟨some metadata, before, caller, memos.query⟩
  /-- A supplied done decision retains its own admitted cache. -/
  | done {fuel inventory caller memos metadata before seed ceiling}
      (admission : HistoryAdmission formulas solver inventory caller memos metadata before fuel seed ceiling) :
      ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        fuel inventory caller memos metadata before seed ceiling (some .done) ⟨none, before, caller, memos.query⟩
  /-- An actual parked restart uses the same native caller and full memo state. -/
  | parked {fuel inventory caller memos metadata before seed ceiling uv checked parked updated next core
        tailSeed tailCeiling output}
      (admission : HistoryAdmission formulas solver inventory caller memos metadata before (fuel + 1) seed ceiling)
      (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory workFuel uv caller before memos
        (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
          workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query))
      (observed : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
          .parked checked (some parked) (some [.ok ((updated, next), core)]))
      (tail : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        fuel inventory caller memos updated (EnumerationExpandableIndex.frame core parked) tailSeed tailCeiling next output) :
      ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        (fuel + 1) inventory caller memos metadata before seed ceiling (some (.expand uv)) output
  /-- The actual selected invocation retains preparation, full local receipts and its admitted false callback. -/
  | selected {fuel inventory caller memos metadata before seed ceiling uv checked prepared ordinaryInventory
        ordinaryCaller ordinaryMemos action narrowed updated rightCore fragment returnedInventory headCaller
        returnedMemos headCache recorded callbackCore callbackSeed callbackCeiling output}
      (admission : HistoryAdmission formulas solver inventory caller memos metadata before (fuel + 1) seed ceiling)
      (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory workFuel uv caller before memos
        (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
          workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query))
      (observed : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
          .narrowed checked prepared ordinaryCaller ordinaryMemos.query action (some narrowed)
            (some [.ok ((false, updated), rightCore)]) none)
      (prefixPost : Post formulas solver ordinaryInventory caller ordinaryCaller ordinaryMemos)
      (invocation : SourcePruningEnumerationSelectedContinuations.Invocation
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
          graph templates stop order workFuel updated uv)
        checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf ordinaryCaller narrowed ordinaryMemos.query
          fragment headCaller returnedMemos.query headCache)
      (receipt : SelectedHistoryReceipt formulas solver updated checkEmpty workFuel uv ordinaryInventory
        ordinaryCaller ordinaryMemos narrowed fragment headCaller headCache returnedInventory returnedMemos)
      (callbackAdmission : RecursiveCallbackAdmission formulas solver returnedInventory headCaller returnedMemos updated
        headCache uv fragment fuel callbackSeed callbackCeiling)
      (callback : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
        (.inl fragment) headCache.core) = [.ok ((false, recorded), callbackCore)])
      (tail : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        fuel returnedInventory headCaller returnedMemos recorded (EnumerationExpandableIndex.frame callbackCore headCache)
          callbackSeed callbackCeiling
          (SourcePruningEnumerationRestart.decision stop order recorded
            (EnumerationExpandableIndex.frame callbackCore headCache)) output) :
      ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        (fuel + 1) inventory caller memos metadata before seed ceiling (some (.expand uv)) output

/-- Resource decoration retains the same actual operation path and output. -/
theorem ResourceHistory.forget
    {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
    {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
    {checkEmpty : Bool} {edgesOf : Node → List (EdgeValue Symbol Constraint)}
    {stop : Option (Metadata Typing → Nat → Bool)} {order : Metadata Typing → List Nat → Option Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {workFuel recursiveFuel : Nat} {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos}
    {metadata : Metadata Typing} {before : Cached} {seed : Seed} {ceiling : Nat}
    {next : Option Next} {output : Output (bits + 2) Typing}
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos metadata before seed ceiling next output) :
    OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      recursiveFuel metadata caller memos.query before next output := by
  induction history with
  | stopped _ => exact .stopped
  | done _ => exact .done
  | parked _ _ observed _ ih => exact .parked observed ih
  | selected _ _ observed _ invocation _ _ callback _ ih => exact .selected observed invocation callback ih

/-- Keep the entire original finite contract and retain admitted histories at its own common work bound. -/
def CompleteWithHistory
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveFuel : Nat) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Typing) (seed : Seed) (ceiling : Nat),
    Packet formulas solver inventory caller memos metadata before →
    Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling →
    SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling →
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome ∧
      ∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) recursiveFuel inventory caller memos metadata before seed ceiling
          (SourcePruningEnumerationRestart.decision stop order metadata before) output

/-- Forgetting history retains the original chosen bound and outcome. -/
theorem CompleteWithHistory.forget
    {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
    {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
    {checkEmpty : Bool} {edgesOf : Node → List (EdgeValue Symbol Constraint)}
    {stop : Option (Metadata Typing → Nat → Bool)} {order : Metadata Typing → List Nat → Option Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {recursiveFuel : Nat}
    (complete : CompleteWithHistory (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel) :
    Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel := by
  intro inventory caller memos before metadata seed ceiling packet bounded known
    selectionMembers selectionLength mass reserved
  obtain ⟨bound, outcome, running, resources, _histories⟩ := complete
    inventory caller memos before metadata seed ceiling packet bounded known
    selectionMembers selectionLength mass reserved
  exact ⟨bound, outcome, running, resources⟩

/-- The actual zero-depth stop and done routes already have admitted output histories. -/
theorem zero_complete_with_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    CompleteWithHistory (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver 0 := by
  intro inventory caller memos before metadata seed ceiling packet bounded known
    _selectionMembers _selectionLength mass reserved
  obtain ⟨outcome, running, resources⟩ := resume_zero_outcome_resources
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata
    (SourcePruningEnumerationRestart.decision stop order metadata before) seed packet bounded known
  have admission : HistoryAdmission formulas solver inventory caller memos metadata before 0 seed ceiling :=
    ⟨packet, bounded, known, mass, reserved⟩
  refine ⟨0, outcome, ?_, resources, ?_⟩
  · intro extra
    exact running (0 + extra)
  · intro extra output member
    have emitted : output ∈ SourcePruningEnumerationHookInvocation.hookOutputs
        (run holeKey fits admits graph templates checkEmpty edgesOf stop order (0 + extra) 0
          metadata caller memos.query before) := by
      change output ∈ SourcePruningEnumerationHookInvocation.hookOutputs
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (0 + extra) 0
          metadata caller memos.query before (SourcePruningEnumerationRestart.decision stop order metadata before))
      rw [running (0 + extra)]
      exact member
    unfold run at emitted
    cases chosen : SourcePruningEnumerationRestart.decision stop order metadata before with
    | none =>
        rw [chosen] at emitted
        simp only [resume, SourcePruningEnumerationHookInvocation.hookOutputs, List.mem_singleton] at emitted
        subst output
        exact .stopped admission
    | some next =>
        rw [chosen] at emitted
        cases next with
        | done =>
            simp only [resume, SourcePruningEnumerationHookInvocation.hookOutputs, List.mem_singleton] at emitted
            subst output
            exact .done admission
        | stuck | expand _ => cases emitted

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
