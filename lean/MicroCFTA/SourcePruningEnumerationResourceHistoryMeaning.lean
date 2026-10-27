import MicroCFTA.SourcePruningEnumerationDischargedRetention
import MicroCFTA.SourcePruningEnumerationParkedMarkerAttachment
import MicroCFTA.SourcePruningEnumerationResourceHistoryCanonical
import MicroCFTA.SourcePruningEnumerationSelectedInvocationLanguage

/-!
# Backward assignment meaning along a discharged resource history

The path retains every original resource and execution receipt.
Only each recorded ordinary head has an extra projected-arity annotation.
A discharged output excludes parked steps and nonterminal opaque children.
The proof derives all other local semantic gates from the actual receipts.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationValidity InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
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

/-- The same actual ordinary receipt also records its own projected arity. -/
def OrdinaryHistoryArityReceipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (metadata : Metadata Typing) (checkEmpty : Bool) (workFuel uv : Nat)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (fragment : Fragment) (reached : Caller (bits + 2)) (after : Cached)
    (returnedInventory : Inventory) (returnedMemos : Memos) : Prop :=
  ∃ (entered : Cached) (handle : Nat) (scs : List Suspended) (decoded : Node)
    (edge : EdgeValue Symbol Constraint) (headSeed : Seed) (inherited : Nat)
    (headInventory : Inventory) (headCaller : Caller (bits + 2)) (headMemos : Memos) (headBound : Nat),
    Packet formulas solver inventory caller memos metadata before ∧
    ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap workFuel uv before.core) =
      [.ok ((uv, handle, scs, decoded), entered.core)] ∧
    Packet formulas solver inventory caller memos metadata entered ∧
    Post formulas solver headInventory caller headCaller headMemos ∧
    SourcePruningEnumerationCapturedEdge.run checkEmpty workFuel workFuel workFuel workFuel workFuel
      uv scs edge headCaller entered headMemos.query = some (.complete fragment reached returnedMemos.query after) ∧
    SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt headSeed inherited formulas solver
      headInventory headCaller headMemos metadata entered checkEmpty uv scs edge headBound fragment reached
      returnedMemos.query after returnedInventory returnedMemos ∧
    ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      arityAllows edge.children.length (EnumerationCorrectness.suspendedVars entered.core.counter tries) = true

/-- The full actual resource path retains only one additional numeric gate at each ordinary head. -/
inductive ResourceHistoryWithArity
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
      ResourceHistoryWithArity holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        fuel inventory caller memos metadata before seed ceiling none ⟨some metadata, before, caller, memos.query⟩
  /-- A supplied done decision retains its own admitted cache. -/
  | done {fuel inventory caller memos metadata before seed ceiling}
      (admission : HistoryAdmission formulas solver inventory caller memos metadata before fuel seed ceiling) :
      ResourceHistoryWithArity holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
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
      (tail : ResourceHistoryWithArity holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        fuel inventory caller memos updated (EnumerationExpandableIndex.frame core parked) tailSeed tailCeiling next output) :
      ResourceHistoryWithArity holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        (fuel + 1) inventory caller memos metadata before seed ceiling (some (.expand uv)) output
  /-- The actual ordinary invocation retains entry, full head receipts and its admitted false callback. -/
  | ordinary {fuel inventory caller memos metadata before seed ceiling uv checked prepared ordinaryInventory
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
      (invocation : SourcePruningEnumerationHookInvocation.OrdinaryInvocation
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
          graph templates stop order workFuel updated uv)
        checkEmpty workFuel workFuel workFuel workFuel workFuel uv edgesOf ordinaryCaller narrowed ordinaryMemos.query
          fragment headCaller returnedMemos.query headCache)
      (receipt : OrdinaryHistoryArityReceipt formulas solver updated checkEmpty workFuel uv ordinaryInventory
        ordinaryCaller ordinaryMemos narrowed fragment headCaller headCache returnedInventory returnedMemos)
      (callbackAdmission : RecursiveCallbackAdmission formulas solver returnedInventory headCaller returnedMemos updated
        headCache uv fragment fuel callbackSeed callbackCeiling)
      (callback : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
        (.inl fragment) headCache.core) = [.ok ((false, recorded), callbackCore)])
      (tail : ResourceHistoryWithArity holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        fuel returnedInventory headCaller returnedMemos recorded (EnumerationExpandableIndex.frame callbackCore headCache)
          callbackSeed callbackCeiling
          (SourcePruningEnumerationRestart.decision stop order recorded
            (EnumerationExpandableIndex.frame callbackCore headCache)) output) :
      ResourceHistoryWithArity holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        (fuel + 1) inventory caller memos metadata before seed ceiling (some (.expand uv)) output

/-- The arity annotation retains every original ordinary receipt field. -/
theorem OrdinaryHistoryArityReceipt.forget
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {metadata : Metadata Typing} {checkEmpty : Bool} {workFuel uv : Nat}
    {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos} {before : Cached}
    {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    (receipt : OrdinaryHistoryArityReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos) :
    OrdinaryHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos := by
  obtain ⟨entered, handle, scs, decoded, edge, headSeed, inherited, headInventory, headCaller,
    headMemos, headBound, original, entry, enteredPacket, post, captured, completed, _arity⟩ := receipt
  exact ⟨entered, handle, scs, decoded, edge, headSeed, inherited, headInventory, headCaller,
    headMemos, headBound, original, entry, enteredPacket, post, captured, completed⟩

variable {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
variable {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
variable {checkEmpty : Bool} {edgesOf : Node → List (EdgeValue Symbol Constraint)}
variable {stop : Option (Metadata Typing → Nat → Bool)}
variable {order : Metadata Typing → List Nat → Option Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {workFuel recursiveFuel : Nat} {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos}
variable {metadata : Metadata Typing} {before : Cached} {seed : Seed} {ceiling : Nat}
variable {next : Option Next} {output : Output (bits + 2) Typing}

/-- Forget only the projected-arity annotations and retain the entire actual resource path. -/
theorem ResourceHistoryWithArity.forget
    (history : ResourceHistoryWithArity holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver workFuel recursiveFuel inventory caller memos metadata before seed ceiling next output) :
    ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos metadata before seed ceiling next output := by
  induction history with
  | stopped admission => exact .stopped admission
  | done admission => exact .done admission
  | parked admission valid observed _tail ih => exact .parked admission valid observed ih
  | ordinary admission valid observed post invocation receipt callbackAdmission callback _tail ih =>
      exact .ordinary admission valid observed post invocation receipt.forget callbackAdmission callback ih

/-- A discharged path restores initial assignment meaning under only its recorded own-arity annotations. -/
theorem ResourceHistoryWithArity.sound
    (history : ResourceHistoryWithArity holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver workFuel recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (actualNext : next = SourcePruningEnumerationRestart.decision stop order metadata before)
    (canonical : Canonical before.core)
    (discharged : SourcePruningEnumerationRendering.Discharged output.cache.core) :
    ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
      Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient output.caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment output.cache.core →
      Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core := by
  revert actualNext canonical discharged
  induction history with
  | stopped _admission =>
      intro _actualNext _canonical _discharged ambient assignment satisfied
      exact satisfied
  | done _admission =>
      intro _actualNext _canonical _discharged ambient assignment satisfied
      exact satisfied
  | @parked fuel inventory caller memos metadata before seed ceiling uv checked parked updated next core
      tailSeed tailCeiling output admission valid observed tail _ih =>
      intro actualNext _canonical discharged
      obtain ⟨_handle, _bucket, _value, _stored, _decoded, _boundary, _created, _retained,
        _outputDecoded, impossible⟩ := parked_tail_created_isolated
        holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel fuel
        inventory caller memos metadata updated before parked uv checked core next tailSeed tailCeiling output
        admission.1 actualNext.symm valid observed tail.forget
      exact False.elim (impossible discharged)
  | @ordinary fuel inventory caller memos metadata before seed ceiling uv checked prepared ordinaryInventory
      ordinaryCaller ordinaryMemos action narrowed updated rightCore fragment returnedInventory headCaller
      returnedMemos headCache recorded callbackCore callbackSeed callbackCeiling output
      admission valid observed _prefixPost invocation receipt _callbackAdmission callback tail ih =>
      intro actualNext canonical discharged
      have chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv) :=
        actualNext.symm
      have narrowedCanonical := SourcePruningEnumerationSelectedStep.prefix_canonical
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos canonical valid
      rw [observed] at narrowedCanonical
      have callbackSuccess : Success (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
          (.inl fragment)) headCache.core (false, recorded) callbackCore := by
        rw [Success, callback]
        exact List.mem_singleton_self _
      have callbackCanonical := receipt.forget.canonical_after_callback graph templates workFuel
        (false, recorded) callbackCore narrowedCanonical callbackSuccess
      have tailMeaning := ih rfl callbackCanonical discharged
      have ready := packet_selected_ready formulas solver inventory stop order metadata caller memos before uv
        admission.1 chosen
      obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := admission.1.valid
      have prefixMeaning := SourcePruningEnumerationSelectedStep.prefix_semantics
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos admission.1.context ready realized valid
      rw [observed] at prefixMeaning
      obtain ⟨entered, handle, scs, decoded, edge, headSeed, inherited, headInventory, localHeadCaller,
        headMemos, headBound, original, entry, enteredPacket, headPost, _captured, completed, ownArity⟩ := receipt
      have entrySuccess : Success (SourcePruningEnumerationEntry.enter
          ordinaryCaller.checked.native.machine.heap workFuel uv) narrowed.core
          (uv, handle, scs, decoded) entered.core := by
        rw [Success, entry]
        exact List.mem_singleton_self _
      have nonterminal := invocation.entry_nonterminal entrySuccess
      have retained := SourcePruningEnumerationOpaqueEvent.completed_head_output_retained
        headSeed inherited formulas solver headInventory localHeadCaller headMemos updated entered checkEmpty
        uv scs edge headBound fragment headCaller returnedMemos.query headCache returnedInventory returnedMemos
        completed holeKey fits admits graph templates edgesOf stop order workFuel fuel recorded callbackCore
        callbackSeed callbackCeiling output callback tail.forget discharged
      obtain ⟨_originalHandle, _parentEntry, _storedEdges, _depth, _free, _stored, _decoded,
        _selected, localMeaning⟩ :=
        SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt.sound_ordinary_callback_input
          original entrySuccess enteredPacket headPost completed callbackSuccess narrowedCanonical
          nonterminal ownArity retained
      intro ambient assignment satisfied
      have callbackSatisfied := tailMeaning ambient assignment satisfied
      have narrowedSatisfied := (localMeaning ambient assignment callbackSatisfied).1
      exact prefixMeaning ambient _ assignment narrowedSatisfied

end MicroCFTA.SourcePruningEnumerationRecursive
