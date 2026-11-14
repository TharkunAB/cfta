import MicroCFTA.SourceSynthesisProgramRolesOpaque
import MicroCFTA.SourceSynthesisProgramRolesUnmarkedCapturedEdge
import MicroCFTA.SourceSynthesisProgramRolesCapturedEdge
import MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteResources
import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot
import MicroCFTA.SourceSynthesisProgramRolesCompression
import MicroCFTA.SourceSynthesisProgramRolesNativeHeap
import MicroCFTA.SourceSynthesisProgramRolesSelectedPrefix
import MicroCFTA.SourceSynthesisProgramRolesOwnInputs
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles
import MicroCFTA.SourcePruningNativeMeaning
import MicroCFTA.SourceSynthesisSelectedProgramChildRetention

/-!
# Program roles in the actual shallow finite shared worker

Each output retains its own marks and exact native endpoint.
Completed callbacks run before the next captured sibling.
The proof does not derive an adequate recursive depth.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourceSynthesisProgramEnumerationRoles (ProgramSlots FragmentRoles SlotRole)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourcePruningEnumerationNodes
open EnumerationCompressionFrame
attribute [local instance] SourcePruningEnumerationAction.actionMonadList
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {Typing Key : Type} {bits : Nat}
local notation "RoleResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)

private def programOutputs (valid : Constraint → Prop) (marked : Nat → Prop)
    (outcome : RoleResult) : Prop :=
  ∀ output ∈ emitted outcome, ∃ extended : Nat → Prop,
    (∀ uv, marked uv → extended uv) ∧
    ProgramSlots valid literal output.caller.checked.native.machine.heap output.cache.core extended

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private def programResumeComplete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (depth : Nat) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Typing) (seed : Seed) (ceiling : Nat),
    Packet formulas solver inventory caller memos metadata before →
    Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling →
    SourcePruningEnumerationSharedPreparedReservation.Reserved bits depth seed ceiling →
    ∀ (valid : Constraint → Prop) (marked : Nat → Prop),
    ProgramSlots valid literal caller.checked.native.machine.heap before.core marked →
    ∃ bound outcome,
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) depth metadata caller memos.query before
        (SourcePruningEnumerationRestart.decision stop order metadata before) = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final depth seed ceiling) outcome ∧
      programOutputs valid marked outcome

private theorem zero_program_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    programResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver 0 := by
  intro inventory caller memos before metadata seed ceiling packet bounded known
    _selectionMembers _selectionLength _mass _reserved valid marked slots
  obtain ⟨outcome, running, resources⟩ := resume_zero_outcome_resources
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory
    caller memos before metadata (SourcePruningEnumerationRestart.decision stop order metadata before)
    seed packet bounded known
  refine ⟨0, outcome, fun extra => running (0 + extra), resources, ?_⟩
  intro output member
  have actualMember : output ∈ emitted (resume holeKey fits admits graph templates checkEmpty
      edgesOf stop order 0 0 metadata caller memos.query before
        (SourcePruningEnumerationRestart.decision stop order metadata before)) := by
    rw [running 0]
    exact member
  obtain ⟨cacheSame, callerSame, _querySame⟩ := resume_zero_output
    holeKey fits admits graph templates checkEmpty edgesOf stop order 0 metadata caller memos.query
    before (SourcePruningEnumerationRestart.decision stop order metadata before) output actualMember
  refine ⟨marked, fun _ tagged => tagged, ?_⟩
  simpa only [cacheSame, callerSame] using slots

private theorem computed_callback_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (depth : Nat)
    (recursive : programResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty
      edgesOf stop order formulas solver depth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (before : Cached) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragments.Fragment Symbol)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits depth seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (callbackFuel : Nat) (result : Bool × Metadata Typing) (after : Core)
    (returned : Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before))
    (framed : EnumerationCompressionFrame.Frame before.core after)
    (recorded : ∀ extra, ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates
      (callbackFuel + extra) metadata uv (.inl fragment) before.core) = [.ok (result, after)]) :
    ∃ bound outcome,
      (∀ extra, continueWith
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) depth)
        graph templates stop order (bound + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final depth seed ceiling) outcome ∧
      programOutputs valid marked outcome := by
  have callback (extra : Nat)
      (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → RoleResult) :
      continueWith recur graph templates stop order (callbackFuel + extra) metadata uv fragment
        caller memos.query before =
        if result.1 then .complete [] caller memos.query
        else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
          (SourcePruningEnumerationRestart.decision stop order result.2
            (EnumerationExpandableIndex.frame after before)) := by
    unfold continueWith
    rw [recorded extra]
    obtain ⟨flag, updated⟩ := result
    cases flag <;> rfl
  by_cases rejected : result.1 = true
  · have resources : OutcomeResources (Typing := Typing) formulas solver caller seed
        (.complete [] caller memos.query) := by
      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have growth := SourcePruningEnumerationSharedPreparedReservation.final_ge depth seed ceiling
    refine ⟨callbackFuel, .complete [] caller memos.query, ?_, resources.mono growth.1 growth.2, ?_⟩
    · intro extra
      rw [callback extra, ite_eq_left rejected]
    · intro output member
      exact (List.not_mem_nil member).elim
  · have afterSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
      caller.checked.native.machine.heap before.core after marked framed slots
    have afterMass : SourcePruningEnumerationPrefixAdmission.suspendedBound
        (EnumerationExpandableIndex.frame after before).core ≤ ceiling := by
      change SourcePruningEnumerationPrefixAdmission.suspendedBound after ≤ ceiling
      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after framed.values]
      exact mass
    obtain ⟨resumeFuel, outcome, running, resources, outputRoles⟩ := recursive
      inventory caller memos (EnumerationExpandableIndex.frame after before) result.2 seed ceiling
      returned bounded known selectionMembers selectionLength afterMass reserved valid marked afterSlots
    refine ⟨callbackFuel + resumeFuel, outcome, ?_, resources, outputRoles⟩
    intro extra
    have actual := callback (resumeFuel + extra)
      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        (callbackFuel + resumeFuel + extra) depth)
    rw [← Nat.add_assoc] at actual
    rw [actual, ite_eq_right rejected]
    have observed := running (callbackFuel + extra)
    have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
    rw [common] at observed
    exact observed

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem observed_narrow_fields
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel uv : Nat) (value result : Node) (heap after : NativeHeap)
    (valid : Constraint → Prop)
    (ready : SourceEqualityRequiredCache.Ready heap) (available : Available heap value)
    (fields : ValueFields valid literal value)
    (actual : SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value heap = .done result after) :
    ValueFields valid literal result := by
  by_cases inside : uv ∈ metadata.types
  · have same := (MergedSourceComparison.Result.done.inj
      ((SourcePruningOuterNarrow.narrow_type holeKey fits admits metadata fuel uv value heap inside).symm.trans actual)).1
    exact same ▸ fields
  · cases fields with
    | empty =>
        have fallback := SourcePruningOuterNarrow.narrow_fallback holeKey fits admits metadata fuel uv
          .empty heap (by intro entry body depth ordinary impossible; cases impossible) inside
        have same := (MergedSourceComparison.Result.done.inj
          ((fallback.trans (SourcePruningEnumerationIdentity.narrowAt_empty fits admits fuel _ heap)).symm.trans actual)).1
        exact same ▸ ValueFields.empty
    | node entry rows depth free checked =>
        rw [SourcePruningOuterNarrow.narrow_fallback holeKey fits admits metadata fuel uv
          (.node entry rows depth free) heap
          (by intro other body nested ordinary impossible; cases impossible) inside] at actual
        change MergedSourceComparison.Result.done
          (InternedConstructorTemplates.run (makeNode (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv)))) heap).1
          (InternedConstructorTemplates.run (makeNode (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv)))) heap).2 =
            .done result after at actual
        have facts := ready.semantic.1.normal.facts
        have constructed := SourceSynthesisHereditaryProgramFields.makeNode_fields valid literal
          (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) heap facts
          (fun edge member => InternedEdgeResidency.resident_edges heap facts.linked _ available.resident edge (List.mem_filter.mp member).1)
          (fun edge member => checked edge (List.mem_filter.mp member).1)
        exact (MergedSourceComparison.Result.done.inj actual).1 ▸ constructed

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem observed_write_slots
    (valid : Constraint → Prop) (heap : NativeHeap) (before after : Core) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal heap before marked) (target : Nat) (payload : UVarValue Symbol)
    (allowed : ∀ uv, marked uv → EnumerationReferences.InputsAllowed
      (fun other => ¬UnionFind.SameClass before.representatives uv other) (references payload))
    (checked : marked target → SlotRole valid literal heap marked payload)
    (written : Success (setValue target payload) before () after) :
    ProgramSlots valid literal heap after marked := by
  have shape := (EnumerationDriver.modify_success _ before after).mp written
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro uv known
    simpa only [shape] using slots.bounded uv known
  · intro uv known
    simpa only [shape] using slots.roots uv known
  · intro uv known
    have incoming := EnumerationReferences.setValue_allowed
      (fun other => ¬UnionFind.SameClass before.representatives uv other) target payload before after
      (slots.incoming uv known) (allowed uv known) written
    simpa only [EnumerationReferences.IncomingAvoid, shape] using incoming
  · intro uv known
    by_cases same : uv = target
    · subst uv
      obtain ⟨old, stored, _role⟩ := slots.stored target known
      have inside := (List.getElem?_eq_some_iff.mp stored).1
      exact ⟨payload, by simpa only [shape] using (List.getElem?_set_self inside :
        (before.values.set target payload)[target]? = some payload), checked known⟩
    · obtain ⟨old, stored, role⟩ := slots.stored uv known
      exact ⟨old, by simpa only [shape, List.getElem?_set_ne (Ne.symm same)] using stored, role⟩

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem observed_narrow_available
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel uv : Nat) (value result : Node)
    (before after : InternedConstructorTemplates.State Symbol Constraint)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = [])
    (actual : SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value before =
      .done result after) : Available after result ∧ result.free = [] := by
  have skipped (same : result = value ∧ after = before) : Available after result ∧ result.free = [] := by
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨available, closed⟩
  by_cases typed : uv ∈ metadata.types
  · have pureDone := SourcePruningOuterNarrow.narrow_type holeKey fits admits metadata fuel uv value before typed
    have same := MergedSourceComparison.Result.done.inj (pureDone.symm.trans actual)
    exact skipped ⟨same.1.symm, same.2.symm⟩
  · cases value with
    | mu =>
        have same := MergedSourceComparison.Result.done.inj actual
        exact skipped ⟨same.1.symm, same.2.symm⟩
    | empty | reference | node | union =>
        have narrowed := actual
        simp [SourcePruningOuterNarrow.narrow, typed] at narrowed
        obtain ⟨rows, middle, exposed, built, _meaning⟩ := SourcePruningNativeView.narrowAt_edges
          (fun _ _ => true) (fun _ _ => False) fits admits (holeKey metadata.typing uv) fuel _ before
          result after ready available closed narrowed
        have verified := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel _ before
          ready.semantic ready.covered available closed
        have semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap middle := by
          simpa only [exposed, MergedSourceExposure.Result.state] using verified.semantic
        have resident : InternedNestedProvenance.Edges middle
            (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) :=
          fun edge member => verified.edges rows middle exposed edge (List.mem_filter.mp member).1
        have children : ∀ child ∈ (rows.filter
            (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))).flatMap EdgeValue.children,
            Available middle child := by
          intro child member
          obtain ⟨edge, member, included⟩ := List.mem_flatMap.mp member
          exact semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge member) child included
        have constructed := InternedProbeProvenance.makeNode_available
          (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) middle
          semantic.1.normal.facts.coherent semantic.1.normal.facts.cached children
        have closedRows : MergedColdReaderClosedInputs.ClosedEdges
            (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) :=
          fun edge member => verified.closed rows middle exposed edge (List.mem_filter.mp member).1
        have constructedClosed := MergedColdReaderClosedInputs.makeNode_closed
          (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))) middle
          semantic.1.normal.facts resident closedRows
        rw [built] at constructed constructedClosed
        exact ⟨constructed.2.2, constructedClosed⟩

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem observed_prefix_action
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (fuel uv : Nat) (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
    (oldHandle : Nat) (scs : List Suspended) (readAfter checked : Core) (oldValue value : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (selectedAction : EnumerateM Symbol Constraint Unit)
    (result : SourcePruningEnumerationSelectedStep.Result (bits + 2) Typing) (raw : List (Except Error (Unit × Core)))
    (reading : ExceptT.run (getValue fuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (checking : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
      fuel uv oldHandle scs readAfter) = [.ok (false, checked)])
    (decoded : lookupNode caller.checked.native.machine.heap oldHandle = some oldValue)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata fuel fuel
      uv oldHandle scs oldValue caller.checked.native.machine.heap = .done (value, some selectedAction) heap)
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
      uv caller before queries = result)
    (field : (match (generalizing := false) result with | .narrowed _ _ _ _ action _ _ _ => action | _ => none) = some raw) :
    ExceptT.run (selectedAction checked) = raw := by
  have copied : (match (generalizing := false)
      SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before queries with
    | .narrowed _ _ _ _ action _ _ _ => action
    | _ => none) = some (ExceptT.run (selectedAction checked)) := by
    simp only [SourcePruningEnumerationSelectedStep.runPrefix,
      SourcePruningEnumerationSelectedStep.runPrefixWithNarrow,
      ← SourcePruningEnumerationAction.prepare_configured_eq, reading, checking, decoded, prepared]
    cases execution : ExceptT.run (selectedAction checked) with
    | nil => rfl
    | cons first rest =>
        cases rest with
        | cons _ _ =>
            cases first with
            | error _ => rfl
            | ok pair =>
                obtain ⟨token, _observed⟩ := pair
                cases token
                rfl
        | nil =>
            cases first with
            | error _ => rfl
            | ok pair =>
                obtain ⟨token, observed⟩ := pair
                cases token
                dsimp only
                cases encodeNode value with
                | none => rfl
                | some newHandle =>
                    dsimp only
                    cases SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv oldHandle newHandle scs
                      before observed with
                    | none => rfl
                    | some attached =>
                        rw [SourcePruningRecordTypes.recordTypes_inr]
                        rfl
  have fields := (congrArg (fun observed : SourcePruningEnumerationSelectedStep.Result (bits + 2) Typing => match observed with
    | .narrowed _ _ _ _ action _ _ _ => action
    | _ => none) actual).trans field
  exact Option.some.inj (copied.symm.trans fields)

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem observed_prepared_slots
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (oldValue value : Node) (heap nextHeap : NativeHeap)
    (action : EnumerateM Symbol Constraint Unit) (before readAfter checked after : Core)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal heap before marked)
    (ready : EnumerationDriver.Ready uv before)
    (nativeReady : SourceEqualityRequiredCache.Ready heap)
    (realized : SourcePruningEnumerationObservation.PendingRealized heap before)
    (kept : SourceEqualityRequiredCache.Keeps heap nextHeap)
    (decoded : lookupNode heap oldHandle = some oldValue)
    (reading : Success (getValue fuel uv) before (.unenumerated (some oldHandle) scs) readAfter)
    (checking : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv oldHandle scs)
      readAfter false checked)
    (narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv oldValue heap =
      .done value nextHeap)
    (nonempty : value ≠ .empty) (encoded : encodeNode value = some newHandle)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata fuel fuel
      uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (executed : Success action checked () after) :
    ProgramSlots valid literal nextHeap after marked := by
  obtain ⟨readFrame, root, size, oldPath, _readPath, oldStored⟩ :=
    getValue_frame fuel uv before readAfter _ ready.safe.1.total reading
  have checkFrame := SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame heap fuel uv oldHandle scs
    readAfter checked (readFrame.total ready.safe.1.total) checking
  have checkedFrame := readFrame.trans checkFrame
  have nativeSlots := SourceSynthesisProgramRolesNativeHeap.keeps_program_slots heap nextHeap before marked kept slots
  have checkedSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
    nextHeap before checked marked checkedFrame nativeSlots
  have selectedAction := SourcePruningEnumerationSelectedStep.prepared_action holeKey fits admits metadata
    fuel fuel uv oldHandle newHandle scs oldValue value heap nextHeap narrowed nonempty encoded
  rw [prepared] at selectedAction
  have actionSame : action =
      (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
        else representative fuel uv >>= fun selected => setValue selected (.unenumerated (some newHandle) scs)) :=
    Option.some.inj (Prod.mk.inj (MergedSourceComparison.Result.done.inj selectedAction).1).2
  rw [actionSame] at executed
  by_cases same : newHandle = oldHandle
  · rw [ite_eq_left same] at executed
    obtain ⟨_unit, afterSame⟩ := (success_pure () () checked after).mp executed
    simpa only [afterSame] using checkedSlots
  · rw [ite_eq_right same] at executed
    obtain ⟨selected, resolved, resolution, writing⟩ := (success_bind _ _ _ _ _).mp executed
    have resolvedFrame := representative_frame fuel uv selected checked resolved
      (checkedFrame.total ready.safe.1.total) resolution
    have wholeFrame := checkedFrame.trans resolvedFrame
    obtain ⟨found, lookup, selectedSame, _resolvedSame⟩ :=
      (representative_success fuel uv checked resolved selected).mp resolution
    have path := (UnionFind.findRoot_correct fuel checked.representatives uv found lookup).1
    have rootSame : selected = root := selectedSame.trans
      (UnionFind.reaches_unique path ((checkedFrame.reaches uv root size).mpr oldPath)).1
    have stored : resolved.values[selected]? = some (.unenumerated (some oldHandle) scs) := by
      simpa only [wholeFrame.values, rootSame] using oldStored
    have resolvedSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
      nextHeap checked resolved marked resolvedFrame checkedSlots
    apply observed_write_slots valid nextHeap resolved after marked resolvedSlots selected
      (.unenumerated (some newHandle) scs) ?_ ?_ writing
    · intro held tagged
      change EnumerationReferences.InputsAllowed
        (fun other => ¬UnionFind.SameClass resolved.representatives held other) scs
      exact resolvedSlots.incoming held tagged (.unenumerated (some oldHandle) scs)
        (List.mem_of_getElem? stored)
    · intro tagged
      have oldStoredAtUv : before.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
        have actualStored := (EnumerationDriver.getValue_root fuel uv before readAfter _
          ready.safe ready.inside ready.root reading).2.2.2
        simpa only [readFrame.values] using actualStored
      obtain ⟨original, originalDecoded, oldAvailable, oldClosed⟩ := realized uv oldHandle scs oldStoredAtUv
      have originalSame : original = oldValue := Option.some.inj (originalDecoded.symm.trans decoded)
      subst original
      obtain ⟨payload, present, role⟩ := resolvedSlots.stored selected tagged
      have payloadSame : payload = .unenumerated (some oldHandle) scs :=
        Option.some.inj (present.symm.trans stored)
      subst payload
      cases role with
      | pending handle bucket source found fields validTries annotationPaths =>
          have retained := lookupNode_keeps heap nextHeap kept oldHandle oldValue decoded
          have sourceSame : source = oldValue := Option.some.inj (found.symm.trans retained)
          have oldFields : ValueFields valid literal oldValue := sourceSame ▸ fields
          have newFields := observed_narrow_fields holeKey fits admits metadata fuel uv oldValue value heap nextHeap
            valid nativeReady oldAvailable oldFields narrowed
          have resultAvailable := observed_narrow_available holeKey fits admits metadata fuel uv oldValue value
            heap nextHeap nativeReady oldAvailable oldClosed narrowed
          obtain ⟨actualHandle, actualEncoded, actualDecoded⟩ := available_readback nextHeap value
            kept.ready.semantic.1.normal.facts.coherent resultAvailable.1 resultAvailable.2
          have handleSame : actualHandle = newHandle := Option.some.inj (actualEncoded.symm.trans encoded)
          subst actualHandle
          exact .pending newHandle scs value actualDecoded newFields validTries annotationPaths

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem observed_repeated_slots
    (heap : NativeHeap) (fuel uv handle : Nat) (scs : List Suspended)
    (before readAfter checked : Core) (safe : Safe before)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal heap before marked)
    (reading : Success (getValue fuel uv) before (.unenumerated (some handle) scs) readAfter)
    (checking : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      readAfter true checked) : ProgramSlots valid literal heap checked marked := by
  obtain ⟨readFrame, oldRoot, size, oldPath, _readPath, oldStored⟩ :=
    getValue_frame fuel uv before readAfter _ safe.1.total reading
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) readAfter true checked := by
        simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using checking
      exact (success_failure .unresolvedReference readAfter checked true impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at checking
        obtain ⟨selected, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp checking
        have resolvedFrame := representative_frame fuel uv selected readAfter resolved
          (readFrame.total safe.1.total) resolution
        have wholeFrame := readFrame.trans resolvedFrame
        obtain ⟨found, lookup, selectedSame, _resolvedSame⟩ :=
          (representative_success fuel uv readAfter resolved selected).mp resolution
        have path := (UnionFind.findRoot_correct fuel readAfter.representatives uv found lookup).1
        have rootSame : selected = oldRoot := selectedSame.trans
          (UnionFind.reaches_unique path ((readFrame.reaches uv oldRoot size).mpr oldPath)).1
        have stored : resolved.values[selected]? = some (.unenumerated (some handle) scs) := by
          simpa only [wholeFrame.values, rootSame] using oldStored
        have resolvedSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
          heap before resolved marked wholeFrame slots
        obtain ⟨current, currentState, read, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨currentSame, stateSame⟩ := (EnumerationDriver.get_success resolved currentState current).mp read
        subst current
        subst currentState
        by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry selected
        · rw [ite_eq_left seen] at continued
          obtain ⟨token, written, writing, finished⟩ := (success_bind _ _ _ _ _).mp continued
          cases token
          obtain ⟨_answer, afterSame⟩ := (success_pure true true written checked).mp finished
          rw [afterSame]
          apply observed_write_slots valid heap resolved written marked resolvedSlots selected
            (.unenumerated (some handle) []) ?_ ?_ writing
          · intro held tagged sc member
            cases member
          · intro tagged
            obtain ⟨payload, present, role⟩ := resolvedSlots.stored selected tagged
            have payloadSame : payload = .unenumerated (some handle) scs :=
              Option.some.inj (present.symm.trans stored)
            subst payload
            cases role with
            | pending native bucket original found fields _validTries _annotationPaths =>
                have same : original = value := Option.some.inj (found.symm.trans decoded)
                have valueFields : ValueFields valid literal value := same ▸ fields
                cases valueFields <;> cases boundary
        · rw [ite_eq_right seen] at continued
          obtain ⟨impossible, _same⟩ := (success_pure false true resolved checked).mp continued
          cases impossible
      · have impossible : Success (pure false : EnumerateM Symbol Constraint Bool) readAfter true checked := by
          simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, ite_eq_right boundary] using checking
        obtain ⟨contradiction, _same⟩ := (success_pure false true readAfter checked).mp impossible
        cases contradiction

private theorem observed_finish_shape
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (uv : Nat) (observed : SourcePruningEnumerationSelectedStep.Result (bits + 2) Typing) :
    match observed with
    | .stopped _ _ | .parked _ _ _ =>
        SourcePruningEnumerationSelectedStep.finish checkEmpty edgesOf 0 0 0 0 0 uv observed = observed
    | .narrowed checked prepared reached queries action candidate right _ =>
        ∃ ordinary, SourcePruningEnumerationSelectedStep.finish checkEmpty edgesOf 0 0 0 0 0 uv observed =
          .narrowed checked prepared reached queries action candidate right ordinary := by
  cases observed with
  | stopped _ _ => rfl
  | parked _ _ _ => rfl
  | narrowed checked prepared reached queries action candidate right ordinary =>
      dsimp only
      unfold SourcePruningEnumerationSelectedStep.finish
      split <;> simp_all only [SourcePruningEnumerationSelectedStep.Result.narrowed.injEq] <;> subst_vars <;>
        simp only [true_and] <;> exact ⟨_, rfl⟩

/-- The same actual prefix observation retains the marked Program slots. -/
theorem observed_prefix_slots
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (observed : SourcePruningEnumerationSelectedStep.Result (bits + 2) Typing)
    (receipt : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates
      checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos observed)
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata fuel fuel fuel fuel fuel fuel uv caller before memos.query = observed) :
    match (generalizing := false) observed with
    | .parked _ (some after) _ =>
        ProgramSlots valid literal caller.checked.native.machine.heap after.core marked
    | .narrowed _ _ reached _ _ (some after) _ _ =>
        ProgramSlots valid literal reached.checked.native.machine.heap after.core marked
    | _ => True := by
  have full := receipt.2.1
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  cases observed with
  | stopped _ _ => trivial
  | parked checked candidate raw =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨oldHandle, scs, readAfter, reading, checking, cached, same, core,
            _cacheValid, _safe, _pending, _counter, _ordered, _raw⟩ := full
          have cacheSame : after = cached := Option.some.inj same
          subst cached
          have readSuccess : Success (getValue fuel uv) before.core
              (.unenumerated (some oldHandle) scs) readAfter := by
            rw [Success, reading]
            exact List.mem_singleton_self _
          have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
              caller.checked.native.machine.heap fuel uv oldHandle scs) readAfter true checked := by
            rw [Success, checking]
            exact List.mem_singleton_self _
          have retained := observed_repeated_slots caller.checked.native.machine.heap fuel uv oldHandle scs
            before.core readAfter checked packet.safe valid marked slots readSuccess checkSuccess
          simpa only [core] using retained
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨nextOrdinary, finished⟩ := observed_finish_shape checkEmpty edgesOf uv
            (.narrowed checked prepared reached queries action (some after) right ordinary)
          rw [finished] at full
          obtain ⟨oldHandle, scs, readAfter, reading, checking, oldValue, value, heap, selectedAction,
            final, decoded, narrowed, preparedActual, _preparedField, reachedSame, _queriesSame,
            post, _querySame, shape⟩ := full
          rcases shape with ⟨_empty, _action, impossible, _right, _ordinary⟩ |
            ⟨newHandle, cached, nonempty, encoded, actionSame, cachedSame, _cacheValid, _safe,
              _pending, _ready, _stored, _waiting, _right, _rest⟩
          · cases impossible
          · have cacheSame : after = cached := Option.some.inj cachedSame
            subst cached
            have rawAction := observed_prefix_action holeKey fits admits graph templates stop order metadata
              fuel uv caller before memos.query oldHandle scs readAfter checked oldValue value heap selectedAction
              (.narrowed checked prepared reached queries action (some after) right ordinary)
              [.ok ((), after.core)] reading checking decoded preparedActual actual actionSame
            have executed : Success selectedAction checked () after.core := by
              rw [Success, rawAction]
              exact List.mem_singleton_self _
            have readSuccess : Success (getValue fuel uv) before.core
                (.unenumerated (some oldHandle) scs) readAfter := by
              rw [Success, reading]
              exact List.mem_singleton_self _
            have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
                caller.checked.native.machine.heap fuel uv oldHandle scs) readAfter false checked := by
              rw [Success, checking]
              exact List.mem_singleton_self _
            have reachedHeap : reached.checked.native.machine.heap = heap := by
              rw [reachedSame]
              rfl
            have kept : SourceEqualityRequiredCache.Keeps caller.checked.native.machine.heap heap := by
              rw [← reachedHeap]
              exact post.effects.keeps
            have retained := observed_prepared_slots holeKey fits admits metadata fuel uv oldHandle newHandle scs
              oldValue value caller.checked.native.machine.heap heap selectedAction before.core readAfter checked
              after.core valid marked slots ready packet.context.ready.semantic.ready realized
              kept decoded readSuccess checkSuccess narrowed nonempty encoded preparedActual executed
            simpa only [reachedHeap] using retained

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem prepend_scan_program
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original middle : Caller (bits + 2)) (middleMemos : Memos) (middleInventory : Inventory)
    (headSeed finalSeed : Seed) (uv : Nat)
    (receipt : SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result (bits + 2))
    (headOutputs : List (Output (bits + 2) Typing))
    (later : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
      (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2))
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (headPost : Post formulas solver middleInventory original middle middleMemos)
    (growth : SourceCurrentAllocatedNativeResourceForecast.Le headSeed.2 finalSeed.2)
    (alphabet : headSeed.1 ⊆ finalSeed.1)
    (headResources : OutcomeResources formulas solver original headSeed
      (.complete headOutputs middle middleMemos.query))
    (headRoles : programOutputs valid marked (.complete headOutputs middle middleMemos.query))
    (tailResources : OutcomeResources formulas solver middle finalSeed (finish uv later))
    (tailRoles : programOutputs valid marked (finish uv later)) :
    let combined := match (generalizing := false) later with
      | .complete receipts outputs reached queries =>
          .complete (receipt :: receipts) (headOutputs ++ outputs) reached queries
      | .stopped receipts outputs reason => .stopped (receipt :: receipts) (headOutputs ++ outputs) reason
    OutcomeResources formulas solver original finalSeed (finish uv combined) ∧
      programOutputs valid marked (finish uv combined) := by
  obtain ⟨_headCaller, _headInventory, _headMemos, _headPost, _headFits, _headKnown,
    _callerSame, _querySame, headValid⟩ := headResources
  have headValidAt : ∀ output ∈ headOutputs, OutputResources formulas solver original finalSeed output :=
    fun output member => (headValid output member).mono growth alphabet
  cases later with
  | complete receipts outputs reached queries =>
      obtain ⟨actual, next, final, post, bounded, known, callerSame, querySame, tailValid⟩ := tailResources
      constructor
      · refine ⟨actual, next, final, headPost.trans post, bounded, known, callerSame, querySame, ?_⟩
        intro output member
        rcases List.mem_append.mp member with first | rest
        · exact headValidAt output first
        · exact (tailValid output rest).post headPost
      · intro output member
        rcases List.mem_append.mp member with first | rest
        · exact headRoles output first
        · exact tailRoles output rest
  | stopped receipts outputs reason =>
      obtain ⟨actual, next, final, post, bounded, known, observed, tailValid⟩ := tailResources
      constructor
      · refine ⟨actual, next, final, headPost.trans post, bounded, known, observed, ?_⟩
        intro output member
        rcases List.mem_append.mp member with first | rest
        · exact headValidAt output first
        · exact (tailValid output rest).post headPost
      · intro output member
        rcases List.mem_append.mp member with first | rest
        · exact headRoles output first
        · exact tailRoles output rest

private theorem callback_program_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (depth : Nat)
    (recursive : programResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty
      edgesOf stop order formulas solver depth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (before : Cached) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragments.Fragment Symbol)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits depth seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked) :
    ∃ bound outcome,
      (∀ extra, continueWith
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) depth)
        graph templates stop order (bound + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final depth seed ceiling) outcome ∧
      programOutputs valid marked outcome := by
  obtain ⟨callbackFuel, result, after, returned, _stable, framed, _types, _holes, _typing,
    _currentFits, _currentKnown, callback⟩ := callback_complete_resources formulas solver inventory
      graph templates metadata uv fragment caller memos before seed packet allocated bounded known
  exact computed_callback_complete holeKey fits admits graph templates checkEmpty edgesOf stop order
    formulas solver depth recursive inventory caller memos before metadata uv fragment seed ceiling packet bounded
    known selectionMembers selectionLength mass reserved valid marked slots callbackFuel result after returned
    framed (fun extra => (callback extra).2.1)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
/-- A stable read retains the same marked Program slots. -/
theorem render_stable_slots
    (heap : NativeHeap) (before after : Core) (valid : Constraint → Prop) (marked : Nat → Prop)
    (stable : EnumerationDriver.RenderStable before after)
    (slots : ProgramSlots valid literal heap before marked) :
    ProgramSlots valid literal heap after marked := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro held tagged
    rw [stable.counter]
    exact slots.bounded held tagged
  · intro held tagged
    obtain ⟨payload, stored, role⟩ := slots.stored held tagged
    have actualStored : after.values[held]? = some payload := by simpa only [stable.values] using stored
    apply (stable.safe.2 held payload actualStored).mp
    intro impossible
    cases role <;> cases impossible
  · intro held tagged
    exact EnumerationReferences.incoming_read held before after stable (slots.incoming held tagged)
  · intro held tagged
    obtain ⟨payload, stored, role⟩ := slots.stored held tagged
    exact ⟨payload, by simpa only [stable.values] using stored, role⟩

omit [DecidableEq Symbol] [DecidableEq Node] in
/-- The same successful preparation retains the marked Program fields and bucket scope. -/
theorem prepared_marked_fields
    (entryFuel nativeFuel uv handle : Nat) (scs : List Suspended)
    (caller : Caller (bits + 2)) (before entered : Cached) (decoded value : Node) (heap : NativeHeap)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (lookup : lookupNode caller.checked.native.machine.heap handle = some decoded)
    (actual : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)))
    (tagged : marked uv) :
    ValueFields valid literal value ∧ EnumerationSemantics.ValidSuspended scs ∧
      SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion scs := by
  have raw := congrArg Prod.fst actual
  have prepared := congrArg Prod.snd actual
  simp only [SourcePruningEnumerationSelectedPreparation.run] at raw prepared
  rw [raw] at prepared
  have actualValue : SourcePruningEnumerationSelectedValue.run nativeFuel decoded
      caller.checked.native.machine.heap = .done value heap := Option.some.inj prepared
  obtain ⟨payload, present, role⟩ := slots.stored uv tagged
  have same : payload = .unenumerated (some handle) scs := Option.some.inj (present.symm.trans stored)
  subst payload
  cases role with
  | pending native bucket original found fields validTries annotationPaths =>
      have sameValue : original = decoded := Option.some.inj (found.symm.trans lookup)
      have originalFields : ValueFields valid literal decoded := sameValue ▸ fields
      have resultFields := SourceSynthesisSelectedProgramChildRetention.prepared_fields originalFields actualValue
      exact ⟨resultFields.2.2, validTries, annotationPaths⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem annotation_nonterminal
    (scs : List Suspended)
    (scope : SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion scs) :
    scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
  apply List.any_eq_false.mpr
  intro sc member tagged
  have terminal : sc.trie = .terminal := by
    cases trieRead : sc.trie with
    | empty => simp only [trieRead, EqualityTrie.isTerminal, Bool.false_eq_true] at tagged
    | terminal => rfl
    | branch children => simp only [trieRead, EqualityTrie.isTerminal, Bool.false_eq_true] at tagged
  obtain ⟨tail, impossible⟩ := scope sc member [] ((EqualityTrie.nil_mem sc.trie).mpr terminal)
  cases impossible

attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile

open InternedProbeProvenance SourcePruningEnumerationNodes
-- Private fragment for the SharedDriver namespace. No public law is claimed.
open SourcePruningEnumerationSharedNativeBranchCompletion (Admitted Pending FragmentHistory HeadCacheBounds edgeCost)
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "HookResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
local notation "advance" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "guardWidth" => SourcePruningEnumerationGuardWidth.width
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "afterHead" => SourcePruningEnumerationSharedPreparedReservation.afterHead
local notation "finiteStep" => SourcePruningEnumerationSharedPreparedReservation.step
local notation "massCeil" => SourcePruningEnumerationRecursiveReservation.massCeil

private theorem head_finite_complete_program
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : programResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (edge : EdgeValue Symbol Constraint)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry storedEdges depth free))
    (parentClosed : free = [])
    (selected : edge ∈ storedEdges) (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ selectedEdge ∈ edgesOf (.node entry rows depth free), selectedEdge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.HeadReserved bits recursiveFuel seed capturedMass inherited)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (fields : marked uv → SourceSynthesisHereditaryProgramFields.EdgeFields valid literal edge) :
    ∃ (bound : Nat) (receipt : Receipt (bits + 2)) (middleCaller : Caller (bits + 2))
      (saved : Queries) (middleMemos : Memos) (middleInventory : Inventory),
      (∀ extra, SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty
        (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs edge caller before memos.query = some receipt) ∧
      Post formulas solver middleInventory caller middleCaller middleMemos ∧ middleMemos.query = saved ∧
      Admitted uv receipt ∧ Pending receipt ∧ FragmentHistory before.core receipt ∧
      HeadCacheBounds before scs (scalar seed.2) (guardWidth seed.1) receipt ∧
      Fits (afterHead seed inherited).2 middleCaller.checked ∧
      Heap (fun guard => guard ∈ (afterHead seed inherited).1) middleCaller.checked.native.machine.heap ∧
      ((receipt = .unhandled ∧ arityAllows edge.children.length scs = true ∧
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint = none) ∨
        ∃ outcome : HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2),
          advance receipt = some (middleCaller, middleMemos.query) ∧
          (∀ extra, match (generalizing := false) receipt with
            | .complete fragment actual queries after =>
                continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
                  graph templates stop order (bound + extra) metadata uv fragment actual queries after = outcome
            | _ => outcome = .complete [] middleCaller middleMemos.query) ∧
          OutcomeResources formulas solver caller (finiteStep recursiveFuel seed capturedMass inherited) outcome ∧
          programOutputs valid marked outcome ∧
          match outcome with
          | .complete _ actual queries =>
              ∃ (next : Inventory) (final : Memos),
                Post formulas solver next caller actual final ∧ final.query = queries ∧
                Packet formulas solver next actual final metadata before ∧
                Fits (finiteStep recursiveFuel seed capturedMass inherited).2 actual.checked ∧
                Heap (fun guard => guard ∈ (finiteStep recursiveFuel seed capturedMass inherited).1)
                  actual.checked.native.machine.heap
          | .stopped _ _ _ => True) := by
  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨children, own⟩ := SourcePruningEnumerationRecursiveReservation.edge_shape_from_packet
    seed formulas solver inventory caller memos metadata before packet bounded known
    parentEntry storedEdges depth free parentAvailable edge selected
  have costBound := SourcePruningEnumerationSharedRecursiveReservation.edge_cost_le seed inherited scs
    before.core.counter edge children own inheritedLength
  have pending := EnumerationReferences.pending_inputs before.core packet.pending uv (some handle) scs stored
  have headGrowth := SourcePruningEnumerationSharedPreparedReservation.afterHead_ge seed inherited
  have stepGrowth := SourcePruningEnumerationSharedPreparedReservation.step_ge recursiveFuel seed capturedMass inherited
  have headKnown : Heap (fun guard => guard ∈ (afterHead seed inherited).1)
      caller.checked.native.machine.heap := fun key resident found => headGrowth.2 (known key resident found)
  have stepKnown : Heap (fun guard => guard ∈ (finiteStep recursiveFuel seed capturedMass inherited).1)
      caller.checked.native.machine.heap := fun key resident found => stepGrowth.2 (known key resident found)
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        refine ⟨0, .unhandled, caller, memos.query, memos, inventory, ?_, Post.refl packet.context,
          rfl, trivial, trivial, trivial, trivial, bounded.mono headGrowth.1, headKnown,
          .inl ⟨rfl, allowed, rfl⟩⟩
        intro extra
        rw [SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run,
          SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.unsupported checkEmpty _ _ _ _ _
            scs edge caller before memos.query allowed projected]
    | some pair =>
        obtain ⟨tries, residual⟩ := pair
        have actualCost : edgeCost scs before.core.counter edge =
            SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs before.core.counter tries := by
          simp only [edgeCost, allowed, ↓reduceIte, projected]
        have actualReserved := reserved.edge costBound
        rw [actualCost] at actualReserved
        have rawPadding := SourcePruningEnumerationSharedRecursiveReservation.head_padding seed inherited
          (edgeCost scs before.core.counter edge) costBound
        have padding := rawPadding
        simp only [actualCost] at padding
        have captured :
            ∃ (r n p h k : Nat) (reached : Caller (bits + 2)) (after : Cached) (saved : Queries)
              (final : Memos) (next : Inventory) (receipt : Receipt (bits + 2)),
              (∀ er en P H ek, p ≤ P → h ≤ H →
                SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty
                  (r + er) (n + en) P H (k + ek) uv scs edge caller before memos.query = some receipt) ∧
              Post formulas solver next caller reached final ∧ final.query = saved ∧
              Admitted uv receipt ∧ Pending receipt ∧ FragmentHistory before.core receipt ∧
              Fits (afterHead seed inherited).2 reached.checked ∧
              Heap (fun guard => guard ∈ (afterHead seed inherited).1) reached.checked.native.machine.heap ∧
              ((∃ fragment, receipt = .complete fragment reached saved after) ∨
                ∃ fragments outer waiting, receipt = .stopped fragments
                  (.ok (some []), reached, saved, outer, waiting) (some after)) ∧
              ∃ extended : Nat → Prop, (∀ held, marked held → extended held) ∧
                ProgramSlots valid literal reached.checked.native.machine.heap after.core extended ∧
                ∀ fragment, receipt = .complete fragment reached saved after →
                  ∃ (callbackFuel : Nat) (recorded : Bool × Metadata Typing) (recordAfter : Core),
                    Packet formulas solver next reached final metadata after ∧
                    Packet formulas solver next reached final recorded.2
                      (EnumerationExpandableIndex.frame recordAfter after) ∧
                    EnumerationCompressionFrame.Frame after.core recordAfter ∧
                    ∀ extra, ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates
                      (callbackFuel + extra) metadata uv (.inl fragment) after.core) = [.ok (recorded, recordAfter)] := by
          by_cases programTarget : marked uv
          · obtain ⟨r, n, p, h, k, reached, after, saved, final, next, afterRoots, receipt,
                ⟨running, post, queries, growth, afterPaths, afterStorage, afterRealized, afterCounts,
                  afterFlags, _origin, _retained, _protects, pendingHistory, shape, returnedFits, returnedKnown⟩,
                extended, extension, afterSlots, callback⟩ :=
              SourceSynthesisProgramRolesCapturedEdge.complete_with_history_resources_program_slots
                seed formulas solver inventory caller before checkEmpty uv handle scs parentEntry storedEdges depth free
                edge roots memos packet.context ready stored parentAvailable parentClosed realized selected paths counts flags
                pending allowed tries residual projected bounded actualReserved known graph templates metadata packet
                valid marked slots programTarget (fields programTarget)
            have cacheValid : SourcePruningEnumerationNativeBranchCompletion.CacheValid reached after :=
              ⟨afterRoots, afterPaths, afterStorage, afterRealized, afterCounts, afterFlags⟩
            have basics : Admitted uv receipt ∧ Pending receipt ∧ FragmentHistory before.core receipt ∧
                ((∃ fragment, receipt = .complete fragment reached saved after) ∨
                  ∃ fragments outer waiting, receipt = .stopped fragments
                    (.ok (some []), reached, saved, outer, waiting) (some after)) := by
              rcases shape with ⟨fragment, completed, safe, allocated, written, ancestry, root, fragmentPending, ordered⟩ |
                ⟨fragments, outer, waiting, stopped⟩
              · subst receipt
                exact ⟨⟨cacheValid, safe, allocated, written, ancestry, root⟩, pendingHistory packet.pending incoming,
                  ⟨growth, fragmentPending, ordered⟩, .inl ⟨fragment, rfl⟩⟩
              · subst receipt
                exact ⟨cacheValid, pendingHistory packet.pending incoming, trivial, .inr ⟨fragments, outer, waiting, rfl⟩⟩
            refine ⟨r, n, p, h, k, reached, after, saved, final, next, receipt, running, post, queries,
              basics.1, basics.2.1, basics.2.2.1, returnedFits.mono padding.1,
              (fun key resident found => padding.2 (returnedKnown key resident found)), basics.2.2.2,
              extended, extension, afterSlots, ?_⟩
            intro fragment completed
            obtain ⟨_fragmentRoles, current, _childrenAfter, _finalizeFuel, callbackFuel, recorded, recordAfter,
                _finalization, recording, _recordSlots⟩ := callback fragment completed
            obtain ⟨returned, _stable, frame, _types, _holes, _typing, _fits, _known, raw⟩ := recording
            exact ⟨callbackFuel, recorded, recordAfter, current, returned, frame, fun extra => (raw extra).2.1⟩
          · obtain ⟨r, n, p, h, k, reached, after, saved, final, next, afterRoots, receipt,
                running, post, queries, growth, afterPaths, afterStorage, afterRealized, afterCounts,
                afterFlags, _origin, _retained, _protects, pendingHistory, shape, returnedFits, returnedKnown,
                afterSlots⟩ :=
              SourceSynthesisProgramRolesUnmarkedCapturedEdge.complete_with_history_resources_prepared_program_slots
                seed formulas solver inventory caller before checkEmpty uv handle scs parentEntry storedEdges depth free
                edge roots memos packet.context ready stored parentAvailable parentClosed realized selected paths counts flags
                pending allowed tries residual projected bounded actualReserved known valid literal marked slots programTarget
            have cacheValid : SourcePruningEnumerationNativeBranchCompletion.CacheValid reached after :=
              ⟨afterRoots, afterPaths, afterStorage, afterRealized, afterCounts, afterFlags⟩
            have basics : Admitted uv receipt ∧ Pending receipt ∧ FragmentHistory before.core receipt ∧
                ((∃ fragment, receipt = .complete fragment reached saved after) ∨
                  ∃ fragments outer waiting, receipt = .stopped fragments
                    (.ok (some []), reached, saved, outer, waiting) (some after)) := by
              rcases shape with ⟨fragment, completed, safe, allocated, written, ancestry, root, fragmentPending, ordered⟩ |
                ⟨fragments, outer, waiting, stopped⟩
              · subst receipt
                exact ⟨⟨cacheValid, safe, allocated, written, ancestry, root⟩, pendingHistory packet.pending incoming,
                  ⟨growth, fragmentPending, ordered⟩, .inl ⟨fragment, rfl⟩⟩
              · subst receipt
                exact ⟨cacheValid, pendingHistory packet.pending incoming, trivial, .inr ⟨fragments, outer, waiting, rfl⟩⟩
            have returnedHeadFits := returnedFits.mono padding.1
            have returnedHeadKnown : Heap (fun guard => guard ∈ (afterHead seed inherited).1)
                reached.checked.native.machine.heap :=
              fun key resident found => padding.2 (returnedKnown key resident found)
            refine ⟨r, n, p, h, k, reached, after, saved, final, next, receipt, running, post, queries,
              basics.1, basics.2.1, basics.2.2.1, returnedHeadFits, returnedHeadKnown, basics.2.2.2,
              marked, (fun _ tagged => tagged), afterSlots, ?_⟩
            intro fragment completed
            have actualComplete : receipt = .complete fragment reached final.query after := by
              simpa only [queries] using completed
            have admitted : Admitted uv (.complete fragment reached final.query after) := actualComplete ▸ basics.1
            have history : FragmentHistory before.core (.complete fragment reached final.query after) :=
              actualComplete ▸ basics.2.2.1
            have actualPending : EnumerationReferences.PendingReferences after.core := by
              simpa only [actualComplete, Pending] using basics.2.1
            obtain ⟨level, frontier, ordered⟩ := packet.ordered
            have current := receipt_packet formulas solver next reached final metadata before.core uv fragment after
              level frontier post.context admitted history actualPending ordered packet.bounded
            obtain ⟨callbackFuel, recorded, recordAfter, returned, _stable, frame, _types, _holes, _typing,
                _fits, _known, raw⟩ := callback_complete_resources formulas solver next graph templates metadata uv fragment
              reached final after (afterHead seed inherited) current admitted.2.2.1 returnedHeadFits returnedHeadKnown
            exact ⟨callbackFuel, recorded, recordAfter, current, returned, frame, fun extra => (raw extra).2.1⟩
        obtain ⟨r, n, p, h, k, middleCaller, after, saved, middleMemos, middleInventory, receipt,
            headRun, headPost, headQueries, admitted, headPending, history, headFits, returnedKnown, shape,
            extended, extension, afterSlots, callback⟩ := captured
        have observed := headRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
        simp only [Nat.add_zero] at observed
        have cacheBounds := SourcePruningEnumerationSharedNativeBranchCompletion.observed_head_cache_bounds
          checkEmpty r n p h k uv scs edge caller before memos.query (scalar seed.2) (guardWidth seed.1)
          children own receipt observed
        let headBound := r + n + p + h + k
        have headAt (w : Nat) (large : headBound ≤ w) :
            SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty w w w w w
              uv scs edge caller before memos.query = some receipt := by
          have rl : r ≤ w := by dsimp [headBound] at large; omega
          have nl : n ≤ w := by dsimp [headBound] at large; omega
          have pl : p ≤ w := by dsimp [headBound] at large; omega
          have hl : h ≤ w := by dsimp [headBound] at large; omega
          have kl : k ≤ w := by dsimp [headBound] at large; omega
          have running := headRun (w - r) (w - n) w w (w - k) pl hl
          simpa only [Nat.add_sub_of_le rl, Nat.add_sub_of_le nl, Nat.add_sub_of_le kl] using running
        rcases shape with ⟨fragment, completed⟩ | ⟨fragments, outer, waiting, stopped⟩
        · subst receipt
          obtain ⟨callbackFuel, recorded, recordAfter, current, returned, frame, raw⟩ := callback fragment rfl
          have afterMass : suspendedBound after.core ≤ massCeil seed capturedMass inherited :=
            Nat.le_trans cacheBounds.2 (Nat.add_le_add initialMass
              (Nat.mul_le_mul_left _ (Nat.add_le_add_right inheritedLength _)))
          obtain ⟨callbackBound, outcome, running, resources, outputRoles⟩ :=
            computed_callback_complete holeKey fits admits graph templates checkEmpty edgesOf stop order
              formulas solver recursiveFuel recursive middleInventory middleCaller middleMemos after metadata uv fragment
              (afterHead seed inherited) (massCeil seed capturedMass inherited) current headFits returnedKnown
              selectionMembers selectionLength afterMass reserved.2 valid extended afterSlots
              callbackFuel recorded recordAfter returned frame raw
          have fullResources : OutcomeResources formulas solver caller
              (finiteStep recursiveFuel seed capturedMass inherited) outcome := resources.post headPost
          have finalRoles : programOutputs valid marked outcome := by
            intro output member
            obtain ⟨finalMarked, finalExtension, slots⟩ := outputRoles output member
            exact ⟨finalMarked, fun held tagged => finalExtension held (extension held tagged), slots⟩
          refine ⟨headBound + callbackBound, _, middleCaller, saved, middleMemos, middleInventory,
            ?_, headPost, headQueries, admitted, headPending, history, cacheBounds, headFits, returnedKnown,
            .inr ⟨outcome, ?_, ?_, fullResources, finalRoles, ?_⟩⟩
          · intro extra
            exact headAt (headBound + callbackBound + extra) (by omega)
          · simp only [SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance, headQueries]
          · intro extra
            have actual := running (headBound + extra)
            have common : callbackBound + (headBound + extra) = headBound + callbackBound + extra := by omega
            rw [common] at actual
            simpa only [headQueries] using actual
          · cases outcome with
            | stopped _ _ _ => trivial
            | complete outputs actual queries =>
                obtain ⟨next, final, post, query, capturedPacket, returnedFits, finalKnown, _outputs⟩ :=
                  completed_captured_packet formulas solver inventory caller memos metadata before
                    (finiteStep recursiveFuel seed capturedMass inherited) outputs actual queries packet fullResources
                exact ⟨next, final, post, query, capturedPacket, returnedFits, finalKnown⟩
        · subst receipt
          have resources : OutcomeResources (Typing := Typing) formulas solver caller (afterHead seed inherited)
              (.complete [] middleCaller middleMemos.query) :=
            ⟨middleCaller, middleInventory, middleMemos, headPost, headFits, returnedKnown, rfl, rfl,
              fun _ member => (List.not_mem_nil member).elim⟩
          have growth := SourcePruningEnumerationSharedPreparedReservation.afterHead_le_step
            recursiveFuel seed capturedMass inherited
          have fullResources := resources.mono growth.1 growth.2
          refine ⟨headBound, _, middleCaller, saved, middleMemos, middleInventory,
            (fun extra => headAt (headBound + extra) (by omega)), headPost, headQueries,
            admitted, headPending, history, cacheBounds, headFits, returnedKnown,
            .inr ⟨.complete [] middleCaller middleMemos.query, ?_, (fun _ => rfl), fullResources, ?_, ?_⟩⟩
          · simp only [SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance, headQueries]
          · intro output member
            exact (List.not_mem_nil member).elim
          · obtain ⟨next, final, post, query, capturedPacket, returnedFits, finalKnown, _outputs⟩ :=
              completed_captured_packet formulas solver inventory caller memos metadata before
                (finiteStep recursiveFuel seed capturedMass inherited) [] middleCaller middleMemos.query packet fullResources
            exact ⟨next, final, post, query, capturedPacket, returnedFits, finalKnown⟩
  · have rejected : arityAllows edge.children.length scs = false := by
      cases value : arityAllows edge.children.length scs with
      | false => rfl
      | true => exact (allowed value).elim
    have resources : OutcomeResources (Typing := Typing) formulas solver caller seed
        (.complete [] caller memos.query) :=
      ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl,
        fun _ member => (List.not_mem_nil member).elim⟩
    refine ⟨0, .rejected caller memos.query before, caller, memos.query, memos, inventory,
      ?_, Post.refl packet.context, rfl, ⟨roots, paths, storage, realized, counts, flags⟩,
      packet.pending, trivial, ⟨by omega, Nat.le_add_right _ _⟩, bounded.mono headGrowth.1, headKnown,
      .inr ⟨.complete [] caller memos.query, rfl, (fun _ => rfl), resources.mono stepGrowth.1 stepGrowth.2,
        ?_, inventory, memos, Post.refl packet.context, rfl, packet, bounded.mono stepGrowth.1, stepKnown⟩⟩
    · intro extra
      rw [SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run,
        SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.arity_rejected checkEmpty _ _ _ _ _
          scs edge caller before memos.query rejected]
    · intro output member
      exact (List.not_mem_nil member).elim

private theorem scan_finite_program
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : programResumeComplete (bits := bits) holeKey fits admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveFuel)
    (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges selectedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry storedEdges depth free))
    (parentClosed : free = [])
    (selected : ∀ edge ∈ selectedEdges, edge ∈ storedEdges)
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.ScanReserved bits recursiveFuel seed capturedMass inherited selectedEdges.length)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (fields : marked uv → ∀ edge ∈ selectedEdges,
      SourceSynthesisHereditaryProgramFields.EdgeFields valid literal edge) :
    ∃ (bound : Nat) (result : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
      (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs before selectedEdges caller memos.query = result) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.stage recursiveFuel seed capturedMass inherited selectedEdges.length)
        (finish uv result) ∧
      programOutputs valid marked (finish uv result) := by
  induction selectedEdges generalizing seed inventory caller memos with
  | nil =>
      refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_, ?_⟩
      · refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
        intro output member
        cases member
      · intro output member
        cases member
  | cons edge rest ih =>
      obtain ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
        headRun, headPost, headQueries, _admitted, _pending, _history, _cacheBounds, _headFits, _headKnown, shape⟩ :=
        head_finite_complete_program holeKey fits admits graph templates checkEmpty edgesOf stop order
          metadata recursiveFuel seed formulas solver recursive inventory caller memos before uv handle scs
          parentEntry storedEdges depth free edge packet ready stored parentAvailable parentClosed
          (selected edge List.mem_cons_self) incoming bounded known selectionMembers selectionLength
          capturedMass inherited initialMass inheritedLength reserved.head valid marked slots
          (fun tagged => fields tagged edge List.mem_cons_self)
      have laterGrowth := SourcePruningEnumerationSharedPreparedReservation.stage_ge recursiveFuel
        (SourcePruningEnumerationSharedPreparedReservation.step recursiveFuel seed capturedMass inherited)
        capturedMass inherited rest.length
      rcases shape with unsupported | ⟨outcome, advanced, callbackRun, resources, outputRoles, captured⟩
      · obtain ⟨unhandled, _allowed, _projected⟩ := unsupported
        subst receipt
        have wholeGrowth := SourcePruningEnumerationSharedPreparedReservation.stage_ge
          recursiveFuel seed capturedMass inherited (edge :: rest).length
        refine ⟨headBound, .stopped [] [] (.edge (some .unhandled) (caller, memos.query)), ?_, ?_, ?_⟩
        · intro extra
          simp only [SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run, headRun extra,
            SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance,
            SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.endpoint]
        · refine ⟨caller, inventory, memos, Post.refl packet.context, bounded.mono wholeGrowth.1,
            (fun key resident found => wholeGrowth.2 (known key resident found)), .inr rfl, ?_⟩
          intro output member
          cases member
        · intro output member
          cases member
      · cases outcome with
        | complete headOutputs hookCaller hookQueries =>
            obtain ⟨hookInventory, hookMemos, hookPost, hookQuery, hookCaptured, hookFits, hookKnown⟩ := captured
            have hookSlots := SourceSynthesisProgramRolesNativeHeap.keeps_program_slots
              caller.checked.native.machine.heap hookCaller.checked.native.machine.heap before.core marked
              hookPost.effects.keeps slots
            obtain ⟨tailBound, tailResult, tailRun, tailResources, tailRoles⟩ :=
              ih (SourcePruningEnumerationSharedPreparedReservation.step recursiveFuel seed capturedMass inherited)
                hookInventory hookCaller hookMemos hookCaptured
                (hookPost.effects.keeps.available (.node parentEntry storedEdges depth free) parentAvailable)
                (fun chosen member => selected chosen (List.mem_cons_of_mem _ member))
                hookFits hookKnown reserved.tail hookSlots
                (fun tagged chosen member => fields tagged chosen (List.mem_cons_of_mem _ member))
            let bound := headBound + tailBound
            let result : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
                (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
              match (generalizing := false) tailResult with
              | .complete receipts later actual queries =>
                  .complete (receipt :: receipts) (headOutputs ++ later) actual queries
              | .stopped receipts later current => .stopped (receipt :: receipts) (headOutputs ++ later) current
            have headQueryResources : OutcomeResources formulas solver caller
                (SourcePruningEnumerationSharedPreparedReservation.step recursiveFuel seed capturedMass inherited)
                (.complete headOutputs hookCaller hookMemos.query) := by
              simpa only [hookQuery] using resources
            have headQueryRoles : programOutputs valid marked (.complete headOutputs hookCaller hookMemos.query) := by
              exact outputRoles
            have joined := prepend_scan_program formulas solver caller hookCaller hookMemos hookInventory
              (SourcePruningEnumerationSharedPreparedReservation.step recursiveFuel seed capturedMass inherited)
              (SourcePruningEnumerationSharedPreparedReservation.stage recursiveFuel
                (SourcePruningEnumerationSharedPreparedReservation.step recursiveFuel seed capturedMass inherited)
                capturedMass inherited rest.length)
              uv receipt headOutputs tailResult valid marked hookPost laterGrowth.1 laterGrowth.2
              headQueryResources headQueryRoles tailResources tailRoles
            refine ⟨bound, result, ?_, ?_, joined.2⟩
            · intro extra
              let w := bound + extra
              have hl : headBound ≤ w := by dsimp [w, bound]; omega
              have tl : tailBound ≤ w := by dsimp [w, bound]; omega
              have first := headRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at first
              have hooked := callbackRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at hooked
              have continued : match (generalizing := false) receipt with
                  | .complete fragment actual queries after =>
                      continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                        graph templates stop order w metadata uv fragment actual queries after =
                        .complete headOutputs hookCaller hookQueries
                  | _ => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance receipt =
                      some (hookCaller, hookQueries) ∧ headOutputs = [] := by
                cases receipt with
                | complete fragment actual queries after => exact hooked
                | unhandled | finalizeStopped _ _ _ _ => cases advanced
                | rejected actual queries after | stopped fragments observation candidate =>
                    obtain ⟨empty, actual, queries⟩ :=
                      SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult.complete.inj hooked
                    exact ⟨by rw [actual, queries]; exact advanced, empty⟩
              have running := SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.continued_head
                (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                  graph templates stop order w metadata uv)
                checkEmpty w w w w w uv scs before edge rest caller hookCaller memos.query hookQueries
                receipt headOutputs first (by cases receipt <;> exact continued)
              have later := tailRun (w - tailBound)
              rw [Nat.add_sub_of_le tl, hookQuery] at later
              rw [later] at running
              cases tailResult <;> exact running
            · simpa only [List.length_cons, SourcePruningEnumerationSharedPreparedReservation.stage_succ]
                using joined.1
        | stopped headOutputs reason reached =>
            have completed : ∃ fragment actual queries after, receipt = .complete fragment actual queries after := by
              cases receipt with
              | complete fragment actual queries after => exact ⟨fragment, actual, queries, after, rfl⟩
              | unhandled | finalizeStopped _ _ _ _ => cases advanced
              | rejected actual queries after | stopped fragments observation candidate =>
                  have impossible := callbackRun 0
                  cases impossible
            obtain ⟨fragment, actual, queries, after, same⟩ := completed
            subst receipt
            have widened := resources.mono laterGrowth.1 laterGrowth.2
            obtain ⟨afterCaller, next, final, post, returnedFits, returnedKnown, observed, outputsValid⟩ := widened
            refine ⟨headBound,
              .stopped [] headOutputs (.continuation (.complete fragment actual queries after) reason reached),
              ?_, ?_, outputRoles⟩
            · intro extra
              simp only [SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run,
                headRun extra, callbackRun extra]
            · refine ⟨afterCaller, next, final, post, ?_, ?_, observed, ?_⟩
              · simpa only [List.length_cons, SourcePruningEnumerationSharedPreparedReservation.stage_succ]
                  using returnedFits
              · simpa only [List.length_cons, SourcePruningEnumerationSharedPreparedReservation.stage_succ]
                  using returnedKnown
              · intro output member
                simpa only [List.length_cons, SourcePruningEnumerationSharedPreparedReservation.stage_succ]
                  using outputsValid output member

private theorem opaque_finite_program
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : programResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (target handle : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready target before.core)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid target before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) = false)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.HeadReserved bits recursiveFuel seed capturedMass inherited)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (unmarked : ¬marked target) :
    ∃ (bound : Nat) (folded : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
      (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + extra) recursiveFuel) graph templates stop order (bound + extra) metadata target)
        caller memos.query (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
          (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          target scs value caller before memos.query) = folded) ∧
      OutcomeResources formulas solver caller (finiteStep recursiveFuel seed capturedMass inherited)
        (finish target folded) ∧ programOutputs valid marked (finish target folded) := by
  have positive : 1 ≤ scalar seed.2 := Nat.le_trans bounded.stored.positive
    (SourceCurrentConstrainedCapTargetForecast.scalar_mass seed.2)
  have pay := Nat.mul_le_mul_right (inherited + guardWidth seed.1 + 1) positive
  simp only [Nat.one_mul] at pay
  have costBound : scs.length + 1 ≤ SourcePruningEnumerationRecursiveReservation.edgeCount seed inherited := by
    unfold SourcePruningEnumerationRecursiveReservation.edgeCount
    omega
  obtain ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
    ⟨headRun, headPost, headQuery, advanced, admitted, _pending, _history, headFits, headKnown, shape,
      _finalization⟩, receiptRoles⟩ :=
    SourceSynthesisProgramRolesOpaque.opaque_complete_resources_program_slots seed formulas solver inventory
      caller memos metadata before checkEmpty target handle scs value packet ready stored incoming available closed
      dispatch bounded (reserved.1.prefix costBound) known valid marked slots unmarked
  have padding : SourceCurrentAllocatedNativeResourceForecast.Le
      (SourcePruningEnumerationSharedIncomingReservation.advance seed (scs.length + 1)).2
      (afterHead seed inherited).2 ∧
      (SourcePruningEnumerationSharedIncomingReservation.advance seed (scs.length + 1)).1 ⊆
        (afterHead seed inherited).1 :=
    ⟨SourcePruningEnumerationSharedIncomingReservation.advance_count_profile_mono seed costBound,
      SourcePruningEnumerationSharedIncomingReservation.advance_count_alphabet_mono seed costBound⟩
  have boundedHead := headFits.mono padding.1
  have knownHead : Heap (fun guard => guard ∈ (afterHead seed inherited).1)
      middleCaller.checked.native.machine.heap := fun key edge resident => padding.2 (headKnown key edge resident)
  have advancedQuery : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance receipt =
      some (middleCaller, middleMemos.query) := by simpa only [headQuery] using advanced
  have finishOther
      (notComplete : ∀ fragment actual queries after, receipt ≠ .complete fragment actual queries after) :
      ∃ bound folded,
        (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
          (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) recursiveFuel) graph templates stop order (bound + extra) metadata target)
          caller memos.query (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
            (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
            target scs value caller before memos.query) = folded) ∧
        OutcomeResources formulas solver caller (finiteStep recursiveFuel seed capturedMass inherited)
          (finish target folded) ∧ programOutputs valid marked (finish target folded) := by
    let folded : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
        (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
      .complete [receipt] [] middleCaller middleMemos.query
    have growth := SourcePruningEnumerationSharedPreparedReservation.final_ge recursiveFuel
      (afterHead seed inherited) (massCeil seed capturedMass inherited)
    refine ⟨headBound, folded, ?_, ?_, ?_⟩
    · intro extra
      rw [headRun extra]
      cases receipt with
      | complete fragment actual queries after => exact (notComplete fragment actual queries after rfl).elim
      | unhandled | finalizeStopped _ _ _ _ => cases advancedQuery
      | rejected actual queries after | stopped fragments observation candidate =>
          simp only [SourcePruningEnumerationSharedReceiptContinuation.run, advancedQuery, folded]
    · refine ⟨middleCaller, middleInventory, middleMemos, headPost, boundedHead.mono growth.1,
        (fun key edge found => growth.2 (knownHead key edge found)), rfl, rfl, ?_⟩
      intro output member
      cases member
    · intro output member
      cases member
  rcases shape with completed | stopped | rejected
  · obtain ⟨fragment, after, same, afterPacket, _counter, afterMass⟩ := completed
    subst receipt
    have massPay := Nat.mul_le_mul_right (inherited + guardWidth seed.1) positive
    simp only [Nat.one_mul] at massPay
    have mass : suspendedBound after.core ≤ massCeil seed capturedMass inherited := by
      unfold SourcePruningEnumerationRecursiveReservation.massCeil
      omega
    obtain ⟨callbackFuel, outcome, callbackRun, resources, outputRoles⟩ := callback_program_complete
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel recursive
      middleInventory middleCaller middleMemos after metadata target fragment (afterHead seed inherited)
      (massCeil seed capturedMass inherited) afterPacket admitted.2.2.1 boundedHead knownHead
      selectionMembers selectionLength mass reserved.2 valid marked receiptRoles
    let folded : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
        (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
      match (generalizing := false) outcome with
      | .complete outputs actual queries =>
          .complete [.complete fragment middleCaller saved after] outputs actual queries
      | .stopped outputs reason endpoint =>
          .stopped [] outputs (.continuation (.complete fragment middleCaller saved after) reason endpoint)
    have fullResources : OutcomeResources formulas solver caller
        (finiteStep recursiveFuel seed capturedMass inherited) outcome := by
      unfold SourcePruningEnumerationSharedPreparedReservation.step
      exact resources.post headPost
    refine ⟨headBound + callbackFuel, folded, ?_, ?_, ?_⟩
    · intro extra
      have first := headRun (callbackFuel + extra)
      rw [← Nat.add_assoc] at first
      rw [first]
      have continued := callbackRun (headBound + extra)
      have common : callbackFuel + (headBound + extra) = headBound + callbackFuel + extra := by omega
      rw [common, headQuery] at continued
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run, continued]
      cases outcome <;> rfl
    · cases outcome <;>
        simpa only [folded, finish, endpoint, OutcomeResources] using fullResources
    · cases outcome <;> exact outputRoles
  · obtain ⟨after, outer, waiting, same, _counter, _mass⟩ := stopped
    apply finishOther
    intro fragment actual queries cached impossible
    rw [same] at impossible
    cases impossible
  · apply finishOther
    intro fragment actual queries cached impossible
    rw [rejected] at impossible
    cases impossible

private theorem prepared_dispatch_program
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (recursiveFuel : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : programResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (ceiling : Nat) (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling) (inheritedLength : scs.length ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits (recursiveFuel + 1) seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked) :
    ∃ (bound : Nat) (observation : SourcePruningEnumerationSharedPreparedContinuations.Preparation)
      (folded : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, SourcePruningEnumerationSharedPreparedContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          (bound + extra) (bound + extra) (bound + extra) uv edgesOf caller before memos.query =
        (observation, some folded)) ∧
      OutcomeResources formulas solver caller (SourcePruningEnumerationSharedPreparedReservation.final (recursiveFuel + 1) seed ceiling) (finish uv folded) ∧ programOutputs valid marked (finish uv folded) := by
  let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
  obtain ⟨preparationFuel, decoded, value, heap, entered, retained,
    preparedFits, _valueMass, preparedKnown, frame, enteredIncoming, sameMass⟩ :=
    SourcePruningEnumerationSelectedPreparation.complete_resources_current
      formulas solver inventory caller memos metadata before uv handle scs packet ready stored
      (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 bounded incoming
      (fun guard => guard ∈ seed.1) known
  obtain ⟨preparationRun, _decodedLookup, preparationPost, enteredPacket, stable, enteredReady,
    enteredStored, _counter, _values, _flags, _waiting, available, closed, _meaning, _satisfaction⟩ := retained
  let preparedCaller := SourcePruningEnumerationSelectedValueCaller.advance caller heap
  have currentFits : Fits start.2 preparedCaller.checked := preparedFits
  have currentKnown : Heap (fun guard => guard ∈ start.1)
      preparedCaller.checked.native.machine.heap := preparedKnown
  have currentMass : SourcePruningEnumerationPrefixAdmission.suspendedBound entered.core ≤ ceiling := by
    rw [sameMass]
    exact initialMass
  have nativeSlots := SourceSynthesisProgramRolesNativeHeap.keeps_program_slots
    caller.checked.native.machine.heap heap before.core marked preparationPost.effects.keeps slots
  have currentSlots := render_stable_slots heap before.core entered.core valid marked stable nativeSlots
  have markedFields (tagged : marked uv) := prepared_marked_fields preparationFuel preparationFuel uv handle scs
    caller before entered decoded value heap valid marked slots stored _decodedLookup (preparationRun 0) tagged
  by_cases empty : value = .empty
  · subst value
    let folded : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
        (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
      .complete [.rejected preparedCaller memos.query entered] [] preparedCaller memos.query
    have growth := SourcePruningEnumerationSharedPreparedReservation.stage_ge recursiveFuel start
      ceiling ceiling (SourcePruningEnumerationSharedPreparedReservation.rows seed)
    refine ⟨preparationFuel,
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done .empty heap)), folded, ?_, ?_, ?_⟩
    · intro extra
      unfold SourcePruningEnumerationSharedPreparedContinuations.run
      rw [preparationRun extra]
      cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;>
        simp only [terminal, Bool.false_eq_true, ↓reduceIte, frame,
          SourcePruningEnumerationSharedSelectedOpaqueDispatch.empty,
          SourcePruningEnumerationSharedReceiptContinuation.run,
          SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance, folded, preparedCaller]
    · refine ⟨preparedCaller, inventory, memos, preparationPost, ?_, ?_, rfl, rfl, ?_⟩
      · simpa only [SourcePruningEnumerationSharedPreparedReservation.final_succ] using currentFits.mono growth.1
      · intro key edge found
        exact growth.2 (currentKnown key edge found)
      · intro output member
        cases member
    · intro output member
      cases member
  by_cases ordinary : ∃ entry rows depth free,
      value = .node entry rows depth free ∧ scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false
  · obtain ⟨entry, rows, depth, free, same, nonterminal⟩ := ordinary
    subst value
    have rowWidth := SourceCurrentConstrainedCapRequiredResources.node_width
      (SourceCurrentConstrainedCapRequiredResources.of_checked currentFits) available
    have countBound : (edgesOf (.node entry rows depth free)).length ≤
        SourcePruningEnumerationSharedPreparedReservation.rows seed :=
      Nat.le_trans (selectionLength entry rows depth free) (Nat.le_trans rowWidth (Nat.le_succ _))
    have rowFields : marked uv → ∀ edge ∈ edgesOf (.node entry rows depth free),
        SourceSynthesisHereditaryProgramFields.EdgeFields valid literal edge := by
      intro tagged edge member
      have actualFields := (markedFields tagged).1
      cases actualFields with
      | node _ _ _ _ checked => exact checked edge (selectionMembers entry rows depth free edge member)
    obtain ⟨branchFuel, folded, branchRun, certificate, outputRoles⟩ := scan_finite_program
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel start
      formulas solver recursive inventory preparedCaller memos entered uv handle scs entry rows
      (edgesOf (.node entry rows depth free)) depth free enteredPacket enteredReady enteredStored available closed
      (selectionMembers entry rows depth free) enteredIncoming currentFits currentKnown
      selectionMembers selectionLength ceiling ceiling currentMass inheritedLength
      (reserved.ordinary _ countBound) valid marked currentSlots rowFields
    have growth := SourcePruningEnumerationSharedPreparedReservation.stage_le_final
      recursiveFuel seed ceiling (edgesOf (.node entry rows depth free)).length countBound
    refine ⟨preparationFuel + branchFuel,
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done (.node entry rows depth free) heap)),
      folded, ?_, (certificate.mono growth.1 growth.2).post preparationPost, outputRoles⟩
    intro extra
    have atPreparation := preparationRun (branchFuel + extra)
    have prepCommon : preparationFuel + (branchFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [prepCommon] at atPreparation
    have atBranch := branchRun (preparationFuel + extra)
    have branchCommon : branchFuel + (preparationFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [branchCommon] at atBranch
    have actual := SourcePruningEnumerationSharedPreparedContinuations.ordinary
      (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        (preparationFuel + branchFuel + extra) recursiveFuel) graph templates stop order
        (preparationFuel + branchFuel + extra) metadata uv)
      checkEmpty (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) uv uv handle scs decoded entry rows depth free heap entered.core
        edgesOf caller before memos.query atPreparation nonterminal
    rw [frame, atBranch] at actual
    exact actual
  · have dispatch : (match (generalizing := false) value with
        | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
        | _ => false) = false := by
      cases value with
      | node entry rows depth free =>
          cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
          | false => exact (ordinary ⟨entry, rows, depth, free, rfl, terminal⟩).elim
          | true => rfl
      | empty | reference _ | mu _ _ _ _ | union _ _ _ _ => rfl
    have unmarked : ¬marked uv := by
      intro tagged
      have currentFields := markedFields tagged
      have fields := currentFields.1
      cases fields with
      | empty => exact empty rfl
      | node entry rows depth free checked =>
          exact ordinary ⟨entry, rows, depth, free, rfl, annotation_nonterminal scs currentFields.2.2⟩
    obtain ⟨branchFuel, folded, composed, certificate, outputRoles⟩ := opaque_finite_program
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel start
      formulas solver recursive inventory preparedCaller memos entered uv handle scs value enteredPacket
      enteredReady enteredStored enteredIncoming available closed dispatch currentFits currentKnown
      selectionMembers selectionLength ceiling ceiling currentMass inheritedLength reserved.first
      valid marked currentSlots unmarked
    have growth := SourcePruningEnumerationSharedPreparedReservation.first_le_final recursiveFuel seed ceiling
    refine ⟨preparationFuel + branchFuel,
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)), folded,
      ?_, (certificate.mono growth.1 growth.2).post preparationPost, outputRoles⟩
    intro extra
    have atPreparation := preparationRun (branchFuel + extra)
    have prepCommon : preparationFuel + (branchFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [prepCommon] at atPreparation
    have atBranch := composed (preparationFuel + extra)
    have branchCommon : branchFuel + (preparationFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [branchCommon] at atBranch
    have actual : SourcePruningEnumerationSharedPreparedContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (preparationFuel + branchFuel + extra) recursiveFuel) graph templates stop order
          (preparationFuel + branchFuel + extra) metadata uv)
        checkEmpty (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) uv edgesOf caller before memos.query =
        (([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)),
          some (SourcePruningEnumerationSharedReceiptContinuation.run
            (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
              (preparationFuel + branchFuel + extra) recursiveFuel) graph templates stop order
              (preparationFuel + branchFuel + extra) metadata uv) preparedCaller memos.query
            (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
              (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
              (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
              (preparationFuel + branchFuel + extra) uv scs value preparedCaller entered memos.query))) := by
      unfold SourcePruningEnumerationSharedPreparedContinuations.run
      rw [atPreparation]
      cases value with
      | node entry rows depth free =>
          have terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
            cases here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
            | false => exact (ordinary ⟨entry, rows, depth, free, rfl, here⟩).elim
            | true => rfl
          simp only [terminal, ↓reduceIte, frame, preparedCaller]
      | empty | reference _ | mu _ _ _ _ | union _ _ _ _ =>
          cases here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;>
            simp only [here, Bool.false_eq_true, ↓reduceIte, frame, preparedCaller]
    rw [atBranch] at actual
    exact actual


private theorem expansion_program_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat)
    (recursive : programResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (uv : Nat) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits (recursiveFuel + 1) seed ceiling)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked) :
    ∃ bound outcome,
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) (recursiveFuel + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final (recursiveFuel + 1) seed ceiling) outcome ∧ programOutputs valid marked outcome := by
  have beforeReady := (SourcePruningEnumerationRestart.selected stop order metadata caller before uv
    packet.valid packet.safe chosen).1
  let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
  have finalGrowth := SourcePruningEnumerationSharedPreparedReservation.final_ge (recursiveFuel + 1) seed ceiling
  have narrowGrowth := SourcePruningEnumerationSharedPreparedReservation.preparedSeed_ge seed
  have stageGrowth := SourcePruningEnumerationSharedPreparedReservation.stage_ge
    recursiveFuel start ceiling ceiling (SourcePruningEnumerationSharedPreparedReservation.rows seed)
  obtain ⟨currentFuel, phases⟩ := SourcePruningEnumerationSharedRecursive.checkpoint_resources holeKey fits admits graph templates checkEmpty edgesOf
    stop order metadata formulas solver inventory caller memos before packet seed.2
    (fun guard => guard ∈ seed.1) bounded known uv chosen
  obtain ⟨legacyFuel, legacyComplete⟩ := SourcePruningEnumerationRecursive.packet_prefix_complete
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before packet
  let prefixFuel := currentFuel + legacyFuel
  have shift (extra : Nat) : currentFuel + (legacyFuel + extra) = prefixFuel + extra := by
    dsimp only [prefixFuel]
    omega
  have legacy (extra : Nat) : SourcePruningEnumerationSelectedStep.PrefixValid
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + extra) uv caller before memos
      (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before memos.query) := by
    have valid := legacyComplete (currentFuel + extra) uv chosen
    have common : legacyFuel + (currentFuel + extra) = prefixFuel + extra := by
      dsimp only [prefixFuel]
      omega
    simpa only [common] using valid
  rcases phases with ⟨checked, originalPhase⟩ | ⟨checked, heap, originalPhase⟩ |
    ⟨checked, phaseValue, heap, after, _nonempty, originalPhase⟩
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    have facts := (phase 0).2.1
    rw [(phase 0).1] at facts
    obtain ⟨cached, sameCache, _core, _raw, checkedPacket⟩ := facts
    have same : checked = cached := Option.some.inj sameCache
    subst cached
    have prefixReceipt := legacy 0
    rw [(phase 0).1] at prefixReceipt
    have checkedSlots : ProgramSlots valid literal caller.checked.native.machine.heap checked.core marked :=
      observed_prefix_slots holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (prefixFuel + 0) uv caller memos before packet beforeReady valid marked slots
        _ prefixReceipt (phase 0).1
    have checkedMass := SourcePruningEnumerationPrefixMass.retained_le
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller memos before packet _ prefixReceipt (phase 0).1
    have framed : EnumerationExpandableIndex.frame checked.core checked = checked := by
      cases checked
      rfl
    by_cases blocked : SourcePruningEnumerationRestart.decision stop order metadata checked = some .stuck
    · have certificate : OutcomeResources (Typing := Typing) formulas solver caller seed
          (.complete [] caller memos.query) := by
        refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
        intro output member
        exact (List.not_mem_nil member).elim
      refine ⟨prefixFuel, .complete [] caller memos.query, ?_, certificate.mono finalGrowth.1 finalGrowth.2, ?_⟩
      · intro extra
        have observed := (phase extra).1
        rw [SourcePruningEnumerationRestart.run_exact, ite_eq_left blocked] at observed
        rw [resume, observed]
      · intro output member
        cases member
    · let parkedSeed := SourcePruningEnumerationSharedPreparedReservation.afterHead start ceiling
      let parkedMass := SourcePruningEnumerationRecursiveReservation.massCeil start ceiling ceiling
      have headGrowth := SourcePruningEnumerationSharedPreparedReservation.afterHead_ge start ceiling
      have parkedFits : Fits parkedSeed.2 caller.checked := bounded.mono (narrowGrowth.1.trans headGrowth.1)
      have parkedKnown : Heap (fun guard => guard ∈ parkedSeed.1) caller.checked.native.machine.heap :=
        fun key edge found => headGrowth.2 (narrowGrowth.2 (known key edge found))
      have massBound : SourcePruningEnumerationPrefixAdmission.suspendedBound checked.core ≤ parkedMass :=
        Nat.le_trans (Nat.le_trans checkedMass initialMass) (Nat.le_add_right _ _)
      obtain ⟨resumeFuel, outcome, running, resources, outputRoles⟩ := recursive
        inventory caller memos checked metadata parkedSeed parkedMass checkedPacket parkedFits parkedKnown
        selectionMembers selectionLength massBound reserved.first.2 valid marked checkedSlots
      have growth := SourcePruningEnumerationSharedPreparedReservation.first_le_final recursiveFuel seed ceiling
      have callbackResources : OutcomeResources formulas solver caller
          (SourcePruningEnumerationSharedPreparedReservation.step recursiveFuel start ceiling ceiling) outcome := by
        simpa only [SourcePruningEnumerationSharedPreparedReservation.step, parkedSeed, parkedMass] using resources
      refine ⟨prefixFuel + resumeFuel, outcome, ?_, callbackResources.mono growth.1 growth.2, outputRoles⟩
      intro extra
      have observed := (phase (resumeFuel + extra)).1
      have common : prefixFuel + (resumeFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [common, SourcePruningEnumerationRestart.run_exact, ite_eq_right blocked] at observed
      have actual := running (prefixFuel + extra)
      have recursiveCommon : resumeFuel + (prefixFuel + extra) = prefixFuel + resumeFuel + extra := by omega
      rw [recursiveCommon] at actual
      rw [resume, observed]
      dsimp only
      rw [framed]
      exact actual
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    have current := (phase 0).2
    rw [(phase 0).1] at current
    obtain ⟨_ordinary, _queries, _value, _heap, _action, final,
      _prepared, _reached, post, query, _shape⟩ := current.1
    have normalizationGrowth := SourcePruningEnumerationPreparedReservation.normalizationProfile_ge
      (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
    have certificate : OutcomeResources (Typing := Typing) formulas solver caller start
        (.complete [] reached memos.query) := by
      refine ⟨reached, inventory, final, post, current.2.1.mono normalizationGrowth,
        current.2.2, rfl, query.symm, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    refine ⟨prefixFuel, .complete [] reached memos.query, ?_, ?_, ?_⟩
    · intro extra
      rw [resume, (phase extra).1]
    · have padded := certificate.mono stageGrowth.1 stageGrowth.2
      simpa only [SourcePruningEnumerationSharedPreparedReservation.final_succ] using padded
    · intro output member
      cases member
  · have phase (extra : Nat) := originalPhase (legacyFuel + extra)
    simp only [shift] at phase
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    obtain ⟨_action, prefixAt, current⟩ := phase 0
    rw [prefixAt] at current
    obtain ⟨_metadataSame, middleMemos, middlePost, middleQuery, middlePacket⟩ :=
      SourcePruningEnumerationSharedRecursive.CurrentPrefixFacts.right_packet current.1
    have prefixReceipt := legacy 0
    rw [prefixAt] at prefixReceipt
    have afterSlots : ProgramSlots valid literal reached.checked.native.machine.heap after.core marked :=
      observed_prefix_slots holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (prefixFuel + 0) uv caller memos before packet beforeReady valid marked slots
        _ prefixReceipt prefixAt
    have admission := SourcePruningEnumerationPrefixAdmission.narrowed_admission
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller memos before packet chosen seed.2 (fun guard => guard ∈ seed.1)
      bounded known _ prefixReceipt
    obtain ⟨handle, scs, _value, _oldMemos, _oldPost, _oldQuery, _oldPacket, ready, stored,
      _decoded, _available, _closed, incoming, _pending, _ids, lengths, _counter, _waiting,
      _oldFits, _oldKnown⟩ := admission
    have middleFits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2
        reached.checked := current.2.1
    have middleKnown : Heap (fun guard => guard ∈ start.1) reached.checked.native.machine.heap := current.2.2
    have currentMass : SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling := Nat.le_trans
      (SourcePruningEnumerationPrefixMass.retained_le holeKey fits admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory (prefixFuel + 0) uv caller memos before packet _ prefixReceipt prefixAt)
      initialMass
    have inheritedLength : scs.length ≤ ceiling := Nat.le_trans lengths initialMass
    obtain ⟨scanFuel, _observation, result, scanRun, certificate, outputRoles⟩ := prepared_dispatch_program
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel seed
      formulas solver recursive inventory reached middleMemos after uv handle scs
      middlePacket ready stored incoming middleFits middleKnown selectionMembers selectionLength
      ceiling currentMass inheritedLength reserved valid marked afterSlots
    refine ⟨prefixFuel + scanFuel, finish uv result, ?_, certificate.post middlePost, outputRoles⟩
    intro extra
    obtain ⟨currentAction, currentPrefix, _current⟩ := phase (scanFuel + extra)
    have common : prefixFuel + (scanFuel + extra) = prefixFuel + scanFuel + extra := by omega
    rw [common] at currentPrefix
    have actual := scanRun (prefixFuel + extra)
    have scanCommon : scanFuel + (prefixFuel + extra) = prefixFuel + scanFuel + extra := by omega
    rw [scanCommon, middleQuery] at actual
    rw [resume, currentPrefix]
    dsimp only
    rw [actual]


private theorem finite_program_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveFuel : Nat) :
    programResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel := by
  induction recursiveFuel with
  | zero => exact zero_program_complete holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
  | succ recursiveFuel ih =>
      intro inventory caller memos before metadata seed ceiling packet bounded known
        selectionMembers selectionLength initialMass reserved valid marked slots
      by_cases expanding : ∃ uv,
          SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)
      · obtain ⟨uv, selected⟩ := expanding
        obtain ⟨bound, outcome, running, resources, outputRoles⟩ := expansion_program_complete
          holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel ih
          inventory caller memos before metadata uv seed ceiling packet bounded known
          selectionMembers selectionLength initialMass reserved selected valid marked slots
        refine ⟨bound, outcome, ?_, resources, outputRoles⟩
        intro extra
        simpa only [selected] using running extra
      · obtain ⟨bound, outcome, running, resources, outputRoles⟩ := zero_program_complete
          holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          inventory caller memos before metadata seed ceiling packet bounded known selectionMembers selectionLength
          initialMass trivial valid marked slots
        have growth := SourcePruningEnumerationSharedPreparedReservation.final_ge (recursiveFuel + 1) seed ceiling
        refine ⟨bound, outcome, ?_, resources.mono growth.1 growth.2, outputRoles⟩
        intro extra
        cases decision : SourcePruningEnumerationRestart.decision stop order metadata before with
        | none => simpa only [decision, resume] using running extra
        | some next =>
            cases next with
            | done => simpa only [decision, resume] using running extra
            | stuck => simpa only [decision, resume] using running extra
            | expand uv => exact (expanding ⟨uv, decision⟩).elim

/-- The same finite worker retains Program roles at every complete or stopped output. -/
theorem run_finite_complete_resources_program_slots
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
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits recursiveFuel seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
      caller.checked.native.machine.heap before.core marked) (root : marked 0) :
    ∃ bound outcome,
      (
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final recursiveFuel seed ceiling) outcome ) ∧
      ∀ output ∈ emitted outcome, ∃ finalMarked : Nat → Prop,
        (∀ uv, marked uv → finalMarked uv) ∧ finalMarked 0 ∧
        SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
          output.caller.checked.native.machine.heap output.cache.core finalMarked := by
  obtain ⟨bound, outcome, running, resources, roles⟩ := finite_program_complete
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
    inventory caller memos before metadata seed ceiling packet bounded known
    selectionMembers selectionLength initialMass reserved valid marked slots
  refine ⟨bound, outcome, ⟨running, resources⟩, ?_⟩
  intro output member
  obtain ⟨finalMarked, extending, outputSlots⟩ := roles output member
  exact ⟨finalMarked, extending, extending 0 root, outputSlots⟩

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
