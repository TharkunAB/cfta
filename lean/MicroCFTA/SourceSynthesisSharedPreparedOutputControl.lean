import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot
import MicroCFTA.SourcePruningEnumerationSharedBranching

/-!
# Control at actual shared prepared outputs

Every emitted output without metadata has no remaining selection.
With no stop rule, every emitted output has this property.
The statement includes stopped prefixes and every fuel and depth.
It does not assert that an output exists or that depth is adequate.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Fold" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
local notation "advance" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance
variable {Typing Key : Type} {width : Nat}
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

private def Controlled (stop : Option (Metadata Typing → Nat → Bool)) (output : Output width Typing) : Prop :=
  (output.metadata = none → EnumerationPureSelection.next (fun _ => none) output.cache = .done) ∧
    (stop = none → output.metadata = none)
private def controlFoldEmitted : Fold (Output width Typing) (Failure width Typing) width → List (Output width Typing)
  | .complete _ outputs _ _ | .stopped _ outputs _ => outputs
private theorem control_finish (uv : Nat) (folded : Fold (Output width Typing) (Failure width Typing) width) :
    emitted (finish uv folded) = controlFoldEmitted folded := by cases folded <;> rfl
private theorem pickNext_done (preference : List Nat → Option Nat) (found : Option (List Nat))
    (done : pickNext preference found = .done) : pickNext (fun _ => none) found = .done := by
  cases found with
  | none => rfl
  | some values =>
    cases values with
    | nil => cases done
    | cons first rest =>
      simp only [pickNext] at done
      split at done
      · split at done <;> cases done
      · cases done
private theorem control_decision_done
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (before : Cached)
    (same : some .done = SourcePruningEnumerationRestart.decision stop order metadata before) :
    EnumerationPureSelection.next (fun _ => none) before = .done := by
  have selected : EnumerationPureSelection.next (order metadata) before = .done := by
    cases stop with
    | none => exact Option.some.inj same.symm
    | some rule =>
      simp only [SourcePruningEnumerationRestart.decision] at same
      split at same
      · cases same
      · exact Option.some.inj same.symm
  exact pickNext_done _ _ selected
private theorem control_receipt
    (stop : Option (Metadata Typing → Nat → Bool))
    (hook : Fragment → Caller width → Queries → Cached → Result)
    (controlled : ∀ fragment caller queries before output, output ∈ emitted (hook fragment caller queries before) →
      Controlled stop output)
    (caller : Caller width) (queries : Queries) (receipt : Option (Receipt width)) :
    ∀ output ∈ controlFoldEmitted (SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries receipt),
      Controlled stop output := by
  cases receipt with
  | none => intro output member; cases member
  | some receipt =>
    cases receipt with
    | unhandled | rejected _ _ _ | finalizeStopped _ _ _ _ => intro output member; cases member
    | complete fragment reached saved after =>
      cases callback : hook fragment reached saved after <;> intro output member
      all_goals exact controlled fragment reached saved after output (by
        simpa only [SourcePruningEnumerationSharedReceiptContinuation.run, callback, controlFoldEmitted, emitted] using member)
    | stopped fragments observation candidate =>
      cases advanced : advance (.stopped fragments observation candidate) with
      | none =>
        intro output member
        simp only [SourcePruningEnumerationSharedReceiptContinuation.run, advanced, controlFoldEmitted, List.not_mem_nil] at member
      | some endpoint =>
        obtain ⟨reached, saved⟩ := endpoint
        intro output member
        simp only [SourcePruningEnumerationSharedReceiptContinuation.run, advanced, controlFoldEmitted, List.not_mem_nil] at member
private theorem control_scan
    (stop : Option (Metadata Typing → Nat → Bool))
    (visit : EdgeValue Symbol Constraint → Caller width → Queries → Cached → Fold (Output width Typing) (Failure width Typing) width)
    (controlled : ∀ edge caller queries before output, output ∈ controlFoldEmitted (visit edge caller queries before) →
      Controlled stop output)
    (before : Cached) (edges : List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries) :
    ∀ output ∈ controlFoldEmitted (SourcePruningEnumerationSharedBranching.scan visit before edges caller queries),
      Controlled stop output := by
  induction edges generalizing caller queries with
  | nil => intro output member; cases member
  | cons edge rest ih =>
    cases first : visit edge caller queries before with
    | stopped processed outputs current =>
      intro output member
      exact controlled edge caller queries before output (by
        simpa only [SourcePruningEnumerationSharedBranching.scan, first, controlFoldEmitted] using member)
    | complete processed outputs reached saved =>
      have later := ih reached saved
      cases suffix : SourcePruningEnumerationSharedBranching.scan visit before rest reached saved <;> intro output member
      all_goals
        simp only [SourcePruningEnumerationSharedBranching.scan, first, suffix, controlFoldEmitted] at member
        rcases List.mem_append.mp member with head | tail
        · exact controlled edge caller queries before output (by simpa only [first, controlFoldEmitted] using head)
        · rw [suffix] at later; exact later output tail

private theorem control_continue
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Result)
    (controlled : ∀ metadata caller queries before decision,
      decision = SourcePruningEnumerationRestart.decision stop order metadata before →
      ∀ output ∈ emitted (recur metadata caller queries before decision), Controlled stop output)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (queries : Queries) (before : Cached) :
    ∀ output ∈ emitted (continueWith recur graph templates stop order fuel metadata uv fragment caller queries before),
      Controlled stop output := by
  unfold continueWith
  dsimp only
  split
  · intro output member; cases member
  · exact controlled _ _ _ _ _ rfl
  · intro output member; cases member

variable [DecidableEq (EdgeKey Symbol Constraint)]

private def ControlPrefixDecision (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) : SourcePruningEnumerationSelectedStep.Result width Typing → Prop
  | .parked _ (some parked) (some [.ok ((updated, next), core)]) =>
    next = SourcePruningEnumerationRestart.decision stop order updated (EnumerationExpandableIndex.frame core parked)
  | _ => True

private theorem control_prefix
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller : Caller width) (before : Cached) (queries : Queries) :
    ControlPrefixDecision stop order (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
      stop order metadata readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries) := by
  unfold SourcePruningEnumerationSelectedStep.runPrefix
  dsimp only
  split
  · rename_i oldHandle scs readAfter readEq
    split
    · rename_i checked checkEq
      cases adapted : SourcePruningEnumerationParkedRestart.adapt caller.checked.native.machine.heap
          indexFuel uv oldHandle scs before checked with
      | none => simp only [Option.map_none]; trivial
      | some parked =>
        simp only [Option.map_some]
        unfold SourcePruningEnumerationRestart.run
        split
        · trivial
        · have same := SourcePruningEnumerationParkedRestart.adapt_core caller.checked.native.machine.heap
            indexFuel uv oldHandle scs before parked checked adapted
          rw [← same]
          rfl
    · repeat' first | trivial | split
    · trivial
  · trivial

variable [DecidableEq Symbol] [DecidableEq Node]

private theorem control_prepared
    (stop : Option (Metadata Typing → Nat → Bool))
    (hook : Fragment → Caller width → Queries → Cached → Result)
    (controlled : ∀ fragment caller queries before output, output ∈ emitted (hook fragment caller queries before) →
      Controlled stop output)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries) (before : Cached)
    (folded : Fold (Output width Typing) (Failure width Typing) width)
    (actual : (SourcePruningEnumerationSharedPreparedContinuations.run hook checkEmpty entryFuel nativeFuel
      r n p h k uv edgesOf caller before queries).2 = some folded) :
    ∀ output ∈ controlFoldEmitted folded, Controlled stop output := by
  unfold SourcePruningEnumerationSharedPreparedContinuations.run at actual
  dsimp only at actual
  split at actual
  · rename_i value heap prepared
    split at actual
    · rename_i target handle scs decoded entered reading
      split at actual
      · cases actual
        exact control_receipt stop hook controlled _ _ _
      · cases value with
        | node entry rows depth free =>
          cases actual
          change ∀ output ∈ controlFoldEmitted (SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
            hook checkEmpty r n p h k target scs (EnumerationExpandableIndex.frame entered before)
            (edgesOf (.node entry rows depth free)) (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries),
            Controlled stop output
          rw [SourcePruningEnumerationSharedBranching.run_eq_scan]
          apply control_scan stop
          intro edge actual current cache output member
          have same : controlFoldEmitted (SourcePruningEnumerationSharedBranching.visitCaptured hook checkEmpty r n p h k
              target scs edge actual current cache) = controlFoldEmitted (SourcePruningEnumerationSharedReceiptContinuation.run
                hook actual current (SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k
                  target scs edge actual cache current)) := by
            cases captured : SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k
                target scs edge actual cache current with
            | none => simp only [SourcePruningEnumerationSharedBranching.visitCaptured,
                SourcePruningEnumerationSharedReceiptContinuation.run, captured, controlFoldEmitted]
            | some receipt =>
              cases receipt with
              | complete fragment reached saved after =>
                cases called : hook fragment reached saved after <;>
                  simp only [SourcePruningEnumerationSharedBranching.visitCaptured,
                    SourcePruningEnumerationSharedReceiptContinuation.run, captured, called, controlFoldEmitted]
              | unhandled | rejected _ _ _ | finalizeStopped _ _ _ _ =>
                simp only [SourcePruningEnumerationSharedBranching.visitCaptured,
                  SourcePruningEnumerationSharedReceiptContinuation.run, captured,
                  SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance, controlFoldEmitted]
              | stopped fragments observation candidate =>
                cases advanced : advance (.stopped fragments observation candidate) with
                | none => simp only [SourcePruningEnumerationSharedBranching.visitCaptured,
                    SourcePruningEnumerationSharedReceiptContinuation.run, captured, advanced, controlFoldEmitted]
                | some endpoint =>
                  obtain ⟨reached, saved⟩ := endpoint
                  simp only [SourcePruningEnumerationSharedBranching.visitCaptured,
                    SourcePruningEnumerationSharedReceiptContinuation.run, captured, advanced, controlFoldEmitted]
          rw [same] at member
          exact control_receipt stop hook controlled _ _ _ output member
        | empty | reference _ | mu _ _ _ _ | union _ _ _ _ =>
          all_goals cases actual; exact control_receipt stop hook controlled _ _ _
    · cases actual
  · cases actual

private theorem control_resume
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth : Nat) (metadata : Metadata Typing) (caller : Caller width) (queries : Queries)
    (before : Cached) (decision : Option Next)
    (consistent : decision = SourcePruningEnumerationRestart.decision stop order metadata before) :
    ∀ output ∈ emitted (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
      metadata caller queries before decision), Controlled stop output := by
  induction depth generalizing metadata caller queries before decision with
  | zero =>
    cases decision with
    | none =>
      intro output member; obtain rfl := List.mem_singleton.mp member
      constructor
      · intro impossible; cases impossible
      · intro noStop
        rw [noStop] at consistent
        cases consistent
    | some next =>
      cases next with
      | done =>
        intro output member; obtain rfl := List.mem_singleton.mp member
        exact ⟨fun _ => control_decision_done stop order metadata before consistent, fun _ => rfl⟩
      | stuck | expand _ => intro output member; cases member
  | succ depth ih =>
    cases decision with
    | none =>
      intro output member; obtain rfl := List.mem_singleton.mp member
      constructor
      · intro impossible; cases impossible
      · intro noStop
        rw [noStop] at consistent
        cases consistent
    | some next =>
      cases next with
      | done =>
        intro output member; obtain rfl := List.mem_singleton.mp member
        exact ⟨fun _ => control_decision_done stop order metadata before consistent, fun _ => rfl⟩
      | stuck => intro output member; cases member
      | expand uv =>
        intro output member
        dsimp only [resume] at member
        split at member
        · cases member
        · rename_i checked parked updated next core observed
          have valid := control_prefix holeKey fits admits graph templates stop order metadata workFuel workFuel
            workFuel workFuel workFuel workFuel uv caller before queries
          rw [observed] at valid
          exact ih updated caller queries (EnumerationExpandableIndex.frame core parked) next valid output member
        · cases member
        · cases member
        · rename_i observed
          split at member
          · cases member
          · rename_i folded prepared
            rw [control_finish] at member
            exact control_prepared stop _
              (fun fragment actual current cache output present => control_continue stop order
                (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth) ih
                graph templates workFuel _ uv fragment actual current cache output present)
              checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf
              _ _ _ folded prepared output member
        · cases member
        · cases member

/-- Actual outputs without metadata are finished. Without a stop rule, every output is finished. -/
theorem run_output_control
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) (caller : Caller width)
    (queries : Queries) (before : Cached) (output : Output width Typing)
    (member : output ∈ emitted (run holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveFuel metadata caller queries before)) :
    (output.metadata = none → EnumerationPureSelection.next (fun _ => none) output.cache = .done) ∧
      (stop = none → output.metadata = none)
    := by
  exact control_resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
    metadata caller queries before _ rfl output member

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
