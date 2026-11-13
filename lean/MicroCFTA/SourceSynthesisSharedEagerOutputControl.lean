import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot

/-!
# Control at actual eager prepared outputs

Only actual recursive done branches emit outputs without metadata.
The proof observes eager child, tuple and outer recursion at every fuel.
It does not assert an output, adequate depth or a satisfying assignment.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure finish continueWith emitted)
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

local notation "Branch" => Fold (Output width Typing) (Failure width Typing) width
local notation "Observation" => SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.Observation
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Branch) →
  (Observation width → Option Cached → Branch) → Branch

private def Controlled (stop : Option (Metadata Typing → Nat → Bool)) (output : Output width Typing) : Prop :=
  (output.metadata = none → EnumerationPureSelection.next (fun _ => none) output.cache = .done) ∧
    (stop = none → output.metadata = none)
private def controlFoldEmitted : Fold (Output width Typing) (Failure width Typing) width → List (Output width Typing)
  | .complete _ outputs _ _ | .stopped _ outputs _ => outputs
private def FoldControlled (stop : Option (Metadata Typing → Nat → Bool)) (folded : Branch) : Prop :=
  ∀ output ∈ controlFoldEmitted folded, Controlled stop output

private def ChildControlled (stop : Option (Metadata Typing → Nat → Bool)) (visit : Visitor) : Prop :=
  ∀ scs incoming caller before queries done stopped,
    (∀ fragment reached saved after, FoldControlled stop (done fragment reached saved after)) →
    (∀ observation candidate, FoldControlled stop (stopped observation candidate)) →
    FoldControlled stop (visit scs incoming caller before queries done stopped)

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

private theorem control_tuple
    (stop : Option (Metadata Typing → Nat → Bool)) (visit : Visitor) (controlled : ChildControlled stop visit)
    (inputs : List (Node × List Suspended)) :
    ∀ caller before queries
      (done : List Fragment → Caller width → Queries → Cached → Branch)
      (stopped : List Fragment → Observation width → Option Cached → Branch),
      (∀ fragments reached saved after, FoldControlled stop (done fragments reached saved after)) →
      (∀ fragments observation candidate, FoldControlled stop (stopped fragments observation candidate)) →
      FoldControlled stop (SourcePruningEnumerationSharedChildVisitors.visitChildren visit done stopped inputs caller before queries) := by
  induction inputs with
  | nil => intro caller before queries done stopped yes no; exact yes [] caller queries before
  | cons input rest ih =>
    rcases input with ⟨value, bucket⟩
    intro caller before queries done stopped yes no
    rw [SourcePruningEnumerationSharedChildVisitors.visitChildren]
    apply controlled
    · intro fragment reached saved after
      exact ih reached after saved _ _
        (fun fragments actual current cache => yes (fragment :: fragments) actual current cache)
        (fun completed observation candidate => no (fragment :: completed) observation candidate)
    · intro observation candidate
      exact no [] observation candidate

private theorem control_selected
    (stop : Option (Metadata Typing → Nat → Bool)) (visit : Visitor) (controlled : ChildControlled stop visit)
    (consume : Receipt width → Branch) (consumed : ∀ receipt, FoldControlled stop (consume receipt))
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries) :
    FoldControlled stop (SourcePruningEnumerationSharedChildVisitors.visitSelected visit consume scs edge caller before queries) := by
  unfold SourcePruningEnumerationSharedChildVisitors.visitSelected
  split
  · exact consumed _
  · exact consumed _
  · exact control_tuple stop visit controlled _ _ _ _ _ _
      (fun fragments reached saved after => consumed _) (fun completed observation candidate => consumed _)
  · exact consumed _

private theorem control_consume
    (stop : Option (Metadata Typing → Nat → Bool))
    (done : Fragment → Caller width → Queries → Cached → Branch)
    (yes : ∀ fragment reached saved after, FoldControlled stop (done fragment reached saved after))
    (caller : Caller width) (queries : Queries) (receipt : Receipt width) :
    FoldControlled stop (SourcePruningEnumerationSharedEagerChildren.consumeSelected done caller queries receipt) := by
  cases receipt with
  | unhandled | rejected _ _ _ | finalizeStopped _ _ _ _ => intro output member; cases member
  | complete fragment reached saved after =>
    cases called : done fragment reached saved after <;> intro output member
    all_goals exact yes fragment reached saved after output (by
      simpa only [SourcePruningEnumerationSharedEagerChildren.consumeSelected, called, controlFoldEmitted] using member)
  | stopped fragments observation candidate =>
    cases advanced : advance (.stopped fragments observation candidate) with
    | none => intro output member
              simp only [SourcePruningEnumerationSharedEagerChildren.consumeSelected, advanced, controlFoldEmitted, List.not_mem_nil] at member
    | some endpoint =>
      obtain ⟨reached, saved⟩ := endpoint
      intro output member
      simp only [SourcePruningEnumerationSharedEagerChildren.consumeSelected, advanced, controlFoldEmitted, List.not_mem_nil] at member

private theorem control_captured
    (stop : Option (Metadata Typing → Nat → Bool)) (visit : Visitor) (controlled : ChildControlled stop visit)
    (hook : Fragment → Caller width → Queries → Cached → Result)
    (hookControlled : ∀ fragment caller queries before output, output ∈ emitted (hook fragment caller queries before) →
      Controlled stop output)
    (k target : Nat) (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (queries : Queries) (before : Cached) :
    FoldControlled stop (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith visit hook k target scs edge caller queries before) := by
  rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
  apply control_selected stop visit controlled
  intro receipt
  cases receipt with
  | complete fragment reached saved after =>
    dsimp only
    cases finalized : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after with
    | none =>
      dsimp only
      exact control_receipt stop hook hookControlled caller queries
        (some (.finalizeStopped fragment reached saved after))
    | some finished =>
      dsimp only
      exact control_receipt stop hook hookControlled caller queries
        (some (.complete fragment reached saved finished))
  | unhandled | rejected _ _ _ | finalizeStopped _ _ _ _ | stopped _ _ _ =>
    exact control_receipt stop hook hookControlled caller queries _

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

private theorem control_shallow
    (stop : Option (Metadata Typing → Nat → Bool)) (checkEmpty : Bool) (r n p h k : Nat) :
    ChildControlled (width := width) stop (SourcePruningEnumerationSharedChildVisitors.shallowVisit checkEmpty r n p h k) := by
  intro scs incoming caller before queries done stopped yes no
  cases dispatched : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k scs incoming caller before queries with
  | mk observation candidate =>
    have rejected := no observation candidate
    rcases observation with ⟨outcome, reached, saved, _outer, _waiting⟩
    cases outcome with
    | error _fault =>
      simpa only [SourcePruningEnumerationSharedChildVisitors.shallowVisit, dispatched] using rejected
    | ok returned =>
      cases returned with
      | none =>
        simpa only [SourcePruningEnumerationSharedChildVisitors.shallowVisit, dispatched] using rejected
      | some raw =>
        cases raw with
        | nil =>
          simpa only [SourcePruningEnumerationSharedChildVisitors.shallowVisit, dispatched] using rejected
        | cons row rows =>
          cases row with
          | error _fault =>
            simpa only [SourcePruningEnumerationSharedChildVisitors.shallowVisit, dispatched] using rejected
          | ok child =>
            rcases child with ⟨fragment, _returnedCore⟩
            cases rows with
            | cons _row _rows =>
              simpa only [SourcePruningEnumerationSharedChildVisitors.shallowVisit, dispatched] using rejected
            | nil =>
              cases candidate with
              | none =>
                simpa only [SourcePruningEnumerationSharedChildVisitors.shallowVisit, dispatched] using rejected
              | some after =>
                simpa only [SourcePruningEnumerationSharedChildVisitors.shallowVisit, dispatched] using
                  yes fragment reached saved after

private theorem control_eager_height
    (stop : Option (Metadata Typing → Nat → Bool)) (checkEmpty : Bool) (r n p h k : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (height : Nat) :
    ∀ (incoming : Node), MergedOrdinaryHeight.height incoming = height →
      ∀ (scs : List Suspended) (caller : Caller width) (before : Cached) (queries : Queries)
        (done : Fragment → Caller width → Queries → Cached → Branch)
        (stopped : Observation width → Option Cached → Branch),
        (∀ fragment reached saved after, FoldControlled stop (done fragment reached saved after)) →
        (∀ observation candidate, FoldControlled stop (stopped observation candidate)) →
        FoldControlled stop (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf
          scs incoming caller before queries done stopped) := by
  induction height using Nat.strongRecOn with
  | ind height ih =>
    intro incoming heightSame scs caller before queries done stopped yes no
    rw [SourcePruningEnumerationSharedEagerChildren.eagerChild]
    split
    · apply control_scan stop
      intro edge reached saved captured output member
      have children : ChildControlled (width := width) stop
          (fun bucket child actual cache current accept reject =>
            if _lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height incoming then
              SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf
                bucket child actual cache current accept reject
            else SourcePruningEnumerationSharedChildVisitors.shallowVisit checkEmpty r n p h k
              bucket child actual cache current accept reject) := by
        intro bucket child actual cache current accept reject accepted rejected
        dsimp only
        split
        · rename_i lower
          exact ih (MergedOrdinaryHeight.height child) (by rw [← heightSame]; exact lower)
            child rfl bucket actual cache current accept reject accepted rejected
        · exact control_shallow stop checkEmpty r n p h k bucket child actual cache current accept reject accepted rejected
      exact control_selected stop _ children _
        (fun receipt => control_consume stop done yes reached saved receipt) scs edge reached captured saved output member
    · exact control_shallow stop checkEmpty r n p h k scs incoming caller before queries done stopped yes no

private theorem control_eager
    (stop : Option (Metadata Typing → Nat → Bool)) (checkEmpty : Bool) (r n p h k : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) :
    ChildControlled (width := width) stop (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf) := by
  intro scs incoming caller before queries done stopped yes no
  exact control_eager_height stop checkEmpty r n p h k edgesOf (MergedOrdinaryHeight.height incoming)
    incoming rfl scs caller before queries done stopped yes no

private theorem control_prepared
    (stop : Option (Metadata Typing → Nat → Bool)) (child : Visitor) (children : ChildControlled stop child)
    (hook : Fragment → Caller width → Queries → Cached → Result)
    (controlled : ∀ fragment caller queries before output, output ∈ emitted (hook fragment caller queries before) →
      Controlled stop output)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries) (before : Cached)
    (folded : Branch)
    (actual : (SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild child hook checkEmpty entryFuel nativeFuel
      r n p h k uv edgesOf caller before queries).2 = some folded) :
    FoldControlled stop folded := by
  unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild at actual
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
          change FoldControlled stop (SourcePruningEnumerationSharedBranching.scan
            (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith child hook k target scs)
            (EnumerationExpandableIndex.frame entered before) (edgesOf (.node entry rows depth free))
            (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries)
          apply control_scan stop
          intro edge actual current cache output member
          exact control_captured stop child children hook controlled k target scs edge actual current cache output member
        | empty | reference _ | mu _ _ _ _ | union _ _ _ _ =>
          all_goals cases actual; exact control_receipt stop hook controlled _ _ _
    · cases actual
  · cases actual

private theorem control_resume
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (child : Visitor) (children : ChildControlled stop child)
    (workFuel depth : Nat) (metadata : Metadata Typing) (caller : Caller width) (queries : Queries)
    (before : Cached) (decision : Option Next)
    (consistent : decision = SourcePruningEnumerationRestart.decision stop order metadata before) :
    ∀ output ∈ emitted (resumeWithChild child holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
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
        dsimp only [resumeWithChild] at member
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
            exact control_prepared stop child children _
              (fun fragment actual current cache output present => control_continue stop order
                (resumeWithChild child holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth) ih
                graph templates workFuel _ uv fragment actual current cache output present)
              checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf
              _ _ _ folded prepared output member
        · cases member
        · cases member

/-- Actual eager outputs retain finishedness and the noStop metadata condition at every fuel. -/
theorem runEager_output_control
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) (caller : Caller width)
    (queries : Queries) (before : Cached) (output : Output width Typing)
    (member : output ∈ emitted (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveFuel metadata caller queries before)) :
    (output.metadata = none → EnumerationPureSelection.next (fun _ => none) output.cache = .done) ∧
      (stop = none → output.metadata = none)
    := by
  exact control_resume holeKey fits admits graph templates checkEmpty edgesOf stop order
    (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
    (control_eager stop checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
    workFuel recursiveFuel metadata caller queries before _ rfl output member

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
