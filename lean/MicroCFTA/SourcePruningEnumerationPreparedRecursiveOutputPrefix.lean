import MicroCFTA.SourcePruningEnumerationPreparedRecursiveDepth
import MicroCFTA.SourcePruningEnumerationSelectedContinuationOutputPrefix

/-!
# Prepared outputs at larger recursive depth

Keep the work fuel and every original input fixed.
Each earlier output list is a prefix of the later output list.
This statement covers complete and stopped results. It does not assert output existence.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Output" => SourcePruningEnumerationRecursive.Output
variable {Typing Key : Type} {width : Nat}
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- Preserve callback output prefixes under the same actual record-types observation. -/
theorem continueWith_outputs_prefix
    (first second : Metadata Typing → Caller width → Queries → Cached → Option Next → Result)
    (prefixHooks : ∀ metadata caller queries before next,
      List.IsPrefix (SourcePruningEnumerationHookInvocation.hookOutputs
        (first metadata caller queries before next))
        (SourcePruningEnumerationHookInvocation.hookOutputs
          (second metadata caller queries before next)))
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (callbackFuel : Nat) (metadata : Metadata Typing) (uv : Nat)
    (fragment : Fragment) (caller : Caller width) (queries : Queries) (before : Cached) :
    List.IsPrefix (SourcePruningEnumerationHookInvocation.hookOutputs
      (continueWith first graph templates stop order callbackFuel metadata uv
        fragment caller queries before))
      (SourcePruningEnumerationHookInvocation.hookOutputs
        (continueWith second graph templates stop order callbackFuel metadata uv
          fragment caller queries before)) := by
  unfold continueWith
  generalize callback : ExceptT.run (SourcePruningRecordTypes.recordTypes
    graph templates callbackFuel metadata uv (.inl fragment) before.core) = raw
  cases raw with
  | nil => exact List.prefix_rfl
  | cons firstRow rest =>
      cases rest with
      | cons secondRow tail =>
          cases firstRow with
          | error error => exact List.prefix_rfl
          | ok pair =>
              obtain ⟨⟨pruned, updated⟩, core⟩ := pair
              cases pruned <;> exact List.prefix_rfl
      | nil =>
          cases firstRow with
          | error error => exact List.prefix_rfl
          | ok pair =>
              obtain ⟨⟨pruned, updated⟩, core⟩ := pair
              cases pruned with
              | true => exact List.prefix_rfl
              | false =>
                  exact prefixHooks updated caller queries (EnumerationExpandableIndex.frame core before)
                    (SourcePruningEnumerationRestart.decision stop order updated
                      (EnumerationExpandableIndex.frame core before))

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Preserve every actual prepared resume output when only recursive depth increases. -/
theorem resume_outputs_moreDepth
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel larger : Nat) (increase : recursiveFuel ≤ larger) :
    ∀ (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached)
      (next : Option Next),
      List.IsPrefix (SourcePruningEnumerationHookInvocation.hookOutputs
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
          metadata caller queries before next))
        (SourcePruningEnumerationHookInvocation.hookOutputs
          (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel larger
            metadata caller queries before next)) := by
  induction recursiveFuel generalizing larger with
  | zero =>
      intro metadata caller queries before next
      cases next with
      | none => cases larger <;> exact List.prefix_rfl
      | some next =>
          cases next with
          | done | stuck => cases larger <;> exact List.prefix_rfl
          | expand uv => exact List.nil_prefix
  | succ fuel ih =>
      cases larger with
      | zero => omega
      | succ larger =>
          have enough : fuel ≤ larger := Nat.le_of_succ_le_succ increase
          intro metadata caller queries before next
          cases next with
          | none => exact List.prefix_rfl
          | some next =>
              cases next with
              | done | stuck => exact List.prefix_rfl
              | expand uv =>
                  unfold resume
                  generalize observedPrefix : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits
                    graph templates stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel
                    uv caller before queries = observed
                  cases observed with
                  | stopped read checked => exact List.prefix_rfl
                  | parked checked candidate raw =>
                      cases candidate with
                      | none => exact List.prefix_rfl
                      | some parked =>
                          cases raw with
                          | none => exact List.prefix_rfl
                          | some rows =>
                              cases rows with
                              | nil => exact List.prefix_rfl
                              | cons firstRow rest =>
                                  cases rest with
                                  | cons secondRow tail => cases firstRow <;> exact List.prefix_rfl
                                  | nil =>
                                      cases firstRow with
                                      | error error => exact List.prefix_rfl
                                      | ok pair =>
                                          obtain ⟨⟨updated, following⟩, core⟩ := pair
                                          exact ih larger enough updated caller queries
                                            (EnumerationExpandableIndex.frame core parked) following
                  | narrowed checked prepared reached saved action candidate right ordinary =>
                      rcases action with _ | (_ | ⟨actionHead, actionTail⟩) <;>
                        first
                        | exact List.prefix_rfl
                        |
                            cases right with
                            | none => exact List.prefix_rfl
                            | some rows =>
                                cases rows with
                                | nil => exact List.prefix_rfl
                                | cons firstRow rest =>
                                    cases rest with
                                    | cons secondRow tail =>
                                        cases firstRow with
                                        | error error => exact List.prefix_rfl
                                        | ok pair =>
                                            obtain ⟨⟨pruned, updated⟩, core⟩ := pair
                                            cases pruned <;> exact List.prefix_rfl
                                    | nil =>
                                        cases firstRow with
                                        | error error => exact List.prefix_rfl
                                        | ok pair =>
                                            obtain ⟨⟨pruned, updated⟩, core⟩ := pair
                                            cases pruned with
                                            | true => exact List.prefix_rfl
                                            | false =>
                                                cases candidate with
                                                | none => exact List.prefix_rfl
                                                | some after =>
                                                    cases ordinary with
                                                    | some current => exact List.prefix_rfl
                                                    | none =>
                                                        let first := continueWith (width := width)
                                                          (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
                                                          graph templates stop order workFuel updated uv
                                                        let second := continueWith (width := width)
                                                          (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel larger)
                                                          graph templates stop order workFuel updated uv
                                                        have same : ∀ fragment headCaller headQueries headCache headOutputs middleCaller middleQueries,
                                                            first fragment headCaller headQueries headCache = .complete headOutputs middleCaller middleQueries →
                                                            second fragment headCaller headQueries headCache = .complete headOutputs middleCaller middleQueries := by
                                                          intro fragment headCaller headQueries headCache headOutputs middleCaller middleQueries completed
                                                          exact continueWith_complete_congr
                                                            (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
                                                            (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel larger)
                                                            (resume_complete_moreDepth holeKey fits admits graph templates checkEmpty edgesOf stop order
                                                              workFuel fuel larger enough)
                                                            graph templates stop order workFuel updated uv
                                                            fragment headCaller headQueries headCache headOutputs middleCaller middleQueries completed
                                                        have prefixHooks : ∀ fragment headCaller headQueries headCache,
                                                            List.IsPrefix (SourcePruningEnumerationHookInvocation.hookOutputs
                                                              (first fragment headCaller headQueries headCache))
                                                              (SourcePruningEnumerationHookInvocation.hookOutputs
                                                                (second fragment headCaller headQueries headCache)) := by
                                                          intro fragment headCaller headQueries headCache
                                                          exact continueWith_outputs_prefix
                                                            (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
                                                            (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel larger)
                                                            (ih larger enough) graph templates stop order workFuel updated uv
                                                            fragment headCaller headQueries headCache
                                                        have retained := SourcePruningEnumerationSelectedContinuations.run_outputs_prefix
                                                          first second checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv
                                                          edgesOf reached after saved same prefixHooks
                                                        dsimp only [first, second] at retained
                                                        cases oldRun : (SourcePruningEnumerationSelectedContinuations.run first checkEmpty
                                                            workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf reached after saved).2 with
                                                        | none =>
                                                            dsimp only [first] at oldRun
                                                            simp only [oldRun, SourcePruningEnumerationHookInvocation.hookOutputs]
                                                            exact List.nil_prefix
                                                        | some oldFold =>
                                                            cases newRun : (SourcePruningEnumerationSelectedContinuations.run second checkEmpty
                                                                workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf reached after saved).2 with
                                                            | none =>
                                                                dsimp only [first] at oldRun
                                                                dsimp only [second] at newRun
                                                                cases oldFold <;>
                                                                  simpa only [oldRun, newRun, Option.map, Option.getD, finish,
                                                                    SourcePruningEnumerationHookInvocation.hookOutputs,
                                                                    SourcePruningEnumerationHookInvocation.foldOutputs] using retained
                                                            | some newFold =>
                                                                dsimp only [first] at oldRun
                                                                dsimp only [second] at newRun
                                                                cases oldFold <;> cases newFold <;>
                                                                  simpa only [oldRun, newRun, Option.map, Option.getD, finish,
                                                                    SourcePruningEnumerationHookInvocation.hookOutputs,
                                                                    SourcePruningEnumerationHookInvocation.foldOutputs] using retained

/-- Preserve every actual prepared driver output when only recursive depth increases. -/
theorem run_outputs_moreDepth
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel larger : Nat) (increase : recursiveFuel ≤ larger)
    (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached) :
    List.IsPrefix (SourcePruningEnumerationHookInvocation.hookOutputs
      (run holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
        metadata caller queries before))
      (SourcePruningEnumerationHookInvocation.hookOutputs
        (run holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel larger
          metadata caller queries before)) :=
  resume_outputs_moreDepth holeKey fits admits graph templates checkEmpty edgesOf stop order
    workFuel recursiveFuel larger increase metadata caller queries before
    (SourcePruningEnumerationRestart.decision stop order metadata before)

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
