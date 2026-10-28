import MicroCFTA.SourcePruningEnumerationPreparedRecursive
import MicroCFTA.SourcePruningEnumerationSelectedContinuationCompletedCongruence

/-!
# Completed prepared recursion at larger recursive depth

Keep the work fuel and every original input fixed.
A completed actual run retains its exact outputs and native endpoint at a
larger recursive depth. This statement does not assert that a run completes.
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

/-- Retain an actual complete callback continuation under agreement on complete recursive results. -/
theorem continueWith_complete_congr
    (first second : Metadata Typing → Caller width → Queries → Cached → Option Next → Result)
    (same : ∀ metadata caller queries before next outputs reached saved,
      first metadata caller queries before next = .complete outputs reached saved →
      second metadata caller queries before next = .complete outputs reached saved)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (callbackFuel : Nat) (metadata : Metadata Typing) (uv : Nat)
    (fragment : Fragment) (caller : Caller width) (queries : Queries) (before : Cached)
    (outputs : List (Output width Typing)) (reached : Caller width) (saved : Queries)
    (actual : continueWith first graph templates stop order callbackFuel metadata uv
      fragment caller queries before = .complete outputs reached saved) :
    continueWith second graph templates stop order callbackFuel metadata uv
      fragment caller queries before = .complete outputs reached saved := by
  unfold continueWith at actual ⊢
  generalize callback : ExceptT.run (SourcePruningRecordTypes.recordTypes
    graph templates callbackFuel metadata uv (.inl fragment) before.core) = raw at actual ⊢
  cases raw with
  | nil => exact actual
  | cons firstRow rest =>
      cases rest with
      | cons secondRow tail =>
          cases firstRow with
          | error error => exact actual
          | ok pair =>
              obtain ⟨⟨pruned, updated⟩, core⟩ := pair
              cases pruned <;> exact actual
      | nil =>
          cases firstRow with
          | error error => exact actual
          | ok pair =>
              obtain ⟨⟨pruned, updated⟩, core⟩ := pair
              cases pruned with
              | true => exact actual
              | false =>
                  exact same updated caller queries (EnumerationExpandableIndex.frame core before)
                    (SourcePruningEnumerationRestart.decision stop order updated
                      (EnumerationExpandableIndex.frame core before)) outputs reached saved actual

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A complete actual prepared resume stays exact when only recursive depth increases. -/
theorem resume_complete_moreDepth
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel larger : Nat) (increase : recursiveFuel ≤ larger) :
    ∀ (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached)
      (next : Option Next) (outputs : List (Output width Typing))
      (finalCaller : Caller width) (finalQueries : Queries),
      resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
        metadata caller queries before next = .complete outputs finalCaller finalQueries →
      resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel larger
        metadata caller queries before next = .complete outputs finalCaller finalQueries := by
  induction recursiveFuel generalizing larger with
  | zero =>
      intro metadata caller queries before next outputs finalCaller finalQueries actual
      cases next with
      | none => cases larger <;> exact actual
      | some next =>
          cases next with
          | done | stuck => cases larger <;> exact actual
          | expand uv => simp only [resume, reduceCtorEq] at actual
  | succ fuel ih =>
      cases larger with
      | zero => omega
      | succ larger =>
          have enough : fuel ≤ larger := Nat.le_of_succ_le_succ increase
          intro metadata caller queries before next outputs finalCaller finalQueries actual
          cases next with
          | none => exact actual
          | some next =>
              cases next with
              | done | stuck => exact actual
              | expand uv =>
                  unfold resume at actual ⊢
                  generalize observedPrefix : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits
                    graph templates stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel
                    uv caller before queries = observed at actual ⊢
                  cases observed with
                  | stopped read checked => exact actual
                  | parked checked candidate raw =>
                      cases candidate with
                      | none => exact actual
                      | some parked =>
                          cases raw with
                          | none => exact actual
                          | some rows =>
                              cases rows with
                              | nil => exact actual
                              | cons firstRow rest =>
                                  cases rest with
                                  | cons secondRow tail => cases firstRow <;> exact actual
                                  | nil =>
                                      cases firstRow with
                                      | error error => exact actual
                                      | ok pair =>
                                          obtain ⟨⟨updated, following⟩, core⟩ := pair
                                          exact ih larger enough updated caller queries
                                            (EnumerationExpandableIndex.frame core parked) following
                                            outputs finalCaller finalQueries actual
                  | narrowed checked prepared reached saved action candidate right ordinary =>
                      rcases action with _ | (_ | ⟨actionHead, actionTail⟩) <;>
                        first
                        | exact actual
                        |
                            cases right with
                            | none => exact actual
                            | some rows =>
                                cases rows with
                                | nil => exact actual
                                | cons firstRow rest =>
                                    cases rest with
                                    | cons secondRow tail =>
                                        cases firstRow with
                                        | error error => exact actual
                                        | ok pair =>
                                            obtain ⟨⟨pruned, updated⟩, core⟩ := pair
                                            cases pruned <;> exact actual
                                    | nil =>
                                        cases firstRow with
                                        | error error => exact actual
                                        | ok pair =>
                                            obtain ⟨⟨pruned, updated⟩, core⟩ := pair
                                            cases pruned with
                                            | true => exact actual
                                            | false =>
                                                cases candidate with
                                                | none => exact actual
                                                | some after =>
                                                    cases ordinary with
                                                    | some current => exact actual
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
                                                            (ih larger enough) graph templates stop order workFuel updated uv
                                                            fragment headCaller headQueries headCache headOutputs middleCaller middleQueries completed
                                                        cases folded : (SourcePruningEnumerationSelectedContinuations.run first checkEmpty
                                                            workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf reached after saved).2 with
                                                        | none =>
                                                            dsimp only [first] at folded
                                                            simp only [folded, reduceCtorEq] at actual
                                                        | some result =>
                                                            dsimp only [first] at folded
                                                            cases result with
                                                            | stopped processed emitted current => simp only [folded, finish, reduceCtorEq] at actual
                                                            | complete processed emitted endCaller endQueries =>
                                                                have retained := SourcePruningEnumerationSelectedContinuations.run_complete_congr
                                                                  first second checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv
                                                                  edgesOf reached after saved same processed emitted endCaller endQueries folded
                                                                dsimp only [second] at retained
                                                                simp only [folded, finish] at actual
                                                                simpa only [retained, finish] using actual

/-- A complete actual prepared driver run stays exact at larger recursive depth. -/
theorem run_complete_moreDepth
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel larger : Nat) (increase : recursiveFuel ≤ larger)
    (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached)
    (outputs : List (Output width Typing)) (finalCaller : Caller width) (finalQueries : Queries)
    (actual : run holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
      metadata caller queries before = .complete outputs finalCaller finalQueries) :
    run holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel larger
      metadata caller queries before = .complete outputs finalCaller finalQueries :=
  resume_complete_moreDepth holeKey fits admits graph templates checkEmpty edgesOf stop order
    workFuel recursiveFuel larger increase metadata caller queries before
    (SourcePruningEnumerationRestart.decision stop order metadata before)
    outputs finalCaller finalQueries actual

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
