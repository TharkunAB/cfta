import MicroCFTA.SourcePruningEnumerationSharedSelectedCounterGrowth
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
import MicroCFTA.SourceSynthesisOriginalFiniteDriver

/-!
# Allocated roots at actual prepared execution stages

Startup allocates slot zero. Actual callbacks retain the counter.
Successful finalization proves that its target is allocated.
Depth-zero outputs retain the same startup cache and native endpoint.
The general positive-depth output-path induction remains separate.
No result in this module adds positivity to OutputResources.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourceSynthesisOriginalFiniteDriver (startup)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Fragment" => Fragments.Fragment Symbol
variable {Typing Key : Type} {width : Nat}
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- Read the outputs of the literal shared prepared outcome, including stopped prefixes. -/
def emitted : Result → List (Output width Typing)
  | .complete outputs _ _ | .stopped outputs _ _ => outputs

/-- Literal source startup allocates the root before any recursive execution. -/
theorem startup_root (value : Node) (handle : Nat) :
    (startup value handle).core.counter = 1 ∧
      0 < (startup value handle).core.counter ∧
      (startup value handle).core.values[0]? = some (.unenumerated (some handle) []) :=
  ⟨rfl, Nat.zero_lt_succ 0, rfl⟩

/-- An actual successful callback retains the counter and total representative paths. -/
theorem callback_counter
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (input : Sum Fragment Nat)
    (before after : Core) (result : Bool × Metadata Typing)
    (total : UnionFind.Total before.representatives)
    (actual : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input before) =
      [.ok (result, after)]) :
    after.counter = before.counter ∧ UnionFind.Total after.representatives := by
  have success : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input)
      before result after := by
    simp only [Success, actual, List.mem_singleton]
  have frame := SourcePruningRecordTypes.recordTypes_frame
    graph templates fuel metadata uv input before after result total success
  exact ⟨frame.counter, frame.total total⟩

/-- An actual successful finalizer has an allocated target in its aligned returned cache. -/
theorem finalized_root
    (native : InternedConstructorTemplates.State Symbol Constraint)
    (fuel target : Nat) (fragment : Fragment) (before after : Cached)
    (actual : SourcePruningEnumerationFinalize.run native fuel target fragment before = some after)
    (aligned : after.core.counter = after.core.values.length) :
    0 < after.core.counter := by
  unfold SourcePruningEnumerationFinalize.run at actual
  obtain ⟨old, present, written⟩ := Option.bind_eq_some_iff.mp actual
  unfold SourcePruningEnumerationNativeIndex.write at written
  obtain ⟨flag, _classified, written⟩ := Option.bind_eq_some_iff.mp written
  obtain ⟨removed, _removedCounts, written⟩ := Option.bind_eq_some_iff.mp written
  obtain ⟨saved, _savedCounts, afterSame⟩ := Option.bind_eq_some_iff.mp written
  have cacheSame := Option.some.inj afterSame
  have coreSame : after.core = {before.core with
      values := before.core.values.set target (.enumerated fragment), expansionAncestry := []} := by
    rw [← cacheSame]
    rfl
  have lengthSame : after.core.values.length = before.core.values.length := by
    rw [coreSame, List.length_set]
  have inside : target < before.core.values.length := (List.getElem?_eq_some_iff.mp present).1
  rw [aligned, lengthSame]
  exact Nat.lt_of_le_of_lt (Nat.zero_le target) inside

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A complete actual shared edge from startup retains an allocated root at its own endpoint. -/
theorem captured_startup_root
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller reached : Caller width) (queries saved : Queries)
    (value : Node) (handle : Nat) (fragment : Fragment) (after : Cached)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (actual : SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k
      target scs edge caller (startup value handle) queries = some (.complete fragment reached saved after)) :
    0 < after.core.counter := by
  have growth := SourcePruningEnumerationSharedSelectedCounterGrowth.captured
    checkEmpty r n p h k target scs edge caller (startup value handle) queries tries residual projected
  rw [actual] at growth
  exact Nat.lt_of_lt_of_le (startup_root value handle).2.1 growth

/-- Every literal depth-zero output retains the same cache, caller and query memo. -/
theorem resume_zero_output
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel : Nat) (metadata : Metadata Typing) (caller : Caller width) (queries : Queries)
    (before : Cached) (decision : Option Next) (output : Output width Typing)
    (member : output ∈ emitted (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel 0 metadata caller queries before decision)) :
    output.cache = before ∧ output.caller = caller ∧ output.queries = queries := by
  cases decision with
  | none =>
    change output ∈ [⟨some metadata, before, caller, queries⟩] at member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨rfl, rfl, rfl⟩
  | some next =>
    cases next with
    | done =>
      change output ∈ [⟨none, before, caller, queries⟩] at member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨rfl, rfl, rfl⟩
    | stuck => cases member
    | expand uv => cases member

/-- Actual source startup supplies root allocation at every emitted depth-zero output. -/
theorem run_zero_startup_root
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel : Nat) (metadata : Metadata Typing) (caller : Caller width) (queries : Queries)
    (value : Node) (handle : Nat) (output : Output width Typing)
    (member : output ∈ emitted (run holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel 0 metadata caller queries (startup value handle))) :
    output.cache = startup value handle ∧ output.cache.core.counter = 1 ∧
      0 < output.cache.core.counter ∧ output.caller = caller ∧ output.queries = queries := by
  obtain ⟨same, callerSame, querySame⟩ := resume_zero_output
    holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel metadata caller queries
    (startup value handle) (SourcePruningEnumerationRestart.decision stop order metadata (startup value handle))
    output member
  exact ⟨same, by rw [same]; rfl, by rw [same]; exact (startup_root value handle).2.1,
    callerSame, querySame⟩

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
