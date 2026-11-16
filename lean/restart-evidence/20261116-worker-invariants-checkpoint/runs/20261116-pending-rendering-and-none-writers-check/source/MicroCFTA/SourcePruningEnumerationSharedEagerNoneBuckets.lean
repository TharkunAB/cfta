import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
import MicroCFTA.EnumerationCompressionFrame

namespace MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "HookResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
set_option autoImplicit false
variable {Typing Key : Type} {width : Nat}

/-- Missing graph domains retain no suspended path bucket. -/
def NoneBucketsEmpty (state : Core) : Prop :=
  ∀ (uv : Nat) (scs : List Suspended),
    state.values[uv]? = some (.unenumerated none scs) → scs = []

/-- Read only successful enumeration-state observations in an actual raw result. -/
def rawCores {α : Type} (raw : List (Except EnumerationState.Error (α × Core))) : List Core :=
  raw.flatMap fun row => match row with
    | .error _ => []
    | .ok (_, state) => [state]

/-- Observe the current prefix's reached cores and its successful raw stages. -/
def selectedCores : SourcePruningEnumerationSelectedStep.Result width Typing → List Core
  | .stopped read checked => rawCores read ++ checked.toList.flatMap rawCores
  | .parked checked candidate raw =>
      checked :: (candidate.toList.map (fun after => after.core) ++ raw.toList.flatMap rawCores)
  | .narrowed checked _prepared _caller _queries action candidate right ordinary =>
      checked :: (action.toList.flatMap rawCores ++ candidate.toList.map (fun after => after.core) ++
        right.toList.flatMap rawCores ++ ordinary.toList.flatMap (fun observed => rawCores observed.1))

/-- A shared child observation retains an outer core and any successful raw cores. -/
def childCores (observation : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.Observation width) :
    List Core :=
  observation.2.2.2.1 :: (match observation.1 with
    | .ok none => []
    | .ok (some raw) => rawCores raw
    | .error (.inl raw) => rawCores raw
    | .error (.inr (.inl _native)) => []
    | .error (.inr (.inr raw)) => rawCores raw)

/-- Observe the real cache or stopping child cores in one actual edge receipt. -/
def receiptCores : Receipt width → List Core
  | .unhandled => []
  | .rejected _caller _queries after => [after.core]
  | .stopped _completed observation candidate =>
      childCores observation ++ candidate.toList.map (fun after => after.core)
  | .finalizeStopped _fragment _caller _queries before => [before.core]
  | .complete _fragment _caller _queries after => [after.core]

/-- Retain concrete enumeration snapshots from every actual worker stop reason. -/
def failureCores : Failure width Typing → List Core
  | .exhausted _uv _metadata before => [before.core]
  | .selected _uv observed => selectedCores observed
  | .callback _uv raw => rawCores raw
  | .preparation _uv observed => rawCores observed.1
  | .alternatives _uv processed (.edge current _endpoint) =>
      processed.flatMap receiptCores ++ current.toList.flatMap receiptCores
  | .alternatives _uv processed (.continuation current reason _endpoint) =>
      processed.flatMap receiptCores ++ receiptCores current ++ failureCores reason

/-- Cover every emitted cache and every actual retained enum stop endpoint. -/
def Preserved : HookResult (Output width Typing) (Failure width Typing) width → Prop
  | .complete outputs _caller _queries =>
      ∀ output ∈ outputs, NoneBucketsEmpty output.cache.core
  | .stopped outputs reason _endpoint =>
      (∀ output ∈ outputs, NoneBucketsEmpty output.cache.core) ∧
        ∀ state ∈ failureCores reason, NoneBucketsEmpty state

/-- Equal value arrays retain the missing-domain bucket property. -/
theorem none_buckets_of_values_eq (before after : Core)
    (initial : NoneBucketsEmpty before) (values : after.values = before.values) : NoneBucketsEmpty after := by
  intro uv scs stored
  exact initial uv scs (by simpa only [values] using stored)

/-- Fresh allocation stores an empty bucket for either optional domain. -/
theorem allocated_none_buckets (node : Option Nat) (before : Core)
    (initial : NoneBucketsEmpty before) : NoneBucketsEmpty (allocated node before) := by
  intro uv scs stored
  have member : UVarValue.unenumerated none scs ∈ before.values ++ [.unenumerated node []] :=
    List.mem_of_getElem? stored
  rcases List.mem_append.mp member with old | fresh
  · obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp old
    exact initial index scs found
  · have same := List.mem_singleton.mp fresh
    cases node with
    | none => exact (UVarValue.unenumerated.inj same).2
    | some handle => cases same

/-- A literal Some-handle write cannot create a missing-domain bucket. -/
theorem some_write_none_buckets (target handle : Nat) (bucket : List Suspended) (before after : Core)
    (initial : NoneBucketsEmpty before)
    (actual : EnumerationCorrectness.Success (setValue target (.unenumerated (some handle) bucket)) before () after) :
    NoneBucketsEmpty after := by
  obtain rfl := (EnumerationDriver.modify_success _ before after).mp actual
  intro uv scs stored
  rcases List.mem_or_eq_of_mem_set (List.mem_of_getElem? stored) with old | same
  · obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp old
    exact initial index scs found
  · cases same

/-- A final fragment write cannot create a missing-domain pending slot. -/
theorem enumerated_write_none_buckets (target : Nat) (fragment : Fragments.Fragment Symbol) (before after : Core)
    (initial : NoneBucketsEmpty before)
    (actual : EnumerationCorrectness.Success (setValue target (.enumerated fragment)) before () after) :
    NoneBucketsEmpty after := by
  obtain rfl := (EnumerationDriver.modify_success _ before after).mp actual
  intro uv scs stored
  rcases List.mem_or_eq_of_mem_set (List.mem_of_getElem? stored) with old | same
  · obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp old
    exact initial index scs found
  · cases same

theorem runEager_real_none_buckets_zero
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel : Nat) (metadata : Metadata Typing)
    (caller : Caller width) (queries : Queries) (before : Cached)
    (initial : NoneBucketsEmpty before.core) :
    Preserved (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
      (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates checkEmpty edgesOf stop order
      workFuel 0 metadata caller queries before)
 := by
  unfold SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
    SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runWithNarrow
  cases selected : SourcePruningEnumerationRestart.decision stop order metadata before with
  | none =>
      intro output member
      have same := List.mem_singleton.mp member
      subst output
      exact initial
  | some decision =>
      cases decision with
      | done =>
          intro output member
          have same := List.mem_singleton.mp member
          subst output
          exact initial
      | stuck =>
          intro output impossible
          cases impossible
      | expand uv =>
          constructor
          · intro output impossible
            cases impossible
          · intro state member
            have same := List.mem_singleton.mp member
            subst state
            exact initial

end MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets

#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets.none_buckets_of_values_eq
#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets.allocated_none_buckets
#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets.some_write_none_buckets
#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets.enumerated_write_none_buckets
#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets.runEager_real_none_buckets_zero
