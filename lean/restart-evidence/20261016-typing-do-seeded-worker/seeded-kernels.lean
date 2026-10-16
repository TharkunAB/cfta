import MicroCFTA.SourceCurrentAllocatedSeededWorkerStability

namespace MicroCFTA.SeededWorkerIndependentKernels
open InternedConstructorTemplates
open SourceCurrentAllocatedSeededWorker
open SourceCurrentAllocatedSeededWorkerCompletion (StableRun)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Empty paths do not inspect even zero bounds or change any checked field. -/
theorem empty_input_retains_whole_state (values : List (Value Symbol Guard)) (before : Checked width) :
    seeded 0 0 0 values [] before = .done .empty before := rfl

/-- A single seed uses projection without a native request. -/
theorem singleton_ignores_native_bound (p h n : Nat) (seed : List Int)
    (values : List (Value Symbol Guard)) (before : Checked width) :
    seeded p h n values [seed] before = operand p h seed values before := rfl

omit [DecidableEq Symbol] in
/-- Projection updates its returned heap at the same equality operations and native tables. -/
theorem projection_retains_native_and_operations (p h : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (before : Checked width)
    (result : Value Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard)
    (done : SourceEqualityProjectionWorker.forest p h path values before.native.machine.heap = .done result heap) :
    operand p h path values before = .done result (advancePhysical before ⟨heap, before.operations⟩) ∧
      (advancePhysical before ⟨heap, before.operations⟩).operations = before.operations ∧
      (advancePhysical before ⟨heap, before.operations⟩).native.nodes = before.native.nodes ∧
      (advancePhysical before ⟨heap, before.operations⟩).native.edges = before.native.edges ∧
      (advancePhysical before ⟨heap, before.operations⟩).native.machine.domains = before.native.machine.domains := by
  obtain ⟨nodes, edges, domains⟩ := SourceCurrentAllocatedQueryMemo.advance_tables before ⟨heap, before.operations⟩
  exact ⟨by simp only [operand, done], rfl, nodes, edges, domains⟩

omit [DecidableEq Symbol] in
/-- An unresolved projection retains both the diagnostic and its reached heap. -/
theorem unresolved_projection_has_exact_state (p h : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (before : Checked width)
    (name : InternedBinderProtocol.Reference) (heap : InternedConstructorTemplates.State Symbol Guard)
    (failed : SourceEqualityProjectionWorker.forest p h path values before.native.machine.heap = .unresolved name heap) :
    operand p h path values before = .failed (.projection (.unresolved name heap))
      (advancePhysical before ⟨heap, before.operations⟩) := by
  simp only [operand, failed]

/-- A failed head skips the seed, tail, and native request. -/
theorem failed_head_stops_fold (p h n : Nat) (values : List (Value Symbol Guard))
    (seed path : List Int) (paths : List (List Int)) (before after : Checked width) (fault : Fault width)
    (failed : operand p h path values before = .failed fault after) :
    fold p h n values seed (path :: paths) before = .failed fault after := by
  simp only [fold, failed, Outcome.bind]

/-- A failed tail retains its full state and skips the final intersection. -/
theorem failed_tail_stops_native (p h n : Nat) (values : List (Value Symbol Guard))
    (seed path : List Int) (paths : List (List Int)) (before middle after : Checked width)
    (head : Value Symbol Guard) (fault : Fault width)
    (first : operand p h path values before = .done head middle)
    (failed : fold p h n values seed paths middle = .failed fault after) :
    fold p h n values seed (path :: paths) before = .failed fault after := by
  simp only [fold, first, failed, Outcome.bind]

/-- Native constraint errors retain the actual complete checked state and message. -/
theorem native_constraint_error_retained (n : Nat) (left right : Value Symbol Guard)
    (before after : Checked width) (message : String)
    (failed : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before =
      .constraintError message after) :
    leaf n left right before = .failed (.native (.constraintError message after)) after := by
  simp only [leaf, failed, SourceEqualityNativeDemand.Outcome.state]

/-- Literal order is head projection, tail fold, then native at the tail return. -/
theorem exact_three_stage_order (p h n : Nat) (values : List (Value Symbol Guard))
    (seed path : List Int) (paths : List (List Int)) (before middle later after : Checked width)
    (head tail result : Value Symbol Guard)
    (one : operand p h path values before = .done head middle)
    (two : fold p h n values seed paths middle = .done tail later)
    (three : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain head tail)) later =
      .done result after) :
    fold p h n values seed (path :: paths) before = .done result after := by
  simp only [fold, one, two, Outcome.bind, leaf, three]

/-- Actual rotated paths supply all three bounds without any extra callback. -/
theorem actual_three_paths_supply_rotated_bounds (values : List (Value Symbol Guard))
    (seed second third : List Int) (before after : Checked width) (result : Value Symbol Guard)
    (actual : SourceCurrentAllocatedSeededQuery.Fold values [second, third, seed] before result after) :
    StableRun (fun p h n => seeded p h n values [seed, second, third] before) result after :=
  SourceCurrentAllocatedSeededWorkerCompletion.seeded_complete (.nonempty actual)

/-- Repeated path occurrences retain two projections and their actual native request. -/
theorem repeated_paths_are_not_removed (values : List (Value Symbol Guard)) (path : List Int)
    (before middle later after : Checked width) (head tail result : Value Symbol Guard)
    (first : SourceCurrentAllocatedSeededQuery.Operand path values before head middle)
    (second : SourceCurrentAllocatedSeededQuery.Operand path values middle tail later)
    (native : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain head tail)) later
      (.code (.pure result)) after) :
    StableRun (fun p h n => seeded p h n values [path, path] before) result after :=
  SourceCurrentAllocatedSeededWorkerCompletion.seeded_complete (.nonempty (.cons first (.one second) native))

/-- Successful incomparable bounds identify the equality operations and both native tables. -/
theorem whole_state_unique (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before after later : Checked width) (first second : Value Symbol Guard)
    (one : seeded p h n values paths before = .done first after)
    (two : seeded P H N values paths before = .done second later) :
    first = second ∧ after.operations = later.operations ∧ after.native.nodes = later.native.nodes ∧
      after.native.edges = later.native.edges ∧ after.native.machine.domains = later.native.machine.domains := by
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedSeededWorkerStability.seeded_done_unique one two
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end MicroCFTA.SeededWorkerIndependentKernels
