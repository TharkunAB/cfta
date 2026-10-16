import MicroCFTA.SourceCurrentAllocatedTargetWorkerSound

namespace MicroCFTA.CurrentAllocatedTargetWorkerIntegration
open InternedConstructorTemplates
open SourceCurrentAllocatedTargetWorker
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "requestNode" => SourceRecursiveIntersectionCode.requestNode
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

theorem empty_target_needs_no_bound
    (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo) :
    target 0 0 0 0 0 values [] before memo = .done .empty before memo := rfl

omit [DecidableEq Symbol] in
theorem exhausted_selected_projection_retains_full_checked_state
    (input : Value Symbol Guard) (before : Checked width) (memo : Memo) :
    projection 0 0 [0] [input] before memo =
      .failed (.projection (.exhausted .worker before.native.machine.heap)) before memo := rfl

omit [DecidableEq Symbol] in
theorem negative_forest_index_skips_an_open_value
    (name : InternedBinderProtocol.Reference) (before : Checked width) (memo : Memo) :
    projection 0 0 [-1] [.reference name] before memo = .done .empty before memo := rfl

theorem failed_projection_does_not_enter_merge
    (input : Value Symbol Guard) (before : Checked width) (memo : Memo) :
    operand 0 0 100 100 [0] [input] before memo =
      .failed (.projection (.exhausted .worker before.native.machine.heap)) before memo := rfl

theorem projection_then_warm_merge_hit_retains_all_native_tables
    (input : Value Symbol Guard) (before : Checked width) (memo : Memo)
    (entry : SourceCurrentMemoMergeGraph.Entry Symbol Guard)
    (found : memo input.referenceOf = some entry) :
    operand 1 0 1 0 [0] [input] before memo = .done entry.result before memo ∧
      SourceCurrentAllocatedTargetGraph.Operand [0] [input] before memo entry.result before memo := by
  have done : operand 1 0 1 0 [0] [input] before memo = .done entry.result before memo := by
    simp only [operand, projection, SourceEqualityProjectionWorker.forest,
      SourceEqualityProjectionGraph.select, List.getElem?_cons_zero, Int.not_lt.mpr (by decide : (0 : Int) ≤ 0),
      ↓reduceIte, Int.toNat_zero, SourceEqualityProjectionWorker.project, Outcome.bind, merge,
      SourceCurrentAllocatedMergeWorker.call, found]
    rfl
  exact ⟨done, SourceCurrentAllocatedTargetWorkerSound.operand_sound 1 0 1 0 [0] [input]
    before memo entry.result before memo done⟩

theorem native_zero_retains_exact_remaining_control
    (left right : Value Symbol Guard) (before : Checked width) (memo : Memo) :
    leaf 0 left right before memo =
      .failed (.native (.yielded (.code (requestNode emptyDomain left right)) before)) before memo := rfl

theorem native_constraint_error_retains_reached_operations
    (n : Nat) (left right : Value Symbol Guard) (before after : Checked width) (memo : Memo)
    (message : String)
    (failed : SourceEqualityNativeDemand.execute n (.code (requestNode emptyDomain left right)) before =
      .constraintError message after) :
    leaf n left right before memo = .failed (.native (.constraintError message after)) after memo := by
  simp only [leaf, failed, SourceEqualityNativeDemand.Outcome.state]

theorem native_block_retains_request_control_and_state
    (n : Nat) (left right : Value Symbol Guard) (before after : Checked width) (memo : Memo)
    (reason : SourceEqualityNativeDemand.Blocked)
    (control : SourceEqualityNativeDemand.Control (Value Symbol Guard))
    (blocked : SourceEqualityNativeDemand.execute n (.code (requestNode emptyDomain left right)) before =
      .blocked reason control after) :
    leaf n left right before memo = .failed (.native (.blocked reason control after)) after memo := by
  simp only [leaf, blocked, SourceEqualityNativeDemand.Outcome.state]

theorem allocated_merge_failure_retains_its_actual_equality_state
    (m s : Nat) (input : Value Symbol Guard) (before : Checked width) (memo saved : Memo)
    (after : SourceCurrentAllocatedMergeGraph.State) (fault : SourceCurrentAllocatedMergeWorker.Fault)
    (failed : SourceCurrentAllocatedMergeWorker.call SourceCurrentAllocatedMerge.literalClear
      m s input (physical before) memo = .failed fault after saved) :
    merge m s input before memo = .failed (.merge fault) (advancePhysical before after) saved := by
  simp only [merge, failed]

theorem failed_fold_head_stops_before_seed_and_tail
    (p h m s n : Nat) (values : List (Value Symbol Guard)) (seed path : List Int)
    (paths : List (List Int)) (before after : Checked width) (memo saved : Memo) (fault : Fault width)
    (failed : operand p h m s path values before memo = .failed fault after saved) :
    fold p h m s n values seed (path :: paths) before memo = .failed fault after saved := by
  simp only [fold, failed, Outcome.bind]

theorem fold_native_request_uses_exact_tail_return
    (p h m s n : Nat) (values : List (Value Symbol Guard)) (seed path : List Int)
    (paths : List (List Int)) (before middle later after : Checked width)
    (memo current saved : Memo) (head tail result : Value Symbol Guard)
    (first : operand p h m s path values before memo = .done head middle current)
    (rest : fold p h m s n values seed paths middle current = .done tail later saved)
    (native : SourceEqualityNativeDemand.execute n (.code (requestNode emptyDomain head tail)) later =
      .done result after) :
    fold p h m s n values seed (path :: paths) before memo = .done result after saved := by
  simp only [fold, first, Outcome.bind, rest, leaf, native]

theorem selected_closed_value_allows_an_unrelated_open_sibling
    (input : Value Symbol Guard) (closed : input.free = [])
    (name : InternedBinderProtocol.Reference) (p h m s : Nat)
    (before after : Checked width) (memo saved : Memo) (result : Value Symbol Guard)
    (done : operand p h m s [0] [input, .reference name] before memo = .done result after saved) :
    SourceEqualityProjectionPathDomain.ForestClosed [0] [input, .reference name] ∧
      SourceCurrentAllocatedTargetGraph.Operand [0] [input, .reference name]
        before memo result after saved := by
  constructor
  · intro value selected
    have same : some input = some value := selected
    cases same
    simpa only [SourceEqualityProjectionPathDomain.NodeClosed] using closed
  · exact SourceCurrentAllocatedTargetWorkerSound.operand_sound p h m s [0] [input, .reference name]
      before memo result after saved done

theorem native_success_derives_physical_graph_from_initial_checks
    (n : Nat) (left right result : Value Symbol Guard) (before after : Checked width) (memo : Memo)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (leftAvailable : InternedProbeProvenance.Available before.native.machine.heap left)
    (rightAvailable : InternedProbeProvenance.Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (requestNode emptyDomain left right)) before)
    (done : SourceEqualityNativeDemand.execute n (.code (requestNode emptyDomain left right)) before =
      .done result after) :
    leaf n left right before memo = .done result after memo ∧
      SourceCurrentAllocatedTargetQuery.Step left right before result after := by
  have completed : leaf n left right before memo = .done result after memo := by
    simp only [leaf, done]
  exact ⟨completed, (SourceCurrentAllocatedTargetWorkerSound.leaf_sound n left right before memo
    ready.good ready.idle leftAvailable rightAvailable leftClosed rightClosed ranges result after memo completed).1⟩

end MicroCFTA.CurrentAllocatedTargetWorkerIntegration
