import MicroCFTA.SourceCurrentConjunctionRowsWorker

namespace MicroCFTA.CurrentConjunctionRowsWorkerIntegration
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker
variable {Symbol Formula : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

theorem empty_rows_use_no_bounds_or_equality_allocation
    (before : Physical Symbol Formula) : rows 0 0 [] before = .done [] before := rfl

theorem one_open_reference_has_no_exposed_tuple
    (name : InternedBinderProtocol.Reference) (before : Physical Symbol Formula) :
    rows 0 0 [.reference name] before = .done [] before := rfl

omit [DecidableEq Symbol] in
theorem failed_exposure_retains_exact_heap_and_skips_operand_suffix
    (h : Nat) (node : (Value Symbol (SourceSymbolicIndex.Constraint Formula))) (nodes : List (Value Symbol (SourceSymbolicIndex.Constraint Formula))) (before : Physical Symbol Formula)
    (heap : InternedConstructorTemplates.State Symbol (SourceSymbolicIndex.Constraint Formula)) (key : InternedBinderProtocol.NodeKey)
    (pending : MergedFreshOrdinaryExposure.nodeEdges h node before.heap = .pending key heap) :
    exposures h (node :: nodes) before = .failed (.pending key) ⟨heap, before.equality⟩ := by
  simp only [exposures, pending]

omit [DecidableEq Symbol] in
theorem exhausted_projection_stops_before_later_jobs
    (input : (Value Symbol (SourceSymbolicIndex.Constraint Formula))) (jobs : List (Job Symbol Formula)) (before : Physical Symbol Formula) :
    projections 0 0 (([input], [0]) :: jobs) before = .failed (.exhausted .worker) before := rfl

omit [DecidableEq Symbol] in
theorem equality_error_retains_literal_fold_operations
    (p h : Nat) (edges : List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))) (before : Physical Symbol Formula)
    (message : String)
    (failed : (SourceCurrentConjunctionEquality.fold edges before.equality).1 = .error message) :
    tuple p h edges before = .failed (.equality message)
      ⟨before.heap, (SourceCurrentConjunctionEquality.fold edges before.equality).2⟩ := by
  simp only [tuple, failed]

omit [DecidableEq Symbol] in
theorem missing_equality_keeps_the_returned_fold_cache
    (p h : Nat) (edges : List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))) (before : Physical Symbol Formula)
    (missing : (SourceCurrentConjunctionEquality.fold edges before.equality).1 = .ok none) :
    tuple p h edges before = .failed .missingEquality
      ⟨before.heap, (SourceCurrentConjunctionEquality.fold edges before.equality).2⟩ := by
  simp only [tuple, missing]

omit [DecidableEq Symbol] in
theorem contradictory_head_skips_suffix_accessors_and_projection
    (edge : (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))) (suffix : List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))) (before : Physical Symbol Formula)
    (contradictory : (SourceCurrentConjunctionEquality.accessor edge.entry.key.constraint before.equality).1 =
      .ok (some .contradiction)) :
    tuple 0 0 (edge :: suffix) before = .done none
      ⟨before.heap, (SourceCurrentConjunctionEquality.accessor edge.entry.key.constraint before.equality).2⟩ := by
  simp only [tuple, SourceCurrentConjunctionEquality.fold_stop edge suffix before.equality contradictory]
  rfl

omit [DecidableEq Symbol] in
theorem requirements_do_not_add_an_arity_check
    (edges : List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))) (before : Physical Symbol Formula) :
    requirements 0 0 edges [] before =
      .done ((SourceCurrentConjunctionRequirements.columns edges).map SourceCurrentConjunctionRequirements.canonical) before := by
  simp only [requirements, classes, Outcome.bind, List.append_nil]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
theorem empty_conjunction_shortcut_does_not_read_identity_keys
    (name : InternedBinderProtocol.Reference) :
    SourceCurrentConjunctionRequirements.canonical ([.empty, .reference name] : List (Value Symbol (SourceSymbolicIndex.Constraint Formula))) = [.empty] := rfl

omit [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
theorem tuple_order_places_tail_operands_before_original_head
    (first second third : (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula)))
    (thirdFirst : SourceCurrentConjunctionTuples.shape third = SourceCurrentConjunctionTuples.shape first)
    (secondThird : SourceCurrentConjunctionTuples.shape second = SourceCurrentConjunctionTuples.shape third) :
    SourceCurrentConjunctionTuples.tuples [[first], [second], [third]] = [[second, third, first]] := by
  simp [SourceCurrentConjunctionTuples.tuples, SourceCurrentConjunctionTuples.extend, thirdFirst, secondThird]

end MicroCFTA.CurrentConjunctionRowsWorkerIntegration
