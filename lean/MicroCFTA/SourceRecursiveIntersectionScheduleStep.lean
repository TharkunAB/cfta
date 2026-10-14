import MicroCFTA.SourceRecursiveIntersectionMuScheduleCalls
import MicroCFTA.SourceRecursiveIntersectionUnionReferenceScheduleCalls

/-!
# Complete actual branch selection preserves semantic correspondence

Every successful source branch supplies the exact selected semantic action.
Original scope supplies all physical reads. The semantic edge worker uses
one additional level, so the parent bound increases by two levels.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language Binding InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionCode (NodeScope)
open SourceRecursiveIntersectionInputView (view inputOf row)
open SourceRecursiveIntersectionScheduleConstructors (Corresponds)
open SourceRecursiveIntersectionScheduleEnvironment (Ordered)
open SourceRecursiveIntersectionControl (decision)

/-- The full physical branch selector derives its exact semantic result from recursive correspondence. -/
theorem onNode_schedule [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (scopes : SourceRecursiveIntersectionScopeCalls.ScopedCalls call)
    (state : Machine Symbol Guard) (valid : Valid state)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap state.heap) (guarded : InternedGuardedProbeHeap.Heap state.heap)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (fuel : Nat) (correct : ScheduleCalls call state holds fuel)
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (known : Domain state domain)
    (scope : NodeScope state.heap ⟨domain, left, right⟩) (ordered : Ordered domain.key.seen)
    (value : Value Symbol Guard) (done : onNode emptyGuard conjoin call domain left right state = .done value state) :
    ∃ shape, IntersectSchedule.run (view state.heap holds) (fuel + 2) (SourceRecursiveIntersectionSchedule.domain domain.key)
      (inputOf left) (inputOf right) = .ok shape ∧ Corresponds holds value shape := by
  have step := SourceRecursiveIntersectionStep.physical_step (view state.heap holds) (fuel + 1) domain.key left right
    (inputOf left) (inputOf right) (scope.left.codec left) (scope.right.codec right)
    (SourceRecursiveIntersectionInputView.closed_readback state.heap valid.1 holds left scope.left scope.leftAvailable)
    (SourceRecursiveIntersectionInputView.closed_readback state.heap valid.1 holds right scope.right scope.rightAvailable)
  suffices branch : ∃ shape, SourceRecursiveIntersectionStep.action (view state.heap holds) (fuel + 1)
      (SourceRecursiveIntersectionSchedule.domain domain.key) (inputOf left) (inputOf right)
      (decision domain.key left right) = some (.ok shape) ∧ Corresponds holds value shape by
    obtain ⟨shape, completed, meaning⟩ := branch
    exact ⟨shape, Option.some.inj (step.symm.trans completed), meaning⟩
  have later := correct.larger call state holds fuel (fuel + 1) (by omega)
  cases selected : decision domain.key left right with
  | empty =>
      simp only [onNode, selected] at done
      cases done
      refine ⟨.empty, rfl, ?_⟩
      intro ambient
      rw [InternedGuardedLanguage.meaning, BinderLanguage.meaning]
  | reset =>
      simp only [onNode, selected] at done
      obtain ⟨shape, completed, meaning⟩ := later IntersectionEmptyDomain.emptyDomain left right (empty_domain state)
        (scope.reset state.heap domain left right) SourceRecursiveIntersectionScheduleEnvironment.ordered_empty value done
      exact ⟨shape, congrArg some completed, meaning⟩
  | self =>
      simp only [onNode, selected] at done
      have same : value = left := (Result.done.inj done).1.symm
      subst value
      refine ⟨(view state.heap holds).copy (inputOf left), rfl, ?_⟩
      rw [SourceRecursiveIntersectionInputView.copy_readback state.heap valid.1 holds left scope.leftAvailable _ (scope.left.codec left)]
      exact SourceRecursiveIntersectionInputView.closed_copy_corresponds holds left scope.left state.heap valid.1 scope.leftAvailable
        (SourceRecursiveIntersectionResultScope.self_closed domain.key left right selected)
  | swap =>
      simp only [onNode, selected] at done
      obtain ⟨shape, completed, meaning⟩ := later domain right left known (scope.swap state.heap domain left right) ordered value done
      exact ⟨shape, congrArg some completed, meaning⟩
  | repeated key =>
      simp only [onNode, selected] at done
      have same : value = SourceRecursiveIntersectionControl.repeatedValue key := (Result.done.inj done).1.symm
      subst value
      exact ⟨.ref (IntersectSchedule.pairName key), rfl, SourceRecursiveIntersectionScheduleConstructors.repeated holds key⟩
  | bothMu =>
      simp only [onNode, selected] at done
      simpa only [selected] using mu_schedule_calls call calls replay scopes state valid semantic guarded holds fuel correct
        domain left right known scope ordered (.inl selected) value done
  | leftMu =>
      simp only [onNode, selected] at done
      simpa only [selected] using mu_schedule_calls call calls replay scopes state valid semantic guarded holds fuel correct
        domain left right known scope ordered (.inr (.inl selected)) value done
  | rightMu =>
      simp only [onNode, selected] at done
      simpa only [selected] using mu_schedule_calls call calls replay scopes state valid semantic guarded holds fuel correct
        domain left right known scope ordered (.inr (.inr selected)) value done
  | leftUnion =>
      simp only [onNode, selected] at done
      cases left with
      | union entry members depth free =>
          obtain ⟨shapes, walked, meaning⟩ := union_schedule_calls call calls replay state valid holds fuel correct domain known ordered
            members right true (SourceRecursiveIntersectionCode.union_member_original entry members depth free scope.left)
            scope.right (fun member present => scope.leftAvailable.children member present) scope.rightAvailable scope.bindings value done
          simp only [↓reduceIte] at walked
          refine ⟨.alternatives shapes, ?_, meaning⟩
          change some ((IntersectSchedule.walk (fun member => IntersectSchedule.run (view state.heap holds) (fuel + 1)
            (SourceRecursiveIntersectionSchedule.domain domain.key) member (inputOf right))
            ((view state.heap holds).members entry.identity)).map Shape.alternatives) = some (.ok (.alternatives shapes))
          rw [SourceRecursiveIntersectionInputView.members_readback state.heap valid.1 holds entry members depth free scope.leftAvailable,
            IntersectSchedule.walk_map, walked]
          rfl
      | empty | reference | node | mu => cases done
  | rightUnion =>
      simp only [onNode, selected] at done
      cases right with
      | union entry members depth free =>
          obtain ⟨shapes, walked, meaning⟩ := union_schedule_calls call calls replay state valid holds fuel correct domain known ordered
            members left false (SourceRecursiveIntersectionCode.union_member_original entry members depth free scope.right)
            scope.left (fun member present => scope.rightAvailable.children member present) scope.leftAvailable scope.bindings value done
          simp only [Bool.false_eq_true, ↓reduceIte] at walked
          refine ⟨.alternatives shapes, ?_, meaning⟩
          change some ((IntersectSchedule.walk (fun member => IntersectSchedule.run (view state.heap holds) (fuel + 1)
            (SourceRecursiveIntersectionSchedule.domain domain.key) (inputOf left) member)
            ((view state.heap holds).members entry.identity)).map Shape.alternatives) = some (.ok (.alternatives shapes))
          rw [SourceRecursiveIntersectionInputView.members_readback state.heap valid.1 holds entry members depth free scope.rightAvailable,
            IntersectSchedule.walk_map, walked]
          rfl
      | empty | reference | node | mu => cases done
  | leftReference =>
      simp only [onNode, selected] at done
      cases scope.left with
      | reference name =>
          obtain ⟨shape, completed, meaning⟩ := reference_schedule_calls call state valid holds fuel correct domain known ordered
            name right true scope.right scope.rightAvailable scope.bindings value done
          exact ⟨shape, congrArg some completed, meaning⟩
      | empty | node | union | mu => cases done
  | rightReference =>
      simp only [onNode, selected] at done
      cases scope.right with
      | reference name =>
          obtain ⟨shape, completed, meaning⟩ := reference_schedule_calls call state valid holds fuel correct domain known ordered
            name left false scope.left scope.leftAvailable scope.bindings value done
          exact ⟨shape, congrArg some completed, meaning⟩
      | empty | node | union | mu => cases done
  | ordinary =>
      simp only [onNode, selected] at done
      cases scope.left with
      | node first leftEdges leftDepth leftFree _ =>
          cases scope.right with
          | node second rightEdges rightDepth rightFree _ =>
              obtain ⟨shape, completed, meaning⟩ := node_schedule_calls emptyGuard conjoin call calls replay state valid holds conjoined fuel
                correct domain known first leftEdges leftDepth leftFree second rightEdges rightDepth rightFree scope ordered value done
              refine ⟨shape, ?_, meaning⟩
              change some ((IntersectSchedule.walk (fun pair => IntersectSchedule.edge (view state.heap holds) (fuel + 1)
                (SourceRecursiveIntersectionSchedule.domain domain.key) pair.1 pair.2)
                (IntersectSchedule.joined ((view state.heap holds).rows first.identity) ((view state.heap holds).rows second.identity))).map
                  Shape.alternatives) = some (.ok shape)
              rw [SourceRecursiveIntersectionInputView.rows_readback state.heap valid.1 holds first leftEdges leftDepth leftFree scope.leftAvailable,
                SourceRecursiveIntersectionInputView.rows_readback state.heap valid.1 holds second rightEdges rightDepth rightFree scope.rightAvailable]
              exact congrArg some completed
          | empty | reference | union | mu => cases done
      | empty | reference | union | mu => cases done
  | unsupported =>
      simp only [onNode, selected] at done
      cases done

end MicroCFTA.SourceRecursiveIntersectionKernel
