import MicroCFTA.SourceRecursiveIntersectionNativeOrdinaryRows

/-!
# Actual closed diagonal reuse

Closed self-intersection returns the exact input record. A nonempty source
free environment first resets to the empty domain. Both paths retain the
same physical and domain caches. Checked native execution derives this law.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionControl

/-- A closed diagonal source call needs at most a domain reset before exact record reuse. -/
theorem execute_closed_diagonal [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned DomainKey) (value : Value Symbol Guard) (closed : value.free = []) (state : Machine Symbol Guard) :
    execute emptyGuard conjoin (fuel + 2) domain value value state = .done value state := by
  by_cases empty : value = .empty
  · subst value
    simp only [execute, onNode, decision, hasEmpty, Value.referenceOf, beq_self_eq_true, Bool.or_self, ite_true]
  · have nonempty : value.referenceOf ≠ .empty := fun same => empty ((EqualityLeafProjectionPhysical.reference_empty value).mp same)
    have noEmpty : hasEmpty value value = false := by
      simp only [hasEmpty, Bool.or_self]
      apply Bool.eq_false_iff.mpr
      intro impossible
      exact nonempty (beq_iff_eq.mp impossible)
    have same : closedSelf value value = true := by simp only [closedSelf, beq_self_eq_true, closed, List.isEmpty_nil, Bool.and_self]
    have initial : reset IntersectionEmptyDomain.emptyDomain.key value value = false := by
      simp only [reset, IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey, List.isEmpty_nil,
        Bool.not_true, Bool.and_false]
    by_cases restart : reset domain.key value value = true
    · have selected := SourceRecursiveIntersectionControl.reset_first domain.key value value noEmpty restart
      simp only [execute, onNode, selected]
      rw [self_first _ _ _ noEmpty initial same]
    · have noRestart : reset domain.key value value = false := by cases own : reset domain.key value value <;> simp_all
      have selected := self_first domain.key value value noEmpty noRestart same
      simp only [execute, onNode, selected]

end MicroCFTA.SourceRecursiveIntersectionKernel

namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks

/-- An actual checked native closed self-intersection returns the identical record and unchanged physical/domain machine. -/
theorem native_closed_diagonal [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (domain : Interned DomainKey)
    (value result : Value Symbol Guard) (closed : value.free = [])
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : NodeReady state.machine ⟨domain, value, value⟩)
    (done : execute emptyGuard conjoin fuel (.node ⟨domain, value, value⟩ .pure) state = .done result after)
    (ranges : WordRanges emptyGuard conjoin (.node ⟨domain, value, value⟩ .pure) state) :
    result = value ∧ after.machine = state.machine := by
  have evaluated := evaluation_of_done emptyGuard conjoin fuel _ state after result done
  obtain ⟨_, _, _, bound, completed⟩ := native_node_correct emptyGuard conjoin fuel _ state after result valid ready done
    (evaluated.bounds_of_ranges ranges)
  exact Result.done.inj ((completed 2).symm.trans (execute_closed_diagonal emptyGuard conjoin bound domain value closed state.machine))

end MicroCFTA.SourceRecursiveIntersectionNative
