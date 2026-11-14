import MicroCFTA.SourceRecursiveIntersectionKernelReadback
import MicroCFTA.InternedBoundaryAtoms
import MicroCFTA.SourceRecursiveIntersectionDomainEquivalence

/-!
# Exact closed-child reset steps in the original mixed domain

The actual entered domain has the original Mu binding.
An Empty operand completes before reset. Other closed operands reset once.
Both equations retain the same actual machine and recursive child order.
-/
namespace MicroCFTA.SourceSynthesisUniverseClosedResetSteps
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl
open SourceRecursiveIntersectionDomain SourceRecursiveIntersectionEnvironment

set_option autoImplicit false
variable {Symbol Guard : Type}

/-- The literal original Mu entry retains a nonempty free map independently of later effects. -/
theorem mixed_entry_nonempty_free_map
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (valid : Cache.Valid domains)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (pattern : Value Symbol Guard) (patternId : Nat) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let original := enter domains IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
    original.1.key.free.isEmpty = false := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let original := enter domains IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  have added : entry.identity ∈ (bindings universeValue pattern).map Prod.fst := by
    change entry.identity ∈ entry.identity :: (binder pattern).map Prod.fst
    exact List.mem_cons_self
  have originalKey := SourceRecursiveIntersectionSchedule.entered_key domains valid
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  have named : entry.identity ∈ names original.1.key := by
    rw [originalKey]
    exact (extend_names _ _ _ _).mpr (Or.inl added)
  change original.1.key.free.isEmpty = false
  cases freeMap : original.1.key.free with
  | nil => simp only [names, freeMap, List.map_nil, List.not_mem_nil] at named
  | cons first rest => rfl

/-- Positive-fuel closed calls preserve Empty priority or reset to the exact lower-fuel call. -/
theorem execute_closed_nonempty_domain_step
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (nonempty : domain.key.free.isEmpty = false)
    (left right : Value Symbol Guard) (leftClosed : left.free = []) (rightClosed : right.free = [])
    (state : Machine Symbol Guard) :
    execute emptyGuard conjoin (fuel + 1) domain left right state =
      if hasEmpty left right = true then .done .empty state
      else execute emptyGuard conjoin fuel IntersectionEmptyDomain.emptyDomain left right state := by
  by_cases empty : hasEmpty left right = true
  · have selected := empty_first domain.key left right empty
    rw [ite_eq_left empty, execute]
    simp only [onNode, selected]
  · have noEmpty : hasEmpty left right = false := by
      cases value : hasEmpty left right <;> simp_all
    have restart : reset domain.key left right = true := by
      simp [reset, leftClosed, rightClosed, nonempty]
    have selected := reset_first domain.key left right noEmpty restart
    rw [ite_eq_right empty, execute]
    simp only [onNode, selected]

/-- A closed child call uses only the strictly smaller empty-domain fuel induction hypothesis. -/
theorem closed_reset_atoms_of_fuel_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (nonempty : domain.key.free.isEmpty = false) (ownerId : Nat)
    (left right : Value Symbol Guard) (leftClosed : left.free = []) (rightClosed : right.free = [])
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right)
    (fuelInduction : ∀ smaller : Nat, smaller < fuel → ∀ (value : Value Symbol Guard) (after : Machine Symbol Guard),
      execute emptyGuard conjoin smaller IntersectionEmptyDomain.emptyDomain left right state = .done value after →
      ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu ownerId) :
    Checked state (execute emptyGuard conjoin fuel domain left right state)
      (fun after value => Available after.heap value ∧
        ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu ownerId) := by
  have native := execute_checked emptyGuard conjoin fuel domain left right state valid known leftAvailable rightAvailable
  refine ⟨native.valid, native.extension, ?_⟩
  intro value after returned
  refine ⟨native.result value after returned, ?_⟩
  cases fuel with
  | zero => simp only [execute] at returned; cases returned
  | succ remaining =>
      rw [execute_closed_nonempty_domain_step emptyGuard conjoin remaining domain nonempty
        left right leftClosed rightClosed state] at returned
      by_cases empty : hasEmpty left right = true
      · rw [ite_eq_left empty] at returned
        cases returned
        intro atom occurrence
        simp only [InternedBoundaryAtoms.atoms, List.not_mem_nil] at occurrence
      · rw [ite_eq_right empty] at returned
        exact fuelInduction remaining (Nat.lt_succ_self remaining) value after returned

end MicroCFTA.SourceSynthesisUniverseClosedResetSteps
