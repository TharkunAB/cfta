import MicroCFTA.EnumerationReferences

namespace MicroCFTA.EnumerationReferences
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
variable {Symbol Guard : Type}

/-- Edges read literal pending buckets or holes in stored enumerated fragments. -/
inductive StoredDependency (state : State Symbol Guard) : Nat → Nat → Prop where
  | suspended {source target : Nat} {node : Option Nat} {scs : List Suspended} {sc : Suspended}
      (stored : state.values[source]? = some (.unenumerated node scs))
      (listed : sc ∈ scs) (alias : UnionFind.SameClass state.representatives target sc.var) :
      StoredDependency state source target
  | fragment {source target hole : Nat} {fragment : Fragment Symbol}
      (stored : state.values[source]? = some (.enumerated fragment))
      (contains : HasHole fragment hole) (alias : UnionFind.SameClass state.representatives target hole) :
      StoredDependency state source target

/-- A dependency into an enumerated slot must also start at an enumerated slot. -/
theorem dependency_into_enumerated
    (state : State Symbol Guard) (pending : PendingReferences state) {source target : Nat}
    (edge : StoredDependency state source target)
    (finish : ∃ fragment, state.values[target]? = some (.enumerated fragment)) :
    ∃ fragment, state.values[source]? = some (.enumerated fragment) := by
  cases edge with
  | suspended stored listed alias =>
      obtain ⟨fragment, expanded⟩ := finish
      exact False.elim ((pending _ fragment expanded) _ (List.mem_of_getElem? stored) _ listed alias)
  | fragment stored _contains _alias => exact ⟨_, stored⟩

/-- Every predecessor of an enumerated endpoint on a finite dependency path is enumerated. -/
theorem dependency_path_into_enumerated
    (state : State Symbol Guard) (pending : PendingReferences state)
    (slots : Nat → Nat) (length : Nat)
    (steps : ∀ index, index < length → StoredDependency state (slots index) (slots (index + 1)))
    (finish : ∃ fragment, state.values[slots length]? = some (.enumerated fragment)) :
    ∃ fragment, state.values[slots 0]? = some (.enumerated fragment) := by
  revert steps finish
  induction length with
  | zero => intro _steps finish; exact finish
  | succ length ih =>
      intro steps finish
      have previous := dependency_into_enumerated state pending (steps length (Nat.lt_succ_self length)) finish
      exact ih (fun index bound => steps index (Nat.lt_trans bound (Nat.lt_succ_self length))) previous

/-- A pending source cannot reach an enumerated slot through stored dependencies. -/
theorem pending_path_not_enumerated
    (state : State Symbol Guard) (pending : PendingReferences state)
    (slots : Nat → Nat) (length : Nat)
    (steps : ∀ index, index < length → StoredDependency state (slots index) (slots (index + 1)))
    (node : Option Nat) (bucket : List Suspended)
    (start : state.values[slots 0]? = some (.unenumerated node bucket))
    (fragment : Fragment Symbol) (finish : state.values[slots length]? = some (.enumerated fragment)) : False := by
  obtain ⟨oldFragment, stored⟩ := dependency_path_into_enumerated state pending slots length steps ⟨fragment, finish⟩
  have impossible := start.symm.trans stored
  cases impossible

end MicroCFTA.EnumerationReferences
