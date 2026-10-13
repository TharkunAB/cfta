import MicroCFTA.InternedNormalizationDepthExact
import MicroCFTA.InternedFilterSelfReference
import MicroCFTA.InternedStoredMuOrigins

/-!
# Deep free names determine actual smart cleanup depth

Deep names occur below an ordinary or Mu boundary. Root union alternatives
do not contribute deep names. Root self filtering preserves depth and
removes a local's root alternatives. A smart binder adds one precisely
when that local still has a deep occurrence.
-/
namespace MicroCFTA.InternedDeepFreeDepth
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (finish)
open InternedUnionNormalForm InternedNormalizationFree InternedStoredMuOrigins
open InternedBinderProtocol (Reference NodeKey)

mutual
/-- References under an ordinary or Mu boundary are deep; bare roots are not. -/
def deepNames : Value Symbol Guard → List Reference
  | .empty | .reference _ => []
  | value@(.node ..) | value@(.mu ..) => value.free
  | .union _ members _ _ => deepMany members
termination_by value => sizeOf value

/-- A root union retains the deep names from each original alternative. -/
def deepMany : List (Value Symbol Guard) → List Reference
  | [] => []
  | first :: rest => deepNames first ++ deepMany rest
termination_by values => sizeOf values
end

/-- Deep membership in a root union selects one actual operand. -/
theorem deepMany_member (values : List (Value Symbol Guard)) (name : Reference) :
    name ∈ deepMany values ↔ ∃ value ∈ values, name ∈ deepNames value := by
  induction values with
  | nil => simp [deepMany]
  | cons first rest ih => simp [deepMany, ih]

/-- A flat operand has a deep occurrence exactly when it has a nonbare occurrence. -/
theorem atomic_deep (value : Value Symbol Guard) (atomic : Atomic value) (name : Reference) :
    name ∈ deepNames value ↔ name ∈ value.free ∧ value ≠ .reference name := by
  cases value <;> simp_all [Atomic, deepNames, Value.free]

/-- A normalized union retains a local free name exactly through a deep operand. -/
theorem union_filter_free [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (level : Nat) (free : List Reference)
    (state : State Symbol Guard) (normal : Normal state)
    (available : Available state (.union entry members level free)) :
    name ∈ (run (withoutSelfReference name (.union entry members level free)) state).1.free ↔
      name ∈ deepNames (.union entry members level free) := by
  have atomic := resident_flat state normal.flat _ available.resident
  have deep : name ∈ deepNames (.union entry members level free) ↔
      ∃ value ∈ members, name ∈ value.free ∧ value ≠ .reference name := by
    rw [deepNames, deepMany_member]
    apply exists_congr
    intro value
    apply and_congr_right
    intro member
    exact atomic_deep value (atomic value member) name
  rw [deep]
  by_cases present : .reference name ∈ members
  · have selected : members.any (fun member => member.referenceOf == .ref name) = true :=
      List.any_eq_true.mpr ⟨.reference name, present, by simp [Value.referenceOf]⟩
    simp only [withoutSelfReference, selected, ↓reduceIte]
    rw [makeUnion_free (members.filter (fun member => member.referenceOf != .ref name)) state normal.facts.coherent normal.facts.cached normal.facts.linked normal.live
      (fun value member => available.children value (List.mem_filter.mp member).1) name]
    constructor
    · rintro ⟨value, included, free⟩
      obtain ⟨member, different⟩ := (withoutSelfReference_members name members value).mp included
      exact ⟨value, member, free, different⟩
    · rintro ⟨value, included, free, different⟩
      exact ⟨value, (withoutSelfReference_members name members value).mpr ⟨included, different⟩, free⟩
  · rw [withoutSelfReference_absent name entry members level free present]
    simp only [run, Value.free]
    rw [union_free state normal.facts.coherent entry members level free available.resident, childFree_member]
    constructor
    · rintro ⟨value, included, free⟩
      exact ⟨value, included, free, fun same => present (same ▸ included)⟩
    · rintro ⟨value, included, free, _⟩
      exact ⟨value, included, free⟩

/-- Outside the direct-self case, normalized local membership is exactly deep membership. -/
theorem filter_free [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state value)
    (nonbare : value ≠ .reference name) :
    name ∈ (run (withoutSelfReference name value) state).1.free ↔ name ∈ deepNames value := by
  cases value with
  | empty => simp [withoutSelfReference, run, Value.free, deepNames]
  | reference other => simp_all [withoutSelfReference, run, Value.free, deepNames, ne_comm]
  | node | mu => simp only [withoutSelfReference, run, deepNames]
  | union entry members level free => exact union_filter_free name entry members level free state normal available

/-- Actual filtering and cleanup add one depth exactly for a raw binder or a deep local. -/
theorem finish_filter_depth [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (entry : Interned NodeKey) (value depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state value) :
    (finish smart (.mu entry (run (withoutSelfReference (.interned entry.identity) value) state).1 depth ordinary)).depth =
      if smart then
        if .interned entry.identity ∈ deepNames value then value.depth + 1 else value.depth
      else value.depth + 1 := by
  classical
  have depthSame := InternedNormalizationDepthExact.filter_depth (.interned entry.identity) value state
    normal.facts.coherent normal.facts.cached normal.facts.linked normal.live available
  cases smart with
  | false => simpa only [finish, Bool.false_eq_true, ↓reduceIte, Value.depth] using congrArg (· + 1) depthSame
  | true =>
      by_cases bare : value = .reference (.interned entry.identity)
      · subst value
        simp [finish, cleanup, withoutSelfReference, run, Value.free, Value.referenceOf, Value.depth, deepNames]
      · have nonbare : (run (withoutSelfReference (.interned entry.identity) value) state).1 ≠
            .reference (.interned entry.identity) := fun equal =>
          bare ((InternedFilterSelfReference.filter_self_iff (.interned entry.identity) value state
            normal.facts.coherent normal.flat available).mp equal)
        have notSelf : (run (withoutSelfReference (.interned entry.identity) value) state).1.referenceOf ≠
            .ref (.interned entry.identity) := fun same => nonbare ((referenceOf_self_iff _ _).mp same)
        have same := filter_free (.interned entry.identity) value state normal available bare
        by_cases live : .interned entry.identity ∈ deepNames value
        · have used := same.mpr live
          simp [finish, cleanup, used, notSelf, live, Value.depth, depthSame]
        · have unused : .interned entry.identity ∉ (run (withoutSelfReference (.interned entry.identity) value) state).1.free :=
            fun used => live (same.mp used)
          simp [finish, cleanup, unused, live, depthSame]

end MicroCFTA.InternedDeepFreeDepth
