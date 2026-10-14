import MicroCFTA.SourceRecursiveIntersectionSchedule

/-!
# Source Mu-branch domain effects

The source binds each encountered Mu at its own identity. The binding list
keeps left-before-right order. Canonical domain allocation preserves these
original complete records and the inserted recursive pair.
-/
namespace MicroCFTA.SourceRecursiveIntersectionEnvironment
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionDomain SourceRecursiveIntersectionControl
open SourceRecursiveIntersectionSchedule

/-- Retain the original Mu value under its own identity. -/
def binder : Value Symbol Guard → List (Nat × Value Symbol Guard)
  | value@(.mu entry ..) => [(entry.identity, value)]
  | _ => []

/-- The source passes left and then right bindings when both operands are Mu. -/
def bindings (left right : Value Symbol Guard) : List (Nat × Value Symbol Guard) := binder left ++ binder right

/-- Only actual complete Mu operands add a source binding. -/
def muNames : IntersectSchedule.Input → List Nat
  | .mu name => [name]
  | _ => []

/-- Physical Mu binding keys agree with the accepted semantic input, without a supplied binding contract. -/
theorem binder_encoded (value : Value Symbol Guard) (input : IntersectSchedule.Input)
    (encoded : IntersectionFlatMemoKey.input value.referenceOf = some input) :
    (binder value).map Prod.fst = muNames input := by
  have read : (binder value).map Prod.fst =
      (match value.referenceOf with | .mu name => [name] | _ => []) := by
    cases value <;> rfl
  rw [read, IntersectionFlatMemoKey.input_reconstruct _ _ encoded]
  cases input <;> rfl

/-- Actual Mu bindings retain their complete available original records. -/
theorem bindings_available (state : State Symbol Guard) (left right : Value Symbol Guard)
    (leftAvailable : Available state left) (rightAvailable : Available state right)
    (binding : Nat × Value Symbol Guard) (member : binding ∈ bindings left right) :
    ∃ entry body depth ordinary, binding = (entry.identity, Value.mu entry body depth ordinary) ∧
      Available state (.mu entry body depth ordinary) := by
  rcases List.mem_append.mp member with first | second
  · cases left <;> simp only [binder, List.mem_nil_iff, List.mem_singleton] at first
    subst binding
    exact ⟨_, _, _, _, rfl, leftAvailable⟩
  · cases right <;> simp only [binder, List.mem_nil_iff, List.mem_singleton] at second
    subst binding
    exact ⟨_, _, _, _, rfl, rightAvailable⟩

/-- Actual source domain allocation retains the exact ordered structural key. -/
def enter (cache : Cache.State DomainKey) (source : DomainKey) (left right : Value Symbol Guard)
    (first second : Nat) : Interned DomainKey × Cache.State DomainKey :=
  IntersectionEmptyDomain.make cache (extend source ((bindings left right).map Prod.fst) (pair first second))

/-- The encountered source Mu values derive the full extended binding invariant. -/
theorem entered_bindings (state : State Symbol Guard) (source : DomainKey) (old : AvailableBindings state source)
    (left right : Value Symbol Guard) (leftAvailable : Available state left) (rightAvailable : Available state right)
    (first second : Nat) :
    AvailableBindings state (extend source ((bindings left right).map Prod.fst) (pair first second)) := by
  apply extend_available state source _ _ old
  intro name member
  obtain ⟨binding, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨entry, body, depth, ordinary, rfl, available⟩ :=
    bindings_available state left right leftAvailable rightAvailable binding present
  exact ⟨entry, body, depth, ordinary, rfl, available⟩

/-- Source domain construction derives canonical order, exact cache allocation, and complete physical bindings. -/
theorem enter_correct (state : State Symbol Guard) (cache : Cache.State DomainKey) (valid : Cache.Valid cache)
    (source : DomainKey) (old : AvailableBindings state source) (left right : Value Symbol Guard)
    (leftAvailable : Available state left) (rightAvailable : Available state right) (first second : Nat) :
    let key := extend source ((bindings left right).map Prod.fst) (pair first second)
    Cache.Valid (enter cache source left right first second).2 ∧
      IntersectionEmptyDomain.Represents (enter cache source left right first second).2 key
        (enter cache source left right first second).1 ∧
      Canonical key ∧ Typed key ∧ AvailableBindings state key := by
  dsimp only
  have allocated := intern_extended cache valid source ((bindings left right).map Prod.fst) (pair first second)
  exact ⟨allocated.1, allocated.2, extend_canonical _ _ _, extend_typed _ _ _,
    entered_bindings state source old left right leftAvailable rightAvailable first second⟩

/-- Typed source domains retain the exact last-new-binding overwrite and old-map fallback. -/
theorem enter_overwrite (source : DomainKey) (typed : Typed source) (left right : Value Symbol Guard)
    (first second name : Nat) :
    keyLookup (extend source ((bindings left right).map Prod.fst) (pair first second)) name =
      keyLookup ⟨(((bindings left right).map Prod.fst).map (fun key => (key, NodeRef.mu key))).reverse ++ source.free,
        pair first second :: source.seen⟩ name :=
  extend_lookup_source source typed _ _ name

/-- Each newly bound identity resolves to the exact encountered source Mu payload. -/
theorem enter_lookup (state : State Symbol Guard) (facts : Facts state) (source : DomainKey)
    (left right : Value Symbol Guard) (leftAvailable : Available state left) (rightAvailable : Available state right)
    (first second : Nat) (binding : Nat × Value Symbol Guard) (member : binding ∈ bindings left right) :
    lookup state (extend source ((bindings left right).map Prod.fst) (pair first second)) binding.1 = some binding.2 := by
  obtain ⟨entry, body, depth, ordinary, rfl, available⟩ :=
    bindings_available state left right leftAvailable rightAvailable binding member
  apply lookup_mu state facts _ entry body depth ordinary available
  apply (extend_names _ _ _ _).mpr
  exact Or.inl (List.mem_map.mpr ⟨(entry.identity, .mu entry body depth ordinary), member, rfl⟩)

/-- Actual extension always inserts the source's independently sorted recursive pair. -/
theorem enter_seen (source : DomainKey) (left right : Value Symbol Guard) (first second : Nat) :
    pair first second ∈ (extend source ((bindings left right).map Prod.fst) (pair first second)).seen := by
  exact (extend_seen _ _ _ _).mpr (Or.inl rfl)

/-- Actual Mu extension has the same binder lookups as the semantic schedule, including both source identities. -/
theorem enter_schedule (source : DomainKey) (left right : Value Symbol Guard) (first second : IntersectSchedule.Input)
    (leftInput : IntersectionFlatMemoKey.input left.referenceOf = some first)
    (rightInput : IntersectionFlatMemoKey.input right.referenceOf = some second)
    (leftId rightId : Nat) (leftIdentity : identity left = some leftId) (rightIdentity : identity right = some rightId)
    (name : Nat) :
    IntersectSchedule.lookup (domain (extend source ((bindings left right).map Prod.fst) (pair leftId rightId))) name =
      IntersectSchedule.lookup
        (IntersectSchedule.extend (domain source)
          ((muNames first ++ muNames second).map (fun key => (key, IntersectSchedule.Input.mu key)))
          (IntersectSchedule.pair first second)) name := by
  rw [extend_lookup, bindings, List.map_append, binder_encoded left first leftInput,
    binder_encoded right second rightInput, pair_encoded left right first second leftInput rightInput
      leftId rightId leftIdentity rightIdentity]

end MicroCFTA.SourceRecursiveIntersectionEnvironment
