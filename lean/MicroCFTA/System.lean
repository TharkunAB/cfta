import MicroCFTA.DistinctRank
import MicroCFTA.Sampler
import MicroCFTA.Construction

/-!
# Finite-language indexing and requested distributions

The language, its enumeration order, and its sampling weights are separate.
A finite cover gives an executable index of the entire accepted language.
It need not list runs or know their multiplicities. Every accepted term has
one rank, including terms whose requested sampling weight is zero.

Language-preserving transformations can change rank order. They preserve
requested distributions only when they also preserve the weight of each
term. These are specification theorems. They do not assert that an arbitrary
Haskell optimization satisfies the stated preservation properties.
-/

namespace MicroCFTA.System
open Language DistinctRank Probability

/-- A finite cover can include extra terms, but it must include every accepted term. -/
def FiniteCover (A : Automaton State Symbol) (q : State)
    (cover : List (Term Symbol)) : Prop := ∀ t, Accepts A q t → t ∈ cover

/-- Finiteness yields one height bound for the whole accepted language. -/
theorem finite_height_bound (A : Automaton State Symbol) (q : State)
    (cover : List (Term Symbol)) (complete : FiniteCover A q cover) :
    ∀ t, Accepts A q t → t.height ≤ forestHeight cover := by
  intro t accepted
  exact height_le_forestHeight cover t (complete t accepted)

/-- Compile the complete finite language to a distinct-term reference index. -/
def finiteIndex [DecidableEq Symbol] (A : Automaton State Symbol) (q : State)
    (cover : List (Term Symbol)) (complete : FiniteCover A q cover) : Index (Accepts A q) :=
  finiteLanguage A q (forestHeight cover) (finite_height_bound A q cover complete)

/-- Every term in the finite language has exactly one index, with no unused indices. -/
theorem finite_bijection [DecidableEq Symbol] (A : Automaton State Symbol) (q : State)
    (cover : List (Term Symbol)) (complete : FiniteCover A q cover) :
    let index := finiteIndex A q cover complete
    (∀ rank : Fin index.count, index.encode (index.decode rank) = rank) ∧
    (∀ term : {t // Accepts A q t}, index.decode (index.encode term) = term) := by
  exact ⟨Index.encode_decode _, Index.decode_encode _⟩

/-- Attach the user's relative weight to every distinct member. -/
def weightedMembers (index : Index (α := α) Valid) (weight : α → Rat) : Distribution α :=
  index.members.map fun member => (weight member, member)

/-- The requested probability law normalizes these weights once. -/
def requested (index : Index (α := α) Valid) (weight : α → Rat) : Distribution α :=
  normalize (weightedMembers index weight)

/-- A unique list member contributes exactly its assigned mass. -/
theorem unique_member_mass [DecidableEq α] (members : List α) (unique : members.Nodup)
    (weight : α → Rat) (member : α) :
    eventMass (fun found => decide (found = member)) (members.map fun a => (weight a, a)) =
      if member ∈ members then weight member else 0 := by
  induction members with
  | nil => simp [eventMass]
  | cons a rest ih =>
      obtain ⟨absent, tail⟩ := List.nodup_cons.mp unique
      simp only [List.map_cons, eventMass, ih tail]
      by_cases same : a = member
      · subst a
        simp [absent, Rat.add_zero]
      · by_cases inside : member ∈ rest <;>
          simp [same, Ne.symm same, inside, Rat.zero_add]

/-- Every accepted term receives exactly its requested relative weight. -/
theorem requested_term_probability [DecidableEq α] (index : Index (α := α) Valid)
    (weight : α → Rat) (member : α) (valid : Valid member) :
    eventMass (fun found => decide (found = member)) (requested index weight) =
      weight member / total (weightedMembers index weight) := by
  unfold requested normalize
  rw [eventMass_scale]
  have mass := unique_member_mass index.members index.nodup weight member
  simp only [(index.exact member).mpr valid, ite_true] at mass
  rw [show eventMass (fun found => decide (found = member)) (weightedMembers index weight) = weight member from mass]
  simp [Rat.div_def, Rat.mul_comm]

/-- A nonnegative request with positive total mass defines a probability law. -/
theorem requested_probability (index : Index (α := α) Valid) (weight : α → Rat)
    (nonnegative : ∀ member, Valid member → 0 ≤ weight member)
    (positive : 0 < total (weightedMembers index weight)) : IsProbability (requested index weight) := by
  apply normalize_probability _ _ positive
  intro entry member
  obtain ⟨a, inside, rfl⟩ := List.mem_map.mp member
  exact nonnegative a ((index.exact a).mp inside)

/-- A rejected term cannot be sampled, for any requested weights. -/
theorem rejected_probability [DecidableEq α] (index : Index (α := α) Valid)
    (weight : α → Rat) (member : α) (rejected : ¬ Valid member) :
    eventMass (fun found => decide (found = member)) (requested index weight) = 0 := by
  unfold requested normalize
  rw [eventMass_scale]
  have absent : member ∉ index.members := fun h => rejected ((index.exact member).mp h)
  have mass := unique_member_mass index.members index.nodup weight member
  simp only [absent, ite_false] at mass
  change _ * eventMass _ (index.members.map _) = _
  rw [mass, Rat.mul_zero]

/-- Index order and the choice of finite cover do not change a requested distribution. -/
theorem requested_order_independent [DecidableEq α] (left right : Index (α := α) Valid)
    (weight : α → Rat) (event : α → Bool) :
    eventMass event (requested left weight) = eventMass event (requested right weight) := by
  apply normalized_perm_event
  apply List.Perm.map
  exact (List.perm_ext_iff_of_nodup left.nodup right.nodup).mpr
    (fun a => (left.exact a).trans (right.exact a).symm)

/-- Reinterpret an index after a proved equivalence of accepted languages. -/
def transport (index : Index (α := α) Before) (same : ∀ a, Before a ↔ After a) : Index After where
  members := index.members
  nodup := index.nodup
  exact := fun a => (index.exact a).trans (same a)

/-- An exact optimization preserves cardinality and each term's requested probability. -/
theorem optimization_correct [DecidableEq α]
    (before : Index (α := α) Before) (after : Index (α := α) After)
    (same : ∀ a, Before a ↔ After a) (weight : α → Rat) (event : α → Bool) :
    before.count = after.count ∧
      eventMass event (requested before weight) = eventMass event (requested after weight) := by
  let carried := transport before same
  exact ⟨Index.count_eq carried after, requested_order_independent carried after weight event⟩

/-- Zero sampling weight does not remove a term from the rank space. -/
theorem zero_weight_still_ranked [DecidableEq α] (index : Index (α := α) Valid)
    (weight : α → Rat) (member : {a // Valid a}) (zero : weight member.val = 0) :
    index.decode (index.encode member) = member ∧
      eventMass (fun found => decide (found = member.val)) (requested index weight) = 0 := by
  refine ⟨index.decode_encode member, ?_⟩
  rw [requested_term_probability index weight member.val member.property, zero]
  simp [Rat.div_def]

/-- Build a finite distinct-term index directly from the declared constrained grammar. -/
def grammarIndex [DecidableEq Symbol] (grammar : Construction.Grammar Nonterminal Symbol)
    (start : Construction.Pattern Nonterminal Symbol) (cover : List (Term Symbol))
    (complete : ∀ t, Construction.Derives grammar start t → t ∈ cover) :
    Index (Construction.Derives grammar start) :=
  transport (finiteIndex (Construction.compile grammar) start cover
    (fun t accepted => complete t ((Construction.compile_exact grammar start t).mp accepted)))
    (Construction.compile_exact grammar start)

/-- Grammar construction, complete enumeration, and distinct indexing compose. -/
theorem grammar_bijection [DecidableEq Symbol] (grammar : Construction.Grammar Nonterminal Symbol)
    (start : Construction.Pattern Nonterminal Symbol) (cover : List (Term Symbol))
    (complete : ∀ t, Construction.Derives grammar start t → t ∈ cover) :
    let index := grammarIndex grammar start cover complete
    (∀ rank : Fin index.count, index.encode (index.decode rank) = rank) ∧
    (∀ term : {t // Construction.Derives grammar start t},
      index.decode (index.encode term) = term) := by
  exact ⟨Index.encode_decode _, Index.decode_encode _⟩

/-- The same compiled grammar gives the requested probability of every declared term. -/
theorem grammar_probability [DecidableEq Symbol] (grammar : Construction.Grammar Nonterminal Symbol)
    (start : Construction.Pattern Nonterminal Symbol) (cover : List (Term Symbol))
    (complete : ∀ t, Construction.Derives grammar start t → t ∈ cover)
    (weight : Term Symbol → Rat) (term : Term Symbol)
    (derived : Construction.Derives grammar start term) :
    let index := grammarIndex grammar start cover complete
    eventMass (fun found => decide (found = term)) (requested index weight) =
      weight term / total (weightedMembers index weight) := by
  exact requested_term_probability _ weight term derived

end MicroCFTA.System
