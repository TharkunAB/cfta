import MicroCFTA.Language
import MicroCFTA.Probability

/-!
# Distinct terms, ranks, and output mass

An accepting run and its output term are different objects. This file removes
repeated terms from the bounded reference enumeration. It gives the resulting
language exactly one rank per term. The rank range is `Fin count`.

The reference index materializes its language. It specifies correctness, not
an efficient compiler. The Haskell acyclic `fromAutomaton` promises this
interface, but its symbolic compiler is not derived from this reference.
Generator sources and choices can instead retain distinct members with equal
values. Their output masses must be added when members share a term.
-/

namespace MicroCFTA.DistinctRank

open Language Probability

/-- Keep one occurrence of every member. The last occurrence determines order. -/
def distinct [DecidableEq α] : List α → List α
  | [] => []
  | a :: rest =>
      let tail := distinct rest
      if a ∈ tail then tail else a :: tail

/-- Removing repeated members preserves membership. -/
theorem mem_distinct [DecidableEq α] (xs : List α) (a : α) :
    a ∈ distinct xs ↔ a ∈ xs := by
  induction xs with
  | nil => simp [distinct]
  | cons b rest ih =>
      simp only [distinct]
      split
      next hb =>
        rw [ih, List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (rfl | h)
          · exact ih.mp hb
          · exact h
      next hb => simp only [List.mem_cons, ih]

/-- The reference list has no repeated member. -/
theorem distinct_nodup [DecidableEq α] (xs : List α) : (distinct xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
      simp only [distinct]
      split
      · exact ih
      · exact List.nodup_cons.mpr ⟨by assumption, ih⟩

/-- A finite language index stores every valid member exactly once. -/
structure Index (Valid : α → Prop) where
  members : List α
  nodup : members.Nodup
  exact : ∀ a, a ∈ members ↔ Valid a

/-- The number of distinct members in a finite index. -/
def Index.count (index : Index Valid) : Nat := index.members.length

/-- Decode a valid rank, including its language-membership proof. -/
def Index.decode (index : Index Valid) (rank : Fin index.count) : {a // Valid a} :=
  ⟨index.members[rank.val]'rank.isLt, (index.exact _).mp (List.getElem_mem rank.isLt)⟩

/-- Encode a valid member by its unique position in the finite index. -/
def Index.encode [DecidableEq α] (index : Index (α := α) Valid)
    (a : {a // Valid a}) : Fin index.count :=
  ⟨index.members.idxOf a.val, List.idxOf_lt_length_iff.mpr ((index.exact a.val).mpr a.property)⟩

/-- Encoding and then decoding preserves the member. -/
theorem Index.decode_encode [DecidableEq α] (index : Index (α := α) Valid)
    (a : {a // Valid a}) : index.decode (index.encode a) = a := by
  apply Subtype.ext
  exact List.getElem_idxOf _

/-- Distinct valid ranks decode to distinct members. -/
theorem Index.decode_injective (index : Index Valid) (i j : Fin index.count)
    (h : index.decode i = index.decode j) : i = j := by
  apply Fin.ext
  exact (List.Nodup.getElem_inj index.nodup).mp (congrArg Subtype.val h)

/-- Decoding and then encoding preserves the rank. -/
theorem Index.encode_decode [DecidableEq α] (index : Index (α := α) Valid)
    (rank : Fin index.count) : index.encode (index.decode rank) = rank := by
  exact index.decode_injective _ _ (index.decode_encode _)

/-- Each valid member has exactly one valid rank. -/
theorem Index.unique_rank [DecidableEq α] (index : Index (α := α) Valid)
    (a : {a // Valid a}) :
    ∃ rank : Fin index.count, index.decode rank = a ∧
      ∀ other, index.decode other = a → other = rank := by
  exact ⟨index.encode a, index.decode_encode a,
    fun other h => index.decode_injective _ _ (h.trans (index.decode_encode a).symm)⟩

/-- Membership-equivalent indices have the same number of distinct members. -/
theorem Index.count_eq [DecidableEq α] (left right : Index (α := α) Valid) :
    left.count = right.count := by
  apply List.Perm.length_eq
  exact (List.perm_ext_iff_of_nodup left.nodup right.nodup).mpr
    (fun a => (left.exact a).trans (right.exact a).symm)

/-- Translate a rank through its member after a language-preserving optimization. -/
def Index.translate [DecidableEq α] (left right : Index (α := α) Valid)
    (rank : Fin left.count) : Fin right.count := right.encode (left.decode rank)

/-- Translation between language-equivalent indices preserves the decoded member. -/
theorem Index.decode_translate [DecidableEq α] (left right : Index (α := α) Valid)
    (rank : Fin left.count) : right.decode (left.translate right rank) = left.decode rank := by
  exact right.decode_encode _

/-- Rank translation has an inverse. A change in order loses no member. -/
theorem Index.translate_roundtrip [DecidableEq α] (left right : Index (α := α) Valid)
    (rank : Fin left.count) : right.translate left (left.translate right rank) = rank := by
  unfold translate
  rw [right.decode_encode, left.encode_decode]

/-- Equal encodings identify equal valid members. -/
theorem Index.encode_eq_iff [DecidableEq α] (index : Index (α := α) Valid)
    (a b : {a // Valid a}) : index.encode a = index.encode b ↔ a = b := by
  constructor
  · intro h
    have hd := congrArg index.decode h
    simpa only [index.decode_encode] using hd
  · exact congrArg index.encode

/-- Map each weighted member to its unique term rank. Repeated masses remain. -/
def Index.rankDistribution [DecidableEq α] (index : Index (α := α) Valid)
    (dist : Distribution {a // Valid a}) : Distribution (Fin index.count) :=
  Probability.map index.encode dist

/-- Decoding a weighted rank distribution restores every original weighted member. -/
theorem Index.decode_rankDistribution [DecidableEq α] (index : Index (α := α) Valid)
    (dist : Distribution {a // Valid a}) :
    Probability.map index.decode (index.rankDistribution dist) = dist := by
  induction dist with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨mass, a⟩
      simp [rankDistribution, Probability.map, index.decode_encode] at ih ⊢
      exact ih

/-- The weight of a distinct rank is the sum of every member mass at that rank. -/
def Index.rankMass [DecidableEq α] (index : Index (α := α) Valid)
    (dist : Distribution {a // Valid a}) (rank : Fin index.count) : Rat :=
  eventMass (fun found => decide (found = rank)) (index.rankDistribution dist)

/-- Rank mass equals the aggregate mass of its decoded term, including duplicates. -/
theorem Index.rankMass_eq [DecidableEq α] (index : Index (α := α) Valid)
    (dist : Distribution {a // Valid a}) (rank : Fin index.count) :
    index.rankMass dist rank =
      eventMass (fun a => decide (a = index.decode rank)) dist := by
  unfold rankMass rankDistribution
  rw [eventMass_map]
  congr 1
  funext a
  change decide (index.encode a = rank) = decide (a = index.decode rank)
  conv => lhs; rw [← index.encode_decode rank]
  simp only [index.encode_eq_iff]

/-- Exact rank reindexing preserves every observable event mass. -/
theorem Index.rankDistribution_event [DecidableEq α] (index : Index (α := α) Valid)
    (dist : Distribution {a // Valid a}) (event : {a // Valid a} → Bool) :
    eventMass (event ∘ index.decode) (index.rankDistribution dist) =
      eventMass event dist := by
  rw [← eventMass_map event index.decode, index.decode_rankDistribution]

/-- Uniform distinct-term sampling assigns one unit of mass per distinct term. -/
theorem Index.uniform_term_probability [DecidableEq α] (index : Index (α := α) Valid)
    (a : α) (ha : Valid a) :
    eventMass (fun found => found == a) (normalize (counting index.members)) =
      1 / (index.count : Rat) := by
  rw [uniform_event_probability, ← List.count_eq_countP,
    index.nodup.count_of_mem ((index.exact a).mpr ha)]
  rfl

/-- Uniform runs need not yield the uniform distribution on distinct outputs. -/
theorem run_uniformity_is_not_term_uniformity :
    eventMass (fun n : Nat => n == 0) (normalize (counting [0, 0, 1])) = 2 / 3 ∧
    eventMass (fun n : Nat => n == 0)
      (normalize (counting (distinct [0, 0, 1]))) = 1 / 2 := by
  decide +kernel

/-- Structural term equality is executable when symbol equality is executable. -/
instance termDecidableEq [DecidableEq Symbol] : DecidableEq (Term Symbol) := fun t u =>
  if h : termEq t u = true then isTrue ((termEq_correct t u).mp h)
  else isFalse (fun he => h ((termEq_correct t u).mpr he))

/-- Remove repeated terms from the bounded accepting-run enumeration. -/
def bounded [DecidableEq Symbol] (A : Automaton State Symbol) (fuel : Nat) (q : State) :
    Index (fun t => Accepts A q t ∧ t.height ≤ fuel) where
  members := distinct (enumerate A fuel q)
  nodup := distinct_nodup _
  exact := fun t => (mem_distinct _ t).trans (mem_enumerate_iff A fuel q t)

/-- Every bounded accepted term has exactly one rank in `0 .. count - 1`. -/
theorem bounded_unique_rank [DecidableEq Symbol]
    (A : Automaton State Symbol) (fuel : Nat) (q : State)
    (t : Term Symbol) (ha : Accepts A q t) (hh : t.height ≤ fuel) :
    ∃ rank : Fin (bounded A fuel q).count,
      ((bounded A fuel q).decode rank).val = t ∧
      ∀ other, ((bounded A fuel q).decode other).val = t → other = rank := by
  obtain ⟨rank, hr, hu⟩ := (bounded A fuel q).unique_rank ⟨t, ha, hh⟩
  exact ⟨rank, congrArg Subtype.val hr,
    fun other h => hu other (Subtype.ext h)⟩

/-- A bound containing every accepted term gives an index of the whole language. -/
def finiteLanguage [DecidableEq Symbol] (A : Automaton State Symbol) (q : State)
    (fuel : Nat) (covers : ∀ t, Accepts A q t → t.height ≤ fuel) :
    Index (Accepts A q) where
  members := (bounded A fuel q).members
  nodup := (bounded A fuel q).nodup
  exact := by
    intro t
    rw [(bounded A fuel q).exact]
    exact ⟨And.left, fun h => ⟨h, covers t h⟩⟩

end MicroCFTA.DistinctRank
