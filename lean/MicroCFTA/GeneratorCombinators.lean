import MicroCFTA.Decoder
import MicroCFTA.DistinctRank
import MicroCFTA.Sampler
import MicroCFTA.Sized
import MicroCFTA.SizeMass

/-!
# Finite generator members and grouped composition

These finite executable operations model `Static`, `Bucket`, `Grouped`,
`Join`, `Chain`, and `Query`. Lists retain member order and multiplicity.
A member keeps its engine term, decoded value, and FEAT size. Rational mass
is the first component of each distribution entry. Group sorting changes
rank order but must preserve every original member and its mass.
-/

namespace MicroCFTA.GeneratorCombinators

open Language Probability

/-- Engine labels used by the finite source, choice, product, and binary join operations. -/
inductive Label (Symbol : Type) where
  | user (symbol : Symbol)
  | pure
  | index (rank : Nat)
  | apply
  | choice (branch : Nat)
  | join
  | joinN
  | centerKeyed
  | argKeyed
  | recursion
  | family
  | atKey
  | key (index : Nat)
  | argKey (component argument : Nat)
  | placeholder
  | leftKeyed
  | rightKeyed
  | group (index : Nat)
  deriving DecidableEq

/-- A retained finite member, independent of its sampling mass. -/
structure Member (Symbol Value : Type) where
  term : Term (Label Symbol)
  value : Value
  size : Nat

/-- A finite generator retains every weighted member, including equal outputs. -/
abbrev Finite (Symbol Value : Type) := Distribution (Member Symbol Value)

/-- The member at a replay rank. -/
def select (members : Finite Symbol Value) (rank : Nat) : Option (Rat × Member Symbol Value) :=
  members[rank]?

/-- Every stored member is returned at a valid rank. -/
theorem member_has_rank (members : Finite Symbol Value) (entry : Rat × Member Symbol Value) :
    entry ∈ members ↔ ∃ rank, rank < members.length ∧ select members rank = some entry := by
  constructor
  · intro present
    obtain ⟨rank, bound, same⟩ := List.mem_iff_getElem.mp present
    exact ⟨rank, bound, by simp [select, List.getElem?_eq_getElem bound, same]⟩
  · rintro ⟨rank, _, found⟩
    exact List.mem_of_getElem? found

/-- The one member of `pure` has a private term, size zero, and unit mass. -/
def pureMember (value : Value) : Finite Symbol Value := [(1, ⟨.node .pure [], value, 0⟩)]

/-- An indexed source has one atom per input position, even when values repeat. -/
def indexed (values : List Value) : Finite Symbol Value :=
  List.ofFn fun rank : Fin values.length =>
    (1 / (values.length : Rat), ⟨.node (.index rank.val) [], values[rank.val], 1⟩)

/-- Indexed-source cardinality counts positions rather than distinct values. -/
theorem indexed_count (values : List Value) : (indexed (Symbol := Symbol) values).length = values.length := by
  simp [indexed]

/-- Mapping changes only decoded values. -/
def mapValues (f : α → β) (members : Finite Symbol α) : Finite Symbol β :=
  Probability.map (fun member => ⟨member.term, f member.value, member.size⟩) members

/-- A pay shifts each size by one without changing a replay rank or mass. -/
def pay (members : Finite Symbol Value) : Finite Symbol Value :=
  Probability.map (fun member => {member with size := member.size + 1}) members

/-- An atomic boundary assigns one size to every retained member. -/
def atomic (members : Finite Symbol Value) : Finite Symbol Value :=
  Probability.map (fun member => {member with size := 1}) members

/-- Project the decoded-value distribution, retaining member multiplicity. -/
def values (members : Finite Symbol Value) : Distribution Value :=
  Probability.map Member.value members

/-- Mapping preserves the number and order of replay positions. -/
theorem mapValues_count (f : α → β) (members : Finite Symbol α) :
    (mapValues f members).length = members.length := by simp [mapValues, Probability.map]

/-- Value mapping is the same map on the exact output distribution. -/
theorem mapValues_distribution (f : α → β) (members : Finite Symbol α) :
    values (mapValues f members) = Probability.map f (values members) := by
  simp [values, mapValues, Probability.map, List.map_map]

/-- Paying changes no decoded value or outcome mass. -/
theorem pay_values (members : Finite Symbol Value) : values (pay members) = values members := by
  simp [pay, values, Probability.map, List.map_map]

/-- Atomic sizing changes no decoded value or outcome mass. -/
theorem atomic_values (members : Finite Symbol Value) : values (atomic members) = values members := by
  simp [atomic, values, Probability.map, List.map_map]

/-- Combine two component members without changing their function-major rank order. -/
def pairMember (term : Term (Label Symbol) → Term (Label Symbol) → Term (Label Symbol))
    (left : Member Symbol α) (right : Member Symbol β) : Member Symbol (α × β) :=
  ⟨term left.term right.term, (left.value, right.value), left.size + right.size⟩

/-- The concrete list product multiplies masses and adds component sizes. -/
def pair (term : Term (Label Symbol) → Term (Label Symbol) → Term (Label Symbol))
    (left : Finite Symbol α) (right : Finite Symbol β) : Finite Symbol (α × β) :=
  Probability.map (fun pair => pairMember term pair.1 pair.2) (Probability.product left right)

/-- Applicative terms retain both component terms under the private apply label. -/
def apply (functions : Finite Symbol (α → β)) (arguments : Finite Symbol α) : Finite Symbol β :=
  mapValues (fun pair => pair.1 pair.2) (pair (fun f x => .node .apply [f, x]) functions arguments)

/-- A distribution product is the independent function-major list product. -/
theorem pair_as_list (term : Term (Label Symbol) → Term (Label Symbol) → Term (Label Symbol))
    (left : Finite Symbol α) (right : Finite Symbol β) :
    pair term left right = Decoder.applyValues
      (left.map (fun first second => (first.1 * second.1, pairMember term first.2 second.2))) right := by
  simp [pair, Probability.map, Probability.product, Decoder.applyValues, List.map_flatMap,
    List.flatMap_map, List.map_map, Function.comp_def]

/-- Product cardinality is derived from the input member counts. -/
theorem pair_count (term : Term (Label Symbol) → Term (Label Symbol) → Term (Label Symbol))
    (left : Finite Symbol α) (right : Finite Symbol β) :
    (pair term left right).length = left.length * right.length := by
  rw [pair_as_list, Decoder.length_applyValues, List.length_map]

/-- Product rank selection follows the source quotient/remainder decoder. -/
theorem pair_select (term : Term (Label Symbol) → Term (Label Symbol) → Term (Label Symbol))
    (left : Finite Symbol α) (right : Finite Symbol β) (rank : Nat) :
    select (pair term left right) rank =
      if rank < left.length * right.length then
        (select left (rank / right.length)).bind fun first =>
          (select right (rank % right.length)).map fun second =>
            (first.1 * second.1, pairMember term first.2 second.2)
      else none := by
  rw [select, pair_as_list, Decoder.get_applyValues]
  simp [select, List.getElem?_map, Option.bind_map, Function.comp_def]

/-- Product values have the exact independent product distribution. -/
theorem pair_values (term : Term (Label Symbol) → Term (Label Symbol) → Term (Label Symbol))
    (left : Finite Symbol α) (right : Finite Symbol β) :
    values (pair term left right) = Probability.product (values left) (values right) := by
  simp [values, pair, pairMember, Probability.map, Probability.product,
    List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

/-- Wrap every choice member with its source branch index. -/
def tagBranches (start : Nat) : List (Rat × Finite Symbol Value) → List (Rat × Finite Symbol Value)
  | [] => []
  | (weight, members) :: rest =>
      (weight, Probability.map (fun member => {member with term := .node (.choice start) [member.term]}) members) ::
        tagBranches (start + 1) rest

/-- Weighted branch choice retains each branch's normalized member distribution. -/
def frequency (branches : List (Rat × Finite Symbol Value)) : Finite Symbol Value :=
  Probability.frequency (tagBranches 0 branches)

/-- Branch tags change no decoded-value distribution or branch weight. -/
theorem tagBranches_values (start : Nat) (branches : List (Rat × Finite Symbol Value)) :
    (tagBranches start branches).map (fun branch => (branch.1, values branch.2)) =
      branches.map (fun branch => (branch.1, values branch.2)) := by
  induction branches generalizing start with
  | nil => rfl
  | cons branch rest ih =>
      rcases branch with ⟨weight, members⟩
      simp only [tagBranches, List.map_cons, ih]
      simp [values, Probability.map, List.map_map]

/-- The finite source frequency sampler has exactly the declared branch-weight semantics. -/
theorem frequency_values (branches : List (Rat × Finite Symbol Value)) :
    values (frequency branches) =
      Probability.frequency (branches.map (fun branch => (branch.1, values branch.2))) := by
  unfold frequency values
  rw [Sampler.map_frequency]
  exact congrArg Probability.frequency (tagBranches_values 0 branches)

/-- A member-weighted choice supplies the current cardinality as each branch's weight. -/
def uniformly (branches : List (Finite Symbol Value)) : Finite Symbol Value :=
  frequency (branches.map (fun branch => ((branch.length : Rat), branch)))

/-- Exact value-event mass sums every occurrence, including equal decoded values. -/
def pmfAt (event : Value → Bool) (members : Finite Symbol Value) : Rat := eventMass event (values members)

/-- A binary join term repeats the same private key on both sides. -/
def joinTerm (group : Nat) (left right : Term (Label Symbol)) : Term (Label Symbol) :=
  let key := Term.node (.group group) []
  .node .join [.node .leftKeyed [key, left], .node .rightKeyed [key, right]]

/-- The emitted join key paths always exist and carry identical subterms. -/
theorem joinTerm_keys_equal (group : Nat) (left right : Term (Label Symbol)) :
    PathsEqual (joinTerm group left right) [0, 0] [1, 0] := by
  exact ⟨.node (.group group) [], rfl, rfl⟩

/-- Compare the keys of two nonempty groups. Empty groups have no semantic members. -/
def groupBefore (before : Key → Key → Bool) (key : α → Key) (left right : List α) : Bool :=
  match left, right with
  | first :: _, second :: _ => before (key first) (key second)
  | [], _ => true
  | _, [] => false

/-- Partition in source order within each key, then order buckets by key. -/
def groupOutcomes [DecidableEq Key] (before : Key → Key → Bool) (key : α → Key)
    (members : List α) : List (List α) :=
  (Sized.groups key members).mergeSort (groupBefore before key)

/-- Sorted buckets retain every source occurrence exactly once. -/
theorem groupOutcomes_perm [DecidableEq Key] (before : Key → Key → Bool) (key : α → Key)
    (members : List α) : (groupOutcomes before key members).flatten.Perm members := by
  exact (List.mergeSort_perm _ _).flatten.trans (Sized.groups_perm key members)

/-- Every output bucket is nonempty and homogeneous in its retained key. -/
theorem groupOutcomes_key [DecidableEq Key] (before : Key → Key → Bool) (key : α → Key)
    (members : List α) (group : List α) (present : group ∈ groupOutcomes before key members) :
    ∃ first rest, group = first :: rest ∧ ∀ member, member ∈ group → key member = key first := by
  exact Sized.groups_constant key members group ((List.mergeSort_perm _ _).mem_iff.mp present)

/-- Bucket conditionals retain their original masses when merged. -/
def regroup [DecidableEq Key] (before : Key → Key → Bool) (key : α → Key)
    (members : Distribution α) : Distribution α :=
  Probability.frequency (conditionalBuckets (groupOutcomes before (fun entry => key entry.2) members))

/-- Key grouping and conditional normalization preserve the complete output distribution. -/
theorem regroup_event [DecidableEq Key] (before : Key → Key → Bool) (key : α → Key)
    (members : Distribution α) (event : α → Bool)
    (positive : ∀ entry, entry ∈ members → 0 < entry.1) :
    eventMass event (regroup before key members) = eventMass event (normalize members) := by
  unfold regroup
  rw [regrouping_preserves_distribution]
  · exact normalized_perm_event event (groupOutcomes_perm before _ members)
  · intro group present
    obtain ⟨first, rest, same, _⟩ := groupOutcomes_key before (fun entry => key entry.2) members group present
    have nonempty : group ≠ [] := by simp [same]
    apply Rat.ne_of_gt (Sized.total_positive group nonempty ?_)
    intro entry member
    apply positive entry
    exact (groupOutcomes_perm before (fun entry => key entry.2) members).mem_iff.mp
      (List.mem_flatten.mpr ⟨group, present, member⟩)

/-- Join inputs are sorted by retained size inside each key bucket. -/
def orderBySize (members : Finite Symbol Value) : Finite Symbol Value :=
  members.mergeSort (fun left right => decide (left.2.size ≤ right.2.size))

/-- Sorting a join side preserves every weighted source member. -/
theorem orderBySize_perm (members : Finite Symbol Value) : (orderBySize members).Perm members :=
  List.mergeSort_perm _ _

/-- Sorting every bucket preserves the complete weighted member multiset. -/
theorem orderGroups_perm (groups : List (Finite Symbol Value)) :
    (groups.map orderBySize).flatten.Perm groups.flatten := by
  induction groups with
  | nil => exact .refl _
  | cons group rest ih =>
      exact List.Perm.append (orderBySize_perm group) ih

/-- The source key ordering followed by each bucket's size ordering. -/
def prepareGroups [DecidableEq Key] (before : Key → Key → Bool) (key : Value → Key)
    (members : Finite Symbol Value) : List (Finite Symbol Value) :=
  (groupOutcomes before (fun entry => key entry.2.value) members).map orderBySize

/-- Join preparation retains each source occurrence and its complete weight. -/
theorem prepareGroups_perm [DecidableEq Key] (before : Key → Key → Bool) (key : Value → Key)
    (members : Finite Symbol Value) : (prepareGroups before key members).flatten.Perm members :=
  (orderGroups_perm _).trans (groupOutcomes_perm before _ members)

/-- Splitting every list contribution into two groups changes only order. -/
theorem flatMap_append_perm (items : List α) (first second : α → List β) :
    (items.flatMap (fun item => first item ++ second item)).Perm
      (items.flatMap first ++ items.flatMap second) := by
  induction items with
  | nil => exact .refl _
  | cons item rest ih =>
      simp only [List.flatMap_cons]
      apply (List.Perm.append (List.Perm.refl (first item ++ second item)) ih).trans
      simpa only [List.append_assoc] using
        ((List.perm_append_comm (l₁ := second item) (l₂ := rest.flatMap first)).append_left
          (first item)).append_right (rest.flatMap second)

/-- Reordering a product's left side reorders the same weighted pairs. -/
theorem product_perm_left (right : Distribution β) {first second : Distribution α}
    (same : first.Perm second) : (Probability.product first right).Perm (Probability.product second right) :=
  same.flatMap_right _

/-- Reordering a product's right side reorders the same weighted pairs. -/
theorem product_perm_right (left : Distribution α) {first second : Distribution β}
    (same : first.Perm second) : (Probability.product left first).Perm (Probability.product left second) := by
  induction left with
  | nil => exact .refl _
  | cons entry rest ih => exact List.Perm.append (same.map _) ih

/-- Grouping both product sides preserves weighted pair multiplicity. -/
theorem product_perm {left left' : Distribution α} {right right' : Distribution β}
    (leftSame : left.Perm left') (rightSame : right.Perm right') :
    (Probability.product left right).Perm (Probability.product left' right') :=
  (product_perm_left right leftSame).trans (product_perm_right left' rightSame)

/-- Right-side group boundaries preserve all pairs, but can change their rank order. -/
theorem product_append_right (left : Distribution α) (first second : Distribution β) :
    (Probability.product left (first ++ second)).Perm
      (Probability.product left first ++ Probability.product left second) := by
  simpa [Probability.product, List.map_append] using
    flatMap_append_perm left
      (fun entry => first.map (fun other => (entry.1 * other.1, (entry.2, other.2))))
      (fun entry => second.map (fun other => (entry.1 * other.1, (entry.2, other.2))))

/-- Enumerate products in right-group order without omitting any weighted pair. -/
theorem product_flatten_right (left : Distribution α) (groups : List (Distribution β)) :
    (Probability.product left groups.flatten).Perm (groups.flatMap (Probability.product left)) := by
  induction groups with
  | nil => simp [Probability.product]
  | cons group rest ih =>
      exact (product_append_right left group rest.flatten).trans ((List.Perm.refl _).append ih)

/-- Group-major products in the exact left-key/right-key iteration order. -/
def groupProducts (left : List (Distribution α)) (right : List (Distribution β)) : Distribution (α × β) :=
  left.flatMap fun first => right.flatMap (Probability.product first)

/-- Group-major pair enumeration retains every weighted pair exactly once. -/
theorem groupProducts_perm (left : List (Distribution α)) (right : List (Distribution β)) :
    (groupProducts left right).Perm (Probability.product left.flatten right.flatten) := by
  induction left with
  | nil => exact .refl _
  | cons group rest ih =>
      simpa [groupProducts, Probability.product, List.flatMap_append] using
        (product_flatten_right group right).symm.append ih

/-- Finite keyed joins filter the prepared pair stream and normalize its accepted mass. -/
def join [DecidableEq LeftKey] [DecidableEq RightKey]
    (leftBefore : LeftKey → LeftKey → Bool) (rightBefore : RightKey → RightKey → Bool)
    (leftKey : α → LeftKey) (rightKey : β → RightKey) (relation : LeftKey → RightKey → Bool)
    (left : Finite Symbol α) (right : Finite Symbol β) : Distribution (Member Symbol α × Member Symbol β) :=
  condition (fun pair => relation (leftKey pair.1.value) (rightKey pair.2.value))
    (groupProducts (prepareGroups leftBefore leftKey left) (prepareGroups rightBefore rightKey right))

/-- A finite join's complete weighted pair stream is the original product conditioned on its key relation. -/
theorem join_event [DecidableEq LeftKey] [DecidableEq RightKey]
    (leftBefore : LeftKey → LeftKey → Bool) (rightBefore : RightKey → RightKey → Bool)
    (leftKey : α → LeftKey) (rightKey : β → RightKey) (relation : LeftKey → RightKey → Bool)
    (left : Finite Symbol α) (right : Finite Symbol β)
    (event : Member Symbol α × Member Symbol β → Bool) :
    eventMass event (join leftBefore rightBefore leftKey rightKey relation left right) =
      eventMass event (condition
        (fun pair => relation (leftKey pair.1.value) (rightKey pair.2.value)) (Probability.product left right)) := by
  apply normalized_perm_event
  apply List.Perm.filter
  exact (groupProducts_perm _ _).trans
    (product_perm (prepareGroups_perm leftBefore leftKey left) (prepareGroups_perm rightBefore rightKey right))

/-- A prepared bucket has one key even after its size sort. -/
theorem prepared_key [DecidableEq Key] (before : Key → Key → Bool) (key : Value → Key)
    (members : Finite Symbol Value) (group : Finite Symbol Value)
    (present : group ∈ prepareGroups before key members) :
    ∃ representative, representative ∈ members ∧ ∀ entry, entry ∈ group →
      key entry.2.value = key representative.2.value := by
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
  obtain ⟨first, rest, shape, sameKey⟩ := groupOutcomes_key before
    (fun entry => key entry.2.value) members original member
  have firstMember : first ∈ original := by simp [shape]
  refine ⟨first, ?_, fun entry found => sameKey entry ((orderBySize_perm original).mem_iff.mp found)⟩
  exact (groupOutcomes_perm before _ members).mem_iff.mp (List.mem_flatten.mpr ⟨original, member, firstMember⟩)

/-- Every term in one product of homogeneous buckets has the same key verdict. -/
theorem grouped_relation_constant
    (leftKey : α → LeftKey) (rightKey : β → RightKey) (relation : LeftKey → RightKey → Bool)
    (left : Finite Symbol α) (right : Finite Symbol β) (lk : LeftKey) (rk : RightKey)
    (leftUniform : ∀ entry, entry ∈ left → leftKey entry.2.value = lk)
    (rightUniform : ∀ entry, entry ∈ right → rightKey entry.2.value = rk)
    (entry : Rat × (Member Symbol α × Member Symbol β))
    (present : entry ∈ Probability.product left right) :
    relation (leftKey entry.2.1.value) (rightKey entry.2.2.value) = relation lk rk := by
  obtain ⟨first, hf, second, hs, same⟩ := (by simpa [Probability.product] using present :
    ∃ first, first ∈ left ∧ ∃ second, second ∈ right ∧
      (first.1 * second.1, (first.2, second.2)) = entry)
  subst entry
  simp [leftUniform first hf, rightUniform second hs]

/-- Testing a relation once for homogeneous keys retains exactly the matching member pairs. -/
theorem grouped_relation_filter
    (leftKey : α → LeftKey) (rightKey : β → RightKey) (relation : LeftKey → RightKey → Bool)
    (left : Finite Symbol α) (right : Finite Symbol β) (lk : LeftKey) (rk : RightKey)
    (leftUniform : ∀ entry, entry ∈ left → leftKey entry.2.value = lk)
    (rightUniform : ∀ entry, entry ∈ right → rightKey entry.2.value = rk) :
    restrict (fun pair => relation (leftKey pair.1.value) (rightKey pair.2.value))
      (Probability.product left right) =
        if relation lk rk then Probability.product left right else [] := by
  have constant := grouped_relation_constant leftKey rightKey relation left right lk rk leftUniform rightUniform
  cases verdict : relation lk rk
  · simp only [Bool.false_eq_true, ↓reduceIte, restrict]
    apply List.filter_eq_nil_iff.mpr
    intro entry present
    simp [constant entry present, verdict]
  · simp only [↓reduceIte, restrict]
    apply List.filter_eq_self.mpr
    intro entry present
    simp [constant entry present, verdict]

/-- A finite bucket keeps its original total mass and its conditional members. -/
structure Bucket (Symbol Value : Type) where
  mass : Rat
  members : Finite Symbol Value

/-- `bucketFromOutcomes` uses a size-one select plan for its conditional members. -/
def bucketFromOutcomes (members : Finite Symbol Value) : Bucket Symbol Value :=
  ⟨total members, atomic (normalize members)⟩

/-- Bucket construction retains every replay position. -/
theorem bucket_count (members : Finite Symbol Value) :
    (bucketFromOutcomes members).members.length = members.length := by
  simp [bucketFromOutcomes, atomic, normalize, scale, Probability.map]

/-- Bucket members use the size-one plan even if the input came from a larger plan. -/
theorem bucket_size (members : Finite Symbol Value) (entry : Rat × Member Symbol Value)
    (present : entry ∈ (bucketFromOutcomes members).members) : entry.2.size = 1 := by
  obtain ⟨old, _, same⟩ := List.mem_map.mp present
  subst entry
  rfl

/-- Restoring the original bucket mass restores all original output masses. -/
theorem bucket_restore_values (members : Finite Symbol Value) (nonzero : total members ≠ 0) :
    values (scale (bucketFromOutcomes members).mass (bucketFromOutcomes members).members) =
      values members := by
  change values (scale (total members) (atomic (normalize members))) = _
  have commute : ∀ (factor : Rat) (dist : Finite Symbol Value),
      scale factor (atomic dist) = atomic (scale factor dist) := by
    intro factor dist
    simp [scale, atomic, Probability.map, List.map_map]
  rw [commute, restore_normalized members nonzero, atomic_values]

/-- A missing size-mass table falls back to member counts, as in `bucketMassIndex`. -/
def bucketMassIndex (members : Finite Symbol Value) (retained : Option (Nat → Rat)) (size : Nat) : Rat :=
  match retained with
  | some mass => mass size
  | none => (members.countP (fun entry => entry.2.size == size) : Rat)

/-- Explicit retained masses override structural member counts. -/
theorem bucketMassIndex_retained (members : Finite Symbol Value) (mass : Nat → Rat) (size : Nat) :
    bucketMassIndex members (some mass) size = mass size := rfl

/-- Missing retained masses use counts without inspecting outcome probabilities. -/
theorem bucketMassIndex_missing (members : Finite Symbol Value) (size : Nat) :
    bucketMassIndex members none size = (members.countP (fun entry => entry.2.size == size) : Rat) := rfl

/-- The finite source's enumerated inverse retains every matching rank. -/
def enumeratedRanks (matchesView : Term (Label Symbol) → Bool) (members : Finite Symbol Value) : List Nat :=
  (List.range members.length).filter fun rank =>
    ((select members rank).map (fun entry => matchesView entry.2.term)).getD false

/-- Enumerated inverse queries are complete and sound for their supplied term-view predicate. -/
theorem enumeratedRanks_exact (matchesView : Term (Label Symbol) → Bool)
    (members : Finite Symbol Value) (rank : Nat) :
    rank ∈ enumeratedRanks matchesView members ↔
      ∃ entry, select members rank = some entry ∧ matchesView entry.2.term = true := by
  simp only [enumeratedRanks, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨bound, accepted⟩
    have selected : select members rank = some members[rank] := List.getElem?_eq_getElem bound
    exact ⟨members[rank], selected, by simpa [selected] using accepted⟩
  · rintro ⟨entry, selected, accepted⟩
    refine ⟨?_, by simp [selected, accepted]⟩
    exact List.getElem?_eq_some_iff.mp selected |>.1

/-- Enumerated inverse queries never repeat a replay rank. -/
theorem enumeratedRanks_nodup (matchesView : Term (Label Symbol) → Bool) (members : Finite Symbol Value) :
    (enumeratedRanks matchesView members).Nodup := List.nodup_range.filter _

/-- Distinct member counts, rather than equal branch shares, determine `uniformly`. -/
theorem uniformly_value_mass :
    pmfAt (· == 0) (uniformly (Symbol := Unit) [indexed [0], indexed [1, 2]]) = 1 / 3 ∧
    pmfAt (· == 0) (frequency (Symbol := Unit) [(1, indexed [0]), (1, indexed [1, 2])]) = 1 / 2 := by
  decide +kernel

/-- Count-weighted branch choice still retains the internal unequal probabilities of a branch. -/
theorem uniformly_keeps_branch_weights :
    let weighted : Finite Unit Nat := [(1/4, ⟨.node (.index 0) [], 0, 1⟩),
      (3/4, ⟨.node (.index 1) [], 1, 1⟩)]
    pmfAt (· == 0) (uniformly [weighted, indexed [2]]) = 1 / 6 := by
  decide +kernel

end MicroCFTA.GeneratorCombinators
