import MicroCFTA.Language
import MicroCFTA.Probability

/-!
# Size annotations and observed source reconstruction

A label changes a term but does not add a source choice. An atomic boundary
sets the size to one. A product adds its source sizes. These are the rules of
`Ranked.Internal.Size`, `labelStatic`, and `atomicStatic`.

`rebuildObserved` models the top-level atomic check added to `groupBuilt` in
commit `ae6b97b`. `rebuildRetained` is a reference repair which also retains
arbitrary source sizes. The latter is not implemented by that commit.
-/

namespace MicroCFTA.Sized

open Language Probability

/-- The structure of one finite source member. -/
inductive Source (Symbol : Type) where
  | unit : Source Symbol
  | product : Source Symbol → Source Symbol → Source Symbol
  | label : Symbol → Source Symbol → Source Symbol
  | choice : Source Symbol → Source Symbol
  | atomic : Source Symbol → Source Symbol
  | retained : Nat → List (Term Symbol) → Source Symbol

/-- The user term forest, after private product nodes are removed. -/
def surface : Source Symbol → List (Term Symbol)
  | .unit => []
  | .product left right => surface left ++ surface right
  | .label symbol child => [.node symbol (surface child)]
  | .choice child => surface child
  | .atomic child => surface child
  | .retained _ forest => forest

/-- A member's number of source choices. -/
def size : Source Symbol → Nat
  | .unit => 1
  | .product left right => size left + size right
  | .label _ child => size child
  | .choice child => size child
  | .atomic _ => 1
  | .retained count _ => count

/-- The top-level atomic marker survives relabelling but not a product. -/
def topAtomic : Source Symbol → Bool
  | .unit => false
  | .product _ _ => false
  | .label _ child => topAtomic child
  | .choice _ => false
  | .atomic _ => true
  | .retained _ _ => false

/-- A marked atomic source has size one, including after relabelling. -/
theorem atomic_size_one (source : Source Symbol) (h : topAtomic source = true) :
    size source = 1 := by
  induction source with
  | unit => simp [topAtomic] at h
  | product _ _ _ _ => simp [topAtomic] at h
  | label _ child ih => exact ih h
  | choice _ _ => simp [topAtomic] at h
  | atomic _ _ => rfl
  | retained _ _ => simp [topAtomic] at h

mutual
  /-- Rebuild a term from one source choice and its rebuilt children. -/
  def rebuildTree : Term Symbol → Source Symbol
    | .node symbol children => .label symbol (rebuildForest children)

  /-- Rebuild a forest with one initial source choice, as `withChildren` does. -/
  def rebuildForest : List (Term Symbol) → Source Symbol
    | [] => .unit
    | tree :: rest => .product (rebuildTree tree) (rebuildForest rest)
end

/-- Rebuilding a tree preserves every symbol and child position. -/
theorem surface_rebuildTree (tree : Term Symbol) :
    surface (rebuildTree tree) = [tree] := by
  induction tree using Term.rec
    (motive_2 := fun forest => surface (rebuildForest forest) = forest) with
  | node symbol children ih => simp [rebuildTree, surface, ih]
  | nil => rfl
  | cons tree rest it ir => simp [rebuildForest, surface, it, ir]

/-- Rebuilding a forest preserves its full list of terms. -/
theorem surface_rebuildForest (forest : List (Term Symbol)) :
    surface (rebuildForest forest) = forest := by
  induction forest with
  | nil => rfl
  | cons tree rest ih => simp [rebuildForest, surface, surface_rebuildTree, ih]

/-- Rebuild a single root directly; otherwise rebuild an applicative forest. -/
def rebuild (forest : List (Term Symbol)) : Source Symbol :=
  match forest with
  | [tree] => rebuildTree tree
  | forest => rebuildForest forest

/-- Both reconstruction branches preserve the original term forest. -/
theorem surface_rebuild (forest : List (Term Symbol)) : surface (rebuild forest) = forest := by
  cases forest with
  | nil => rfl
  | cons tree rest =>
      cases rest with
      | nil => exact surface_rebuildTree tree
      | cons second rest => exact surface_rebuildForest _

/-- The reconstruction implemented by the top-level atomic fix. -/
def rebuildObserved (source : Source Symbol) : Source Symbol :=
  if topAtomic source then .atomic (rebuild (surface source)) else rebuild (surface source)

/-- The fixed reconstruction preserves terms for every source. -/
theorem rebuildObserved_terms (source : Source Symbol) :
    surface (rebuildObserved source) = surface source := by
  unfold rebuildObserved
  split <;> simp [surface, surface_rebuild]

/-- The fixed reconstruction preserves sizes for top-level atomic sources. -/
theorem rebuildObserved_atomic_size (source : Source Symbol) (h : topAtomic source = true) :
    size (rebuildObserved source) = size source := by
  simp [rebuildObserved, h, size, atomic_size_one source h]

/-- A non-atomic source keeps its size only when structural reconstruction has that size. -/
theorem rebuildObserved_nonatomic_size (source : Source Symbol) (h : topAtomic source = false) :
    size (rebuildObserved source) = size source ↔ size (rebuild (surface source)) = size source := by
  simp [rebuildObserved, h]

/-- Retain the source size while rebuilding its term structure.
The retained constructor models a singleton `PlanSized` entry. -/
def rebuildRetained (source : Source Symbol) : Source Symbol :=
  .retained (size source) (surface (rebuild (surface source)))

/-- Retaining the annotation preserves both term structure and exact size. -/
theorem rebuildRetained_correct (source : Source Symbol) :
    surface (rebuildRetained source) = surface source ∧ size (rebuildRetained source) = size source := by
  simp [rebuildRetained, surface, size, surface_rebuild]

/-- One decoded member, its construction, and its exact sampling mass. -/
structure Member (Symbol Value : Type) where
  source : Source Symbol
  value : Value
  mass : Rat

/-- The observations that size restriction and value-level probabilities use. -/
structure Annotation (Symbol Value : Type) where
  forest : List (Term Symbol)
  size : Nat
  value : Value

/-- Read the complete observable annotation of a member. -/
def annotation (member : Member Symbol Value) : Annotation Symbol Value :=
  ⟨surface member.source, size member.source, member.value⟩

/-- Rebuild each member with its original size, value, and mass. -/
def rebuildMember (member : Member Symbol Value) : Member Symbol Value :=
  {member with source := rebuildRetained member.source}

/-- The reference repair preserves the complete annotation and mass of each member. -/
theorem rebuildMember_correct (member : Member Symbol Value) :
    annotation (rebuildMember member) = annotation member ∧
      (rebuildMember member).mass = member.mass := by
  obtain ⟨ht, hs⟩ := rebuildRetained_correct member.source
  simp [rebuildMember, annotation, ht, hs]

/-- Rebuild a member with the currently implemented top-level atomic check. -/
def rebuildObservedMember (member : Member Symbol Value) : Member Symbol Value :=
  {member with source := rebuildObserved member.source}

/-- The current patch preserves complete annotations of top-level atomic members. -/
theorem rebuildObservedMember_atomic (member : Member Symbol Value)
    (h : topAtomic member.source = true) :
    annotation (rebuildObservedMember member) = annotation member := by
  simp [annotation, rebuildObservedMember, rebuildObserved_terms,
    rebuildObserved_atomic_size member.source h]

/-- Retain one finite distribution entry per source rank. -/
def distribution (members : List (Member Symbol Value)) : Distribution (Annotation Symbol Value) :=
  members.map fun member => (member.mass, annotation member)

/-- Rebuilding all members preserves the exact annotated distribution. -/
theorem rebuild_distribution (members : List (Member Symbol Value)) :
    distribution (members.map rebuildMember) = distribution members := by
  simp only [distribution, List.map_map]
  apply List.map_congr_left
  intro member _
  obtain ⟨ha, hm⟩ := rebuildMember_correct member
  simp [ha, hm]

/-- The current patch preserves the exact distribution of an atomic source. -/
theorem rebuildObserved_distribution_atomic (members : List (Member Symbol Value))
    (h : ∀ member ∈ members, topAtomic member.source = true) :
    distribution (members.map rebuildObservedMember) = distribution members := by
  simp only [distribution, List.map_map]
  apply List.map_congr_left
  intro member hm
  simp only [Function.comp_def]
  rw [rebuildObservedMember_atomic member (h member hm)]
  rfl

/-- Every size-conditioned event probability is preserved for a top-level atomic source. -/
theorem rebuildObserved_conditioned_atomic (members : List (Member Symbol Value))
    (h : ∀ member ∈ members, topAtomic member.source = true)
    (sizeEvent : Nat → Bool) (event : Annotation Symbol Value → Bool) :
    eventMass event (condition (fun member => sizeEvent member.size)
      (distribution (members.map rebuildObservedMember))) =
      eventMass event (condition (fun member => sizeEvent member.size) (distribution members)) := by
  rw [rebuildObserved_distribution_atomic members h]

/-- Keep members within a source-choice size bound. -/
def bounded (bound : Nat) (members : List (Member Symbol Value)) : List (Member Symbol Value) :=
  members.filter fun member => decide (size member.source ≤ bound)

/-- Rebuilding commutes with size restriction. No member crosses the bound. -/
theorem rebuild_bounded (bound : Nat) (members : List (Member Symbol Value)) :
    bounded bound (members.map rebuildMember) = (bounded bound members).map rebuildMember := by
  simp only [bounded, List.filter_map]
  rfl

/-- Size-bounded cardinalities are preserved, including duplicate values. -/
theorem rebuild_bounded_cardinality (bound : Nat) (members : List (Member Symbol Value)) :
    (bounded bound (members.map rebuildMember)).length = (bounded bound members).length := by
  rw [rebuild_bounded, List.length_map]

/-- The probability of every size-bounded event is preserved. -/
theorem rebuild_bounded_probability (bound : Nat) (members : List (Member Symbol Value))
    (event : Annotation Symbol Value → Bool) :
    eventMass event (normalize (distribution (bounded bound (members.map rebuildMember)))) =
      eventMass event (normalize (distribution (bounded bound members))) := by
  rw [rebuild_bounded, rebuild_distribution]

/-- The source-size relation used by strictly smaller-member queries. -/
abbrev Smaller (left right : Member Symbol Value) : Prop := size left.source < size right.source

/-- Retaining source annotations preserves the strict size order in both directions. -/
theorem rebuild_smaller_iff (left right : Member Symbol Value) :
    Smaller (rebuildMember left) (rebuildMember right) ↔ Smaller left right := by
  rfl

/-- Partition finite members by the first occurrence of each observation key. -/
def groups [DecidableEq Key] (key : α → Key) (members : List α) : List (List α) :=
  match members with
  | [] => []
  | member :: rest =>
      (member :: rest.filter (fun other => decide (key other = key member))) ::
        groups key (rest.filter (fun other => decide (key other ≠ key member)))
termination_by members.length
decreasing_by
  simp only [List.length_unattach]
  apply Nat.lt_of_le_of_lt (List.length_filter_le _ _)
  simp

/-- The executable partition retains every source occurrence exactly once. -/
theorem groups_perm [DecidableEq Key] (key : α → Key) (members : List α) :
    (groups key members).flatten.Perm members := by
  induction members using groups.induct key with
  | case1 => simp [groups]
  | case2 member rest ih =>
      rw [List.unattach_filter (g := fun other => decide (key other ≠ key member))
        (hf := fun _ _ => rfl), List.unattach_attach] at ih
      rw [groups]
      simp only [List.flatten_cons, List.cons_append]
      apply List.Perm.cons
      have heq : (rest.filter (fun other => decide (key other ≠ key member))) =
          rest.filter (fun other => !decide (key other = key member)) := by simp
      have hp := List.Perm.append
        (List.Perm.refl (rest.filter (fun other => decide (key other = key member)))) ih
      exact hp.trans (by rw [heq]; exact List.filter_append_perm _ rest)

/-- Every partition group has a representative and one observation key. -/
theorem groups_constant [DecidableEq Key] (key : α → Key) (members : List α) :
    ∀ group ∈ groups key members, ∃ first rest, group = first :: rest ∧
      ∀ member ∈ group, key member = key first := by
  induction members using groups.induct key with
  | case1 => simp [groups]
  | case2 first rest ih =>
      rw [List.unattach_filter (g := fun other => decide (key other ≠ key first))
        (hf := fun _ _ => rfl), List.unattach_attach] at ih
      intro group hg
      rw [groups] at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · refine ⟨first, _, rfl, ?_⟩
        intro member hm
        rcases List.mem_cons.mp hm with rfl | hm
        · rfl
        · exact of_decide_eq_true (List.mem_filter.mp hm).2
      · exact ih group hg

/-- Rebuild members, then partition them by a finite observation. -/
def rebuildGrouped [DecidableEq Key] (key : Member Symbol Value → Key)
    (members : List (Member Symbol Value)) : List (Member Symbol Value) :=
  (groups key (members.map rebuildMember)).flatten

/-- A nonempty list of positive run masses has positive total mass. -/
theorem total_positive (dist : Distribution α) (hn : dist ≠ [])
    (hp : ∀ entry ∈ dist, 0 < entry.1) : 0 < total dist := by
  cases dist with
  | nil => contradiction
  | cons entry rest =>
      rcases entry with ⟨mass, value⟩
      have hm : 0 < mass := hp (mass, value) (by simp)
      have hr : 0 ≤ total rest := total_nonnegative rest
        (fun entry he => Rat.le_of_lt (hp entry (List.mem_cons_of_mem _ he)))
      change 0 < mass + total rest
      grind

/-- The concrete key partition and conditional bucket algorithm preserve every event mass. -/
theorem partition_conditional_probability [DecidableEq Key]
    (key : Rat × α → Key) (dist : Distribution α)
    (hp : ∀ entry ∈ dist, 0 < entry.1) (event : α → Bool) :
    eventMass event (frequency (conditionalBuckets (groups key dist))) =
      eventMass event (normalize dist) := by
  have hg : ∀ group ∈ groups key dist, total group ≠ 0 := by
    intro group hm
    obtain ⟨first, rest, heq, _⟩ := groups_constant key dist group hm
    apply Rat.ne_of_gt
    apply total_positive group
    · simp [heq]
    · intro entry he
      exact hp entry ((groups_perm key dist).mem_iff.mp (List.mem_flatten.mpr ⟨group, hm, he⟩))
  rw [regrouping_preserves_distribution _ hg]
  exact normalized_perm_event event (groups_perm key dist)

/-- Grouping changes order but does not change any retained member occurrence. -/
theorem rebuildGrouped_perm [DecidableEq Key] (key : Member Symbol Value → Key)
    (members : List (Member Symbol Value)) :
    (rebuildGrouped key members).Perm (members.map rebuildMember) := by
  exact groups_perm key _

/-- Annotation retention and partitioning preserve the full distribution up to order. -/
theorem rebuildGrouped_distribution [DecidableEq Key]
    (key : Member Symbol Value → Key) (members : List (Member Symbol Value)) :
    (distribution (rebuildGrouped key members)).Perm (distribution members) := by
  have hp := (rebuildGrouped_perm key members).map (fun member => (member.mass, annotation member))
  change (distribution (rebuildGrouped key members)).Perm (distribution (members.map rebuildMember)) at hp
  rwa [rebuild_distribution] at hp

/-- Every condition on source sizes gives the same output probabilities after rebuilding and grouping. -/
theorem rebuildGrouped_conditioned_probability [DecidableEq Key]
    (key : Member Symbol Value → Key) (members : List (Member Symbol Value))
    (sizeEvent : Nat → Bool) (event : Annotation Symbol Value → Bool) :
    eventMass event (condition (fun entry => sizeEvent entry.size)
      (distribution (rebuildGrouped key members))) =
    eventMass event (condition (fun entry => sizeEvent entry.size) (distribution members)) := by
  simp only [eventMass_condition]
  rw [eventMass_perm _ (rebuildGrouped_distribution key members),
    eventMass_perm _ (rebuildGrouped_distribution key members)]

/-- The count of every exact size class is preserved. -/
theorem rebuildGrouped_exact_size_count [DecidableEq Key]
    (key : Member Symbol Value → Key) (members : List (Member Symbol Value)) (wantedSize : Nat) :
    (rebuildGrouped key members).countP (fun member => size member.source == wantedSize) =
      members.countP (fun member => size member.source == wantedSize) := by
  rw [(rebuildGrouped_perm key members).countP_eq,
    List.countP_map]
  rfl

/-- Bounded grouping preserves the annotated distribution up to ordering. -/
theorem rebuildGrouped_bounded_distribution [DecidableEq Key]
    (key : Member Symbol Value → Key) (bound : Nat) (members : List (Member Symbol Value)) :
    (distribution (bounded bound (rebuildGrouped key members))).Perm
      (distribution (bounded bound members)) := by
  have hp := (rebuildGrouped_perm key members).filter
    (fun member => decide (size member.source ≤ bound))
  have hq := hp.map (fun member => (member.mass, annotation member))
  change (distribution (bounded bound (rebuildGrouped key members))).Perm
    (distribution (bounded bound (members.map rebuildMember))) at hq
  rwa [rebuild_bounded, rebuild_distribution] at hq

/-- Grouping and annotation retention preserve every bounded event probability. -/
theorem rebuildGrouped_bounded_probability [DecidableEq Key]
    (key : Member Symbol Value → Key) (bound : Nat) (members : List (Member Symbol Value))
    (event : Annotation Symbol Value → Bool) :
    eventMass event (normalize (distribution (bounded bound (rebuildGrouped key members)))) =
      eventMass event (normalize (distribution (bounded bound members))) := by
  exact normalized_perm_event event (rebuildGrouped_bounded_distribution key bound members)

/-- Grouping and annotation retention preserve every bounded cardinality. -/
theorem rebuildGrouped_bounded_cardinality [DecidableEq Key]
    (key : Member Symbol Value → Key) (bound : Nat) (members : List (Member Symbol Value)) :
    (bounded bound (rebuildGrouped key members)).length = (bounded bound members).length := by
  have hp := (rebuildGrouped_perm key members).filter
    (fun member => decide (size member.source ≤ bound))
  change (bounded bound (rebuildGrouped key members)).Perm
    (bounded bound (members.map rebuildMember)) at hp
  rw [hp.length_eq, rebuild_bounded_cardinality]

/-- Select every occurrence strictly smaller than the supplied member. -/
def smallerMembers (target : Member Symbol Value) (members : List (Member Symbol Value)) :
    List (Member Symbol Value) := members.filter fun member => decide (Smaller member target)

/-- Rebuilding preserves the complete list of strictly smaller members. -/
theorem rebuild_smallerMembers (target : Member Symbol Value) (members : List (Member Symbol Value)) :
    smallerMembers (rebuildMember target) (members.map rebuildMember) =
      (smallerMembers target members).map rebuildMember := by
  simp only [smallerMembers, List.filter_map]
  rfl

/-- Partitioning preserves the annotated multiset of strictly smaller members. -/
theorem rebuildGrouped_smallerMembers [DecidableEq Key]
    (key : Member Symbol Value → Key) (target : Member Symbol Value)
    (members : List (Member Symbol Value)) :
    (distribution (smallerMembers (rebuildMember target) (rebuildGrouped key members))).Perm
      (distribution (smallerMembers target members)) := by
  have hp := (rebuildGrouped_perm key members).filter
    (fun member => decide (Smaller member (rebuildMember target)))
  have hq := hp.map (fun member => (member.mass, annotation member))
  change (distribution (smallerMembers (rebuildMember target) (rebuildGrouped key members))).Perm
    (distribution (smallerMembers (rebuildMember target) (members.map rebuildMember))) at hq
  rwa [rebuild_smallerMembers, rebuild_distribution] at hq

/-- Reconstructing a non-atomic labelled source can change its size. -/
def plainWrapped : Source Bool := .label true (.label false .unit)

/-- Even without an atomic child, source-choice size need not equal tree-node count. -/
theorem plain_reconstruction_counterexample :
    topAtomic plainWrapped = false ∧ size plainWrapped = 1 ∧
      size (rebuildObserved plainWrapped) = 2 := by decide +kernel

/-- A product can contain an atomic boundary while its own marker is false. -/
def nestedAtomic : Source Bool :=
  .label true (.product (.atomic (.label false (.label true .unit))) (.label false .unit))

/-- A top-level marker cannot recover an atomic boundary inside a product. -/
theorem nested_atomic_reconstruction_counterexample :
    topAtomic nestedAtomic = false ∧ size nestedAtomic = 2 ∧
      size (rebuildObserved nestedAtomic) = 4 := by decide +kernel

end MicroCFTA.Sized
