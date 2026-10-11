import MicroCFTA.DistinctRank

/-!
# First-deepest-child enumeration

`Internal.Tree.deepestTerms` fixes the first child at the current depth.
Earlier children come from the shallower table. Later children come from the
at-most table. This avoids listing the same child tuple at several pivots.
The tables below are total functions; absent map keys mean empty languages.
-/

namespace MicroCFTA.LevelEnumeration
open Language

/-- The general source worker, including its loop nesting and empty-child case. -/
def childLists (current atMost shallower : State → List α) : List State → List (List α)
  | [] => []
  | q :: qs =>
      (current q).flatMap (fun child => (products atMost qs).map (child :: ·)) ++
      (childLists current atMost shallower qs).flatMap
        (fun rest => (shallower q).map (· :: rest))

/-- Some child has the current depth. -/
def Reaches (height : α → Nat) (depth : Nat) (children : List α) : Prop :=
  ∃ child ∈ children, height child = depth

/-- The first-deepest split contains exactly all bounded tuples that reach this depth. -/
theorem childLists_exact (current atMost shallower : State → List α)
    (allowed : State → α → Prop) (height : α → Nat) (depth : Nat)
    (cur : ∀ q t, t ∈ current q ↔ allowed q t ∧ height t = depth)
    (upto : ∀ q t, t ∈ atMost q ↔ allowed q t ∧ height t ≤ depth)
    (below : ∀ q t, t ∈ shallower q ↔ allowed q t ∧ height t < depth)
    (keys : List State) (children : List α) :
    children ∈ childLists current atMost shallower keys ↔
      All₂ (fun q t => allowed q t ∧ height t ≤ depth) keys children ∧
        Reaches height depth children := by
  induction keys generalizing children with
  | nil =>
      constructor
      · simp [childLists]
      · rintro ⟨hs, hd⟩
        cases hs
        simp [Reaches] at hd
  | cons q qs ih =>
      constructor
      · intro found
        rcases List.mem_append.mp found with first | later
        · obtain ⟨a, ha, rest, hr, rfl⟩ :=
            (by simpa only [List.mem_flatMap, List.mem_map] using first :
              ∃ a ∈ current q, ∃ rest ∈ products atMost qs, a :: rest = children)
          have aok := (cur q a).mp ha
          have restok := (mem_products atMost qs rest).mp hr
          exact ⟨.cons ⟨aok.1, by omega⟩ (All₂.imp (fun q t h => (upto q t).mp h) restok),
            ⟨a, by simp, aok.2⟩⟩
        · obtain ⟨rest, hr, a, ha, rfl⟩ :=
            (by simpa only [List.mem_flatMap, List.mem_map] using later :
              ∃ rest ∈ childLists current atMost shallower qs, ∃ a ∈ shallower q, a :: rest = children)
          have aok := (below q a).mp ha
          obtain ⟨restok, witness, member, reaches⟩ := ih rest |>.mp hr
          exact ⟨.cons ⟨aok.1, by omega⟩ restok, ⟨witness, by simp [member], reaches⟩⟩
      · rintro ⟨accepted, reaches⟩
        cases accepted with
        | cons aok restok =>
          rename_i a rest
          by_cases atDepth : height a = depth
          · apply List.mem_append.mpr; left
            exact List.mem_flatMap.mpr ⟨a, (cur q a).mpr ⟨aok.1, atDepth⟩,
              List.mem_map.mpr ⟨rest, (mem_products atMost qs rest).mpr
                (All₂.imp (fun q t h => (upto q t).mpr h) restok), rfl⟩⟩
          · have tailReaches : Reaches height depth rest := by
              obtain ⟨witness, member, eq⟩ := reaches
              rcases List.mem_cons.mp member with same | inside
              · subst witness; exact False.elim (atDepth eq)
              · exact ⟨witness, inside, eq⟩
            apply List.mem_append.mpr; right
            exact List.mem_flatMap.mpr ⟨rest, (ih rest).mpr ⟨restok, tailReaches⟩,
              List.mem_map.mpr ⟨a, (below q a).mpr ⟨aok.1, by omega⟩, rfl⟩⟩

/-- Bounding each child bounds the maximum height. -/
theorem forestHeight_le (ts : List (Term Symbol)) (depth : Nat)
    (bound : ∀ t ∈ ts, t.height ≤ depth) : forestHeight ts ≤ depth := by
  induction ts with
  | nil => exact Nat.zero_le _
  | cons t ts ih =>
      exact Nat.max_le.mpr ⟨bound t (by simp), ih (fun u hu => bound u (by simp [hu]))⟩

/-- Maximum child height equals the depth precisely when a bounded child reaches it. -/
theorem forestHeight_exact (ts : List (Term Symbol)) (depth : Nat)
    (positive : 0 < depth) :
    forestHeight ts = depth ↔
      (∀ t ∈ ts, t.height ≤ depth) ∧ Reaches Term.height depth ts := by
  induction ts with
  | nil => simp [forestHeight, Reaches]; omega
  | cons t ts ih =>
      change max t.height (forestHeight ts) = depth ↔ _
      constructor
      · intro eq
        have limits : t.height ≤ depth ∧ forestHeight ts ≤ depth := by omega
        refine ⟨?_, ?_⟩
        · intro u member
          rcases List.mem_cons.mp member with rfl | member
          · exact limits.1
          · exact Nat.le_trans (height_le_forestHeight ts u member) limits.2
        · by_cases head : t.height = depth
          · exact ⟨t, by simp, head⟩
          · have tail : forestHeight ts = depth := by omega
            obtain ⟨u, member, same⟩ := (ih.mp tail).2
            exact ⟨u, by simp [member], same⟩
      · rintro ⟨limits, u, member, same⟩
        have bounded := forestHeight_le ts depth (fun u hu => limits u (by simp [hu]))
        have upper := limits t (by simp)
        have lower := height_le_forestHeight (t :: ts) u member
        change u.height ≤ max t.height (forestHeight ts) at lower
        omega

/-- The specialized one-child branch is the general worker. -/
theorem unary_dispatch (current atMost shallower : State → List α) (q : State) :
    childLists current atMost shallower [q] = (current q).map (fun t => [t]) := by
  simp [childLists, products, ← List.map_eq_flatMap]

/-- The two-child branch keeps exactly the source loop order. -/
theorem binary_dispatch (current atMost shallower : State → List α) (q r : State) :
    childLists current atMost shallower [q,r] =
      (current q).flatMap (fun a => (atMost r).map (fun b => [a,b])) ++
      (current r).flatMap (fun b => (shallower q).map (fun a => [a,b])) := by
  simp [childLists, products, ← List.map_eq_flatMap, List.flatMap_map, Function.comp_def]

/-- The exact-depth table obtained from the checked bounded language. -/
def current (A : Automaton State Symbol) (depth : Nat) (q : State) : List (Term Symbol) :=
  (enumerate A depth q).filter (fun t => decide (t.height = depth))

/-- The first-deepest source worker preserves exactly the accepted child tuples at this depth. -/
theorem accepted_children_exact (A : Automaton State Symbol) (depth : Nat)
    (positive : 0 < depth) (keys : List State) (ts : List (Term Symbol)) :
    ts ∈ childLists (current A depth) (enumerate A depth) (enumerate A (depth - 1)) keys ↔
      All₂ (Accepts A) keys ts ∧ forestHeight ts = depth := by
  have split := childLists_exact (current A depth) (enumerate A depth) (enumerate A (depth - 1))
    (Accepts A) Term.height depth
    (by intro q t; simp [current, mem_enumerate_iff]; omega)
    (by intro q t; exact mem_enumerate_iff A depth q t)
    (by
      intro q t
      rw [mem_enumerate_iff]
      constructor
      · rintro ⟨ha, hh⟩; exact ⟨ha, by omega⟩
      · rintro ⟨ha, hh⟩; exact ⟨ha, by omega⟩) keys ts
  rw [split, all₂_height_iff]
  constructor
  · rintro ⟨⟨accepted, bounded⟩, reaches⟩
    exact ⟨accepted, (forestHeight_exact ts depth positive).mpr
      ⟨fun t member => Nat.le_trans (height_le_forestHeight ts t member) bounded, reaches⟩⟩
  · rintro ⟨accepted, height⟩
    exact ⟨⟨accepted, by omega⟩, ((forestHeight_exact ts depth positive).mp height).2⟩

/-- Build and check precisely one non-leaf level, using the source split algorithm. -/
def deeper (A : Automaton State Symbol) (depth : Nat) (q : State) : List (Term Symbol) :=
  (A q).flatMap fun edge =>
    ((childLists (current A depth) (enumerate A depth) (enumerate A (depth - 1)) edge.children).map
      (Term.node edge.label)).filter edge.guard

/-- The optimized level constructor loses no accepted term and adds no invalid term. -/
theorem deeper_exact (A : Automaton State Symbol) (depth : Nat) (positive : 0 < depth)
    (q : State) (t : Term Symbol) :
    t ∈ deeper A depth q ↔ Accepts A q t ∧ t.height = depth + 1 := by
  constructor
  · intro member
    obtain ⟨edge, present, built⟩ := List.mem_flatMap.mp member
    obtain ⟨built, guarded⟩ := List.mem_filter.mp built
    obtain ⟨ts, selected, same⟩ := List.mem_map.mp built
    subst t
    obtain ⟨accepted, height⟩ := (accepted_children_exact A depth positive edge.children ts).mp selected
    refine ⟨Accepts.node edge ts present accepted guarded, ?_⟩
    simpa only [Term.height, forestHeight] using congrArg (· + 1) height
  · rintro ⟨accepted, height⟩
    cases accepted with
    | node edge ts present children guarded =>
      have h : forestHeight ts = depth := by
        have height : forestHeight ts + 1 = depth + 1 := by
          simpa [Term.height, forestHeight] using height
        omega
      exact List.mem_flatMap.mpr ⟨edge, present,
        List.mem_filter.mpr ⟨List.mem_map.mpr ⟨ts,
          (accepted_children_exact A depth positive edge.children ts).mpr ⟨children, h⟩, rfl⟩, guarded⟩⟩

/-- An empty current table makes every first-deepest product empty. -/
theorem childLists_empty (current atMost shallower : State → List α)
    (empty : ∀ q, current q = []) (keys : List State) :
    childLists current atMost shallower keys = [] := by
  induction keys with
  | nil => rfl
  | cons q qs ih => simp [childLists, empty q, ih]

/-- If no state has a term at one positive height, the next level is empty too. -/
theorem empty_next (A : Automaton State Symbol) (depth : Nat) (positive : 0 < depth)
    (empty : ∀ q, current A depth q = []) : ∀ q, current A (depth + 1) q = [] := by
  intro q
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro t member
  obtain ⟨listed, height⟩ := List.mem_filter.mp member
  have accepted := ((mem_enumerate_iff A (depth + 1) q t).mp listed).1
  have height : t.height = depth + 1 := of_decide_eq_true height
  have next := (deeper_exact A depth positive q t).mpr ⟨accepted, height⟩
  have worker := childLists_empty (current A depth) (enumerate A depth) (enumerate A (depth - 1)) empty
  simp [deeper, worker] at next

/-- The source's global empty-level stopping condition cannot omit a later level. -/
theorem empty_later (A : Automaton State Symbol) (depth : Nat) (positive : 0 < depth)
    (empty : ∀ q, current A depth q = []) (later : Nat) :
    ∀ q, current A (depth + later) q = [] := by
  induction later with
  | zero => simpa using empty
  | succ later ih => exact empty_next A (depth + later) (by omega) ih

/-- No accepted term lies beyond the first globally empty positive level. -/
theorem stop_complete (A : Automaton State Symbol) (depth : Nat) (positive : 0 < depth)
    (empty : ∀ q, current A depth q = []) (q : State) (t : Term Symbol)
    (accepted : Accepts A q t) : t.height < depth := by
  by_cases above : t.height < depth
  · exact above
  apply False.elim
  have bound : depth ≤ t.height := by omega
  have nil := empty_later A depth positive empty (t.height - depth) q
  have same : depth + (t.height - depth) = t.height := by omega
  rw [same] at nil
  have member : t ∈ current A t.height q := by
    apply List.mem_filter.mpr
    exact ⟨(mem_enumerate_iff A t.height q t).mpr ⟨accepted, Nat.le_refl _⟩, by simp⟩
  rw [nil] at member
  exact List.not_mem_nil member

end MicroCFTA.LevelEnumeration
