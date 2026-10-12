import MicroCFTA.SourceActuals

/-!
# Canonical outer conjunctions

Flatten only And nodes. Keep scoped, negated, and disjunctive guards intact.
Remove Top and duplicate conjuncts. Sorting uses the source structural order.
-/
namespace MicroCFTA.GuardConjunction
open SourceGuards Guards

/-- Flatten the outer conjunction without crossing any other guard constructor. -/
def atoms : SourceGuards.Guard Formula → List (SourceGuards.Guard Formula)
  | .top => []
  | .and parts => parts.flatMap atoms
  | guard => [guard]

/-- The source reuses Top and singleton guards instead of adding an And node. -/
def conjoin : List (SourceGuards.Guard Formula) → SourceGuards.Guard Formula
  | [] => .top
  | [guard] => guard
  | guards => .and guards

/-- Sorted sets are represented by duplicate-free sorted lists. -/
def canonical [DecidableEq Atom] (le : Atom → Atom → Bool) (items : List Atom) : List Atom :=
  items.eraseDups.mergeSort le

/-- Normalize one whole outer conjunction. -/
def normalize [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (guard : SourceGuards.Guard Formula) : SourceGuards.Guard Formula :=
  conjoin (canonical le (atoms guard))

theorem canonical_mem [DecidableEq Atom] (le : Atom → Atom → Bool) (items : List Atom) (item : Atom) :
    item ∈ canonical le items ↔ item ∈ items := by simp [canonical]

/-- Conjunctive and disjunctive folds are determined by their decisive verdicts. -/
theorem combine_yes (items : List Verdict) :
    combine true items = .yes ↔ ∀ item ∈ items, item = .yes := by
  induction items with
  | nil => simp [combine]
  | cons item rest ih => cases item <;> cases found : combine true rest <;> simp_all [combine, conjunction] <;> assumption

theorem combine_no (items : List Verdict) :
    combine true items = .no ↔ .no ∈ items := by
  induction items with
  | nil => simp [combine]
  | cons item rest ih => cases item <;> cases found : combine true rest <;> simp_all [combine, conjunction]

theorem disjoin_no (items : List Verdict) :
    combine false items = .no ↔ ∀ item ∈ items, item = .no := by
  induction items with
  | nil => simp [combine]
  | cons item rest ih => cases item <;> cases found : combine false rest <;> simp_all [combine, disjunction] <;> assumption

theorem disjoin_yes (items : List Verdict) :
    combine false items = .yes ↔ .yes ∈ items := by
  induction items with
  | nil => simp [combine]
  | cons item rest ih => cases item <;> cases found : combine false rest <;> simp_all [combine, disjunction]

/-- Reordering and removing duplicates preserve all three outcomes. -/
theorem combine_ext (positive : Bool) (first second : List Verdict)
    (same : ∀ item, item ∈ first ↔ item ∈ second) : combine positive first = combine positive second := by
  have yes : combine positive first = .yes ↔ combine positive second = .yes := by
    cases positive <;> simp only [combine_yes, disjoin_yes]
    · exact same .yes
    · exact ⟨fun all item member => all item ((same item).mpr member), fun all item member => all item ((same item).mp member)⟩
  have no : combine positive first = .no ↔ combine positive second = .no := by
    cases positive <;> simp only [combine_no, disjoin_no]
    · exact ⟨fun all item member => all item ((same item).mpr member), fun all item member => all item ((same item).mp member)⟩
    · exact same .no
  cases firstResult : combine positive first <;> cases secondResult : combine positive second <;> simp_all

theorem combine_singleton (positive : Bool) (item : Verdict) : combine positive [item] = item := by
  cases positive <;> cases item <;> rfl

/-- The connective selected by the current polarity. -/
def join (positive : Bool) (first second : Verdict) : Verdict :=
  if positive then conjunction first second else disjunction first second

private theorem join_assoc (positive : Bool) (a b c : Verdict) :
    join positive (join positive a b) c = join positive a (join positive b c) := by
  cases positive
  · exact disjunction_associative a b c
  · exact conjunction_associative a b c

private theorem join_left (positive : Bool) (v : Verdict) :
    join positive (if positive then .yes else .no) v = v := by
  cases positive <;> cases v <;> rfl

theorem combine_cons (positive : Bool) (item : Verdict) (items : List Verdict) :
    combine positive (item :: items) = join positive item (combine positive items) := by
  cases positive <;> cases item <;> rfl

theorem combine_append (positive : Bool) (first second : List Verdict) :
    combine positive (first ++ second) = join positive (combine positive first) (combine positive second) := by
  induction first with
  | nil => exact (join_left positive _).symm
  | cons item rest ih =>
      simp only [List.cons_append, combine_cons, ih]
      exact (join_assoc positive item _ _).symm

/-- Flattening nested Boolean folds does not change their verdict. -/
theorem combine_flatMap (positive : Bool) (groups : List (List Verdict)) :
    combine positive groups.flatten = combine positive (groups.map (combine positive)) := by
  induction groups with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.flatten_cons, combine_append, ih, List.map_cons, combine_cons]

/-- Outer flattening preserves the complete current evaluator at fixed tables and scope. -/
theorem atoms_evaluate (formulas : Formulas Formula) (solver : Entailment Formula) (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (fresh : List (Path × (Name × Name))) (unknown : List Path)
    (scopes : List (List (Resolved Formula))) (positive : Bool) (guard : SourceGuards.Guard Formula) :
    combine positive ((atoms guard).map (evaluateWith formulas solver observed sameAt fresh unknown scopes positive)) =
      evaluateWith formulas solver observed sameAt fresh unknown scopes positive guard := by
  let eval := evaluateWith formulas solver observed sameAt fresh unknown scopes positive
  induction guard using SourceGuards.Guard.rec
    (motive_2 := fun guards => ∀ guard ∈ guards, combine positive ((atoms guard).map eval) = eval guard) with
  | top => cases positive <;> simp [atoms, evaluateWith, polarize, combine, negate]
  | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ | substitute _ _ _ | not _ _ | or _ _ =>
      simpa only [atoms, List.map_singleton] using combine_singleton positive _
  | and parts ih =>
      simp only [atoms, evaluateWith]
      change combine positive ((parts.flatMap atoms).map eval) = combine positive (parts.map eval)
      have same : parts.map (fun guard => combine positive ((atoms guard).map eval)) = parts.map eval := by
        apply List.map_congr_left
        exact ih
      have grouped := combine_flatMap positive (parts.map (fun guard => (atoms guard).map eval))
      simpa only [← List.flatMap_def, List.map_flatMap, List.map_map, Function.comp_def, same] using grouped
  | nil => rename_i guard member; simp at member
  | cons first rest ih ir =>
      rename_i guard member
      rcases List.mem_cons.mp member with rfl | member
      · exact ih
      · exact ir guard member

/-- Rebuilding a list conjunction preserves its fold, including Top and singleton cases. -/
theorem conjoin_evaluate (formulas : Formulas Formula) (solver : Entailment Formula) (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (fresh : List (Path × (Name × Name))) (unknown : List Path)
    (scopes : List (List (Resolved Formula))) (positive : Bool) (guards : List (SourceGuards.Guard Formula)) :
    evaluateWith formulas solver observed sameAt fresh unknown scopes positive (conjoin guards) =
      combine positive (guards.map (evaluateWith formulas solver observed sameAt fresh unknown scopes positive)) := by
  cases guards with
  | nil => cases positive <;> simp [conjoin, evaluateWith, polarize, combine, negate]
  | cons first rest => cases rest with
    | nil => exact (combine_singleton positive _).symm
    | cons second rest => simp only [conjoin, evaluateWith]

/-- Canonical conjunction keeps Yes, No, and Unknown for all current guards and nested scopes. -/
theorem normalize_evaluate [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (formulas : Formulas Formula) (solver : Entailment Formula) (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (fresh : List (Path × (Name × Name))) (unknown : List Path)
    (scopes : List (List (Resolved Formula))) (positive : Bool) (guard : SourceGuards.Guard Formula) :
    evaluateWith formulas solver observed sameAt fresh unknown scopes positive (normalize le guard) =
      evaluateWith formulas solver observed sameAt fresh unknown scopes positive guard := by
  rw [normalize, conjoin_evaluate, ← atoms_evaluate formulas solver observed sameAt fresh unknown scopes positive guard]
  apply combine_ext
  intro verdict
  simp [canonical_mem]

private theorem eraseDups_nodup {α : Type _} [BEq α] [LawfulBEq α] (items : List α) : items.eraseDups.Nodup := by
  cases items with
  | nil => simp
  | cons first rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp only [List.mem_eraseDups, List.mem_filter]
        intro member
        simpa using member.2
      · exact eraseDups_nodup _
termination_by items.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le ..)


/-- A structural total order gives one canonical list for each finite set. -/
theorem canonical_ext [DecidableEq Atom] (le : Atom → Atom → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a)
    (antisymm : ∀ a b, le a b → le b a → a = b)
    (first second : List Atom) (same : ∀ atom, atom ∈ first ↔ atom ∈ second) :
    canonical le first = canonical le second := by
  apply List.Perm.eq_of_pairwise (fun a b _ _ => antisymm a b)
    (List.pairwise_mergeSort trans total _) (List.pairwise_mergeSort trans total _)
  apply (List.perm_ext_iff_of_nodup
    ((List.mergeSort_perm _ _).symm.nodup (eraseDups_nodup _))
    ((List.mergeSort_perm _ _).symm.nodup (eraseDups_nodup _))).mpr
  intro atom
  simpa [canonical] using same atom

/-- Every retained conjunct is already indivisible by the outer flattening. -/
theorem atoms_irreducible (guard : SourceGuards.Guard Formula)
    (atom : SourceGuards.Guard Formula) (member : atom ∈ atoms guard) : atoms atom = [atom] := by
  induction guard using SourceGuards.Guard.rec
    (motive_2 := fun guards => ∀ guard ∈ guards, ∀ atom ∈ atoms guard, atoms atom = [atom]) generalizing atom with
  | top => simp only [atoms, List.not_mem_nil] at member
  | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ | substitute _ _ _ | not _ _ | or _ _ =>
      simp only [atoms, List.mem_singleton] at member
      subst atom
      simp only [atoms]
  | and parts ih =>
      simp only [atoms] at member
      obtain ⟨guard, present, member⟩ := List.mem_flatMap.mp member
      exact ih guard present atom member
  | nil => rename_i guard present atom member; simp at present
  | cons first rest ih ir =>
      rename_i guard present atom member
      rcases List.mem_cons.mp present with rfl | present
      · exact ih atom member
      · exact ir guard present atom member

/-- Rebuilding normalized conjuncts does not create a new nested conjunction. -/
theorem atoms_conjoin (guards : List (SourceGuards.Guard Formula))
    (irreducible : ∀ guard ∈ guards, atoms guard = [guard]) : atoms (conjoin guards) = guards := by
  cases guards with
  | nil => simp only [conjoin, atoms]
  | cons first rest => cases rest with
    | nil => exact irreducible first (by simp)
    | cons second rest =>
        simp only [conjoin, atoms]
        have expanded : (first :: second :: rest).flatMap atoms =
            (first :: second :: rest).flatMap (fun guard => [guard]) := by
          rw [List.flatMap_def, List.flatMap_def]
          apply congrArg List.flatten
          exact List.map_congr_left irreducible
        simpa using expanded

/-- Normalization exposes exactly its sorted distinct atom list. -/
theorem atoms_normalize [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (guard : SourceGuards.Guard Formula) : atoms (normalize le guard) = canonical le (atoms guard) := by
  apply atoms_conjoin
  intro atom member
  exact atoms_irreducible guard atom ((canonical_mem le _ atom).mp member)

/-- Repeated normalization is structurally idempotent under the source total order. -/
theorem normalize_idempotent [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (antisymm : ∀ a b, le a b → le b a → a = b) (guard : SourceGuards.Guard Formula) :
    normalize le (normalize le guard) = normalize le guard := by
  unfold normalize
  apply congrArg conjoin
  apply canonical_ext le trans total antisymm
  intro atom
  rw [atoms_conjoin _ (fun atom member => atoms_irreducible guard atom ((canonical_mem le _ atom).mp member))]
  exact canonical_mem le _ atom

/-- The repaired binary conjunction uses the complete set of both operands' outer atoms. -/
def merge [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (left right : SourceGuards.Guard Formula) : SourceGuards.Guard Formula := normalize le (.and [left, right])

/-- All association and operand orders have the same syntactic normal form. -/
theorem merge_associative [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (antisymm : ∀ a b, le a b → le b a → a = b)
    (a b c : SourceGuards.Guard Formula) : merge le (merge le a b) c = merge le a (merge le b c) := by
  simp only [merge, normalize]
  apply congrArg conjoin
  apply canonical_ext le trans total antisymm
  intro atom
  simp only [atoms, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have clean (left right : SourceGuards.Guard Formula) :
      atoms (conjoin (canonical le (atoms left ++ atoms right))) = canonical le (atoms left ++ atoms right) := by
    apply atoms_conjoin
    intro atom member
    rcases List.mem_append.mp ((canonical_mem le _ atom).mp member) with member | member
    · exact atoms_irreducible left atom member
    · exact atoms_irreducible right atom member
  simp only [clean, List.mem_append, canonical_mem, or_assoc]

theorem merge_commutative [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (antisymm : ∀ a b, le a b → le b a → a = b)
    (a b : SourceGuards.Guard Formula) : merge le a b = merge le b a := by
  unfold merge normalize
  apply congrArg conjoin
  apply canonical_ext le trans total antisymm
  intro atom
  simp [atoms, or_comm]

/-- Canonical conjunctions contain no more atoms than the original input. -/
theorem normalize_atoms_bound [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (guard : SourceGuards.Guard Formula) : (atoms (normalize le guard)).length ≤ (atoms guard).length := by
  rw [atoms_normalize]
  apply List.Nodup.length_le_of_subset
    ((List.mergeSort_perm _ _).symm.nodup (eraseDups_nodup _))
  intro atom member
  exact (canonical_mem le _ atom).mp member

/-- Two guards with the same outer atom set have the same normal form. -/
theorem normalize_eq [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (antisymm : ∀ a b, le a b → le b a → a = b)
    (first second : SourceGuards.Guard Formula)
    (same : ∀ atom, atom ∈ atoms first ↔ atom ∈ atoms second) : normalize le first = normalize le second :=
  congrArg conjoin (canonical_ext le trans total antisymm _ _ same)

/-- Merging retains precisely the union of the original outer atom sets. -/
theorem merge_mem [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (left right atom : SourceGuards.Guard Formula) :
    atom ∈ atoms (merge le left right) ↔ atom ∈ atoms left ∨ atom ∈ atoms right := by
  rw [merge, atoms_normalize, canonical_mem]
  simp only [atoms, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]

/-- Repeated intersection with an existing conjunct cannot grow the canonical syntax. -/
theorem merge_absorbs [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (antisymm : ∀ a b, le a b → le b a → a = b)
    (left right : SourceGuards.Guard Formula) : merge le (merge le left right) left = merge le left right := by
  apply normalize_eq le trans total antisymm
  intro atom
  simp only [atoms, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, merge_mem]
  grind

/-- Conjoining a canonical result with itself returns the identical guard. -/
theorem merge_normalized_self [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (antisymm : ∀ a b, le a b → le b a → a = b)
    (guard : SourceGuards.Guard Formula) : merge le (normalize le guard) (normalize le guard) = normalize le guard := by
  rw [← normalize_idempotent le trans total antisymm guard]
  apply normalize_eq le trans total antisymm
  intro atom
  simp only [atoms, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, or_self,
    atoms_normalize, canonical_mem]

end MicroCFTA.GuardConjunction
