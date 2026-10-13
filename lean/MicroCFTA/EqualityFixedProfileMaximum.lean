import MicroCFTA.EqualityFixedRowProfile

/-!
# A removable maximum in a finite closed node family

The row-profile argument identifies one member that no distinct pair of
family members can produce. Repeated removal can assign a maximum-based
rank to one powerset layer over strict-ranked rows. This file proves the
removal step. It does not assert that this rank survives another powerset
layer or that arbitrary nested source rows have the required strict rank.
-/
namespace MicroCFTA.EqualityFixedProfileMaximum
open EqualityFixedProjectionInvariant EqualityFixedRowProfile

/-- Some family members contain the row and some omit it. -/
def Varies (family : List (Rows Row)) (row : Row) : Prop :=
  ∃ first ∈ family, ∃ second ∈ family, first row ∧ ¬ second row

/-- No intersection of two distinct family members produces this member. -/
def Prime (meet : Node → Node → Node) (family : List Node) (node : Node) : Prop :=
  node ∈ family ∧ ∀ first ∈ family, ∀ second ∈ family, first ≠ second → meet first second ≠ node

/-- Distinct finite row sets have a highest rank at which their family varies. -/
theorem highest_varies (rank : Row → Nat) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (family : List (Rows Row)) (different : ∃ first ∈ family, ∃ second ∈ family, first ≠ second) :
    ∃ selected, Varies family selected ∧
      ∀ first ∈ family, ∀ second ∈ family, ∀ row, rank selected < rank row → (first row ↔ second row) := by
  classical
  have existsRow : ∃ row, Varies family row := by
    apply Classical.byContradiction
    intro absent
    rcases different with ⟨first, inFirst, second, inSecond, unequal⟩
    apply unequal
    funext row
    apply propext
    constructor
    · intro present
      apply Classical.byContradiction
      intro missing
      exact absent ⟨row, first, inFirst, second, inSecond, present, missing⟩
    · intro present
      apply Classical.byContradiction
      intro missing
      exact absent ⟨row, second, inSecond, first, inFirst, present, missing⟩
  let varied := inventory.filter (fun row => decide (Varies family row))
  obtain ⟨row, varying⟩ := existsRow
  have member : row ∈ varied := by simp only [varied, List.mem_filter, decide_eq_true_eq]; exact ⟨complete row, varying⟩
  let selected := varied.maxOn rank (List.ne_nil_of_mem member)
  have selectedMember : selected ∈ varied := List.maxOn_mem
  have selectedVaries : Varies family selected := by
    exact of_decide_eq_true (List.mem_filter.mp selectedMember).2
  refine ⟨selected, selectedVaries, ?_⟩
  intro first inFirst second inSecond current higher
  have notVaried : ¬ Varies family current := by
    intro varies
    have found : current ∈ varied := by
      simp only [varied, List.mem_filter, decide_eq_true_eq]
      exact ⟨complete current, varies⟩
    have bound : rank current ≤ rank selected := List.le_apply_maxOn_of_mem found
    omega
  constructor
  · intro present
    apply Classical.byContradiction
    intro missing
    exact notVaried ⟨first, inFirst, second, inSecond, present, missing⟩
  · intro present
    apply Classical.byContradiction
    intro missing
    exact notVaried ⟨second, inSecond, first, inFirst, present, missing⟩

/-- Removing one rejected member makes a filtered family strictly shorter. -/
theorem filter_shorter (family : List Node) (keep : Node → Bool)
    (removed : ∃ node ∈ family, keep node = false) : (family.filter keep).length < family.length := by
  have bound := List.length_filter_le keep family
  apply Nat.lt_of_le_of_ne bound
  intro same
  rcases removed with ⟨node, member, rejected⟩
  have kept := List.length_filter_eq_length_iff.mp same node member
  simp only [rejected, Bool.false_eq_true] at kept

/-- An output-isolated subfamily keeps its removable maxima in the original family. -/
theorem prime_lift (meet : Node → Node → Node) (family : List Node) (keep : Node → Bool)
    (isolated : ∀ first ∈ family, ∀ second ∈ family, keep (meet first second) = true →
      keep first = true ∧ keep second = true)
    (node : Node) (prime : Prime meet (family.filter keep) node) : Prime meet family node := by
  refine ⟨(List.mem_filter.mp prime.1).1, ?_⟩
  intro first inFirst second inSecond different same
  have selected := (List.mem_filter.mp prime.1).2
  have inputs := isolated first inFirst second inSecond (same ▸ selected)
  exact prime.2 first (List.mem_filter.mpr ⟨inFirst, inputs.1⟩)
    second (List.mem_filter.mpr ⟨inSecond, inputs.2⟩) different same

/-- Every nonempty closed finite family has a member that no distinct pair produces. -/
theorem prime_exists (join : Row → Row → Row → Prop) (rank : Row → Nat)
    (diagonal : ∀ row, join row row row)
    (symmetric : ∀ first second row, join first second row ↔ join second first row)
    (strict : ∀ first second row, join first second row → row ≠ first → rank row < rank first)
    (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (family : List (Rows Row)) (nonempty : family ≠ [])
    (closed : ∀ first ∈ family, ∀ second ∈ family, narrow join first second ∈ family) :
    ∃ node, Prime (narrow join) family node := by
  classical
  by_cases allSame : ∀ first ∈ family, ∀ second ∈ family, first = second
  · obtain ⟨node, member⟩ := List.exists_mem_of_ne_nil family nonempty
    exact ⟨node, member, fun first a second b different => False.elim (different (allSame first a second b))⟩
  · have distinct : ∃ first ∈ family, ∃ second ∈ family, first ≠ second := by
      apply Classical.byContradiction
      intro absent
      apply allSame
      intro first a second b
      apply Classical.byContradiction
      intro different
      exact absent ⟨first, a, second, b, different⟩
    obtain ⟨selected, varying, higher⟩ := highest_varies rank inventory complete family distinct
    rcases varying with ⟨positive, inPositive, negative, inNegative, found, missing⟩
    have profile : ∀ node ∈ family, Profile rank selected positive node :=
      fun node member row above => higher node member positive inPositive row above
    by_cases created : Creates join rank selected positive
    · refine ⟨negative, inNegative, ?_⟩
      intro first a second b different same
      have present : narrow join first second selected := by
        rw [narrow, ite_eq_right different]
        exact (product_at join rank diagonal symmetric strict selected positive first second
          (profile first a) (profile second b)).mpr (Or.inl created)
      exact missing (same ▸ present)
    · by_cases absorbed : Absorbs join rank selected positive
      · let keep : Rows Row → Bool := fun node => decide (¬ node selected)
        have rule : ∀ first ∈ family, ∀ second ∈ family,
            narrow join first second selected ↔ first selected ∨ second selected :=
          fun first a second b => absorbs_or join rank diagonal symmetric strict selected positive
            first second (profile first a) (profile second b) created absorbed
        have subsetClosed : ∀ first ∈ family.filter keep, ∀ second ∈ family.filter keep,
            narrow join first second ∈ family.filter keep := by
          intro first a second b
          have ha := List.mem_filter.mp a
          have hb := List.mem_filter.mp b
          apply List.mem_filter.mpr
          refine ⟨closed first ha.1 second hb.1, ?_⟩
          simp only [keep, decide_eq_true_eq] at ha hb ⊢
          exact fun present => ((rule first ha.1 second hb.1).mp present).elim ha.2 hb.2
        have subsetNonempty : family.filter keep ≠ [] :=
          List.ne_nil_of_mem (List.mem_filter.mpr ⟨inNegative, by simpa only [keep, decide_eq_true_eq] using missing⟩)
        obtain ⟨node, prime⟩ := prime_exists join rank diagonal symmetric strict inventory complete
          (family.filter keep) subsetNonempty subsetClosed
        refine ⟨node, prime_lift (narrow join) family keep ?_ node prime⟩
        intro first a second b present
        simp only [keep, decide_eq_true_eq] at present ⊢
        exact ⟨fun h => present ((rule first a second b).mpr (Or.inl h)),
          fun h => present ((rule first a second b).mpr (Or.inr h))⟩
      · let keep : Rows Row → Bool := fun node => decide (node selected)
        have rule : ∀ first ∈ family, ∀ second ∈ family,
            narrow join first second selected ↔ first selected ∧ second selected :=
          fun first a second b => neither_and join rank diagonal symmetric strict selected positive
            first second (profile first a) (profile second b) created absorbed
        have subsetClosed : ∀ first ∈ family.filter keep, ∀ second ∈ family.filter keep,
            narrow join first second ∈ family.filter keep := by
          intro first a second b
          have ha := List.mem_filter.mp a
          have hb := List.mem_filter.mp b
          apply List.mem_filter.mpr
          refine ⟨closed first ha.1 second hb.1, ?_⟩
          simp only [keep, decide_eq_true_eq] at ha hb ⊢
          exact (rule first ha.1 second hb.1).mpr ⟨ha.2, hb.2⟩
        have subsetNonempty : family.filter keep ≠ [] :=
          List.ne_nil_of_mem (List.mem_filter.mpr ⟨inPositive, by simpa only [keep, decide_eq_true_eq] using found⟩)
        obtain ⟨node, prime⟩ := prime_exists join rank diagonal symmetric strict inventory complete
          (family.filter keep) subsetNonempty subsetClosed
        refine ⟨node, prime_lift (narrow join) family keep ?_ node prime⟩
        intro first a second b present
        simp only [keep, decide_eq_true_eq] at present ⊢
        exact (rule first a second b).mp present
termination_by family.length
decreasing_by
  · exact filter_shorter family _ ⟨positive, inPositive, by simp [found]⟩
  · exact filter_shorter family _ ⟨negative, inNegative, by simp [missing]⟩

end MicroCFTA.EqualityFixedProfileMaximum
