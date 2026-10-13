import MicroCFTA.EqualityFixedProjectionInvariant

/-!
# One row after the higher row profile agrees

For a strict-ranked row relation, a product can produce a row only from
that row or from higher rows. If two node operands agree on all higher
rows, their product at the selected row has three possible forms. It is
Boolean conjunction, Boolean disjunction, or it retains both input bits
and can add the row. The whole-node identity shortcut preserves these
properties.

This is a local step for a synchronized profile argument. It does not
assume that arbitrary nested source nodes have a strict intersection rank.
The checked nested cycles exclude that stronger premise.
-/
namespace MicroCFTA.EqualityFixedRowProfile
open EqualityFixedProjectionInvariant

/-- Read one fixed set of rows above the selected row's rank. -/
def Profile (rank : Row → Nat) (selected : Row) (high rows : Rows Row) : Prop :=
  ∀ row, rank selected < rank row → (rows row ↔ high row)

/-- Two higher rows can create the selected row without an input copy of it. -/
def Creates (join : Row → Row → Row → Prop) (rank : Row → Nat)
    (selected : Row) (high : Rows Row) : Prop :=
  ∃ first second, rank selected < rank first ∧ rank selected < rank second ∧
    high first ∧ high second ∧ join first second selected

/-- A higher row can retain the selected row in a proper Cartesian product. -/
def Absorbs (join : Row → Row → Row → Prop) (rank : Row → Nat)
    (selected : Row) (high : Rows Row) : Prop :=
  ∃ row, rank selected < rank row ∧ high row ∧ join selected row selected

/-- An occurrence and its projected target can have different higher row profiles. -/
def CreatesBetween (join : Row → Row → Row → Prop) (rank : Row → Nat)
    (selected : Row) (leftHigh rightHigh : Rows Row) : Prop :=
  ∃ first second, rank selected < rank first ∧ rank selected < rank second ∧
    leftHigh first ∧ rightHigh second ∧ join first second selected

/-- The Cartesian product has an exact Boolean description at the selected row. -/
theorem product_at (join : Row → Row → Row → Prop) (rank : Row → Nat)
    (diagonal : ∀ row, join row row row)
    (symmetric : ∀ first second row, join first second row ↔ join second first row)
    (strict : ∀ first second row, join first second row → row ≠ first → rank row < rank first)
    (selected : Row) (high left right : Rows Row)
    (leftProfile : Profile rank selected high left) (rightProfile : Profile rank selected high right) :
    product join left right selected ↔
      Creates join rank selected high ∨
      (left selected ∧ Absorbs join rank selected high) ∨
      (right selected ∧ Absorbs join rank selected high) ∨
      (left selected ∧ right selected) := by
  classical
  constructor
  · rintro ⟨first, second, inFirst, inSecond, combined⟩
    by_cases firstSame : selected = first
    · subst first
      by_cases secondSame : selected = second
      · subst second
        exact Or.inr (Or.inr (Or.inr ⟨inFirst, inSecond⟩))
      · have higher := strict second selected selected ((symmetric _ _ _).mp combined) secondSame
        exact Or.inr (Or.inl ⟨inFirst, second, higher, (rightProfile second higher).mp inSecond, combined⟩)
    · have firstHigher := strict first second selected combined firstSame
      by_cases secondSame : selected = second
      · subst second
        exact Or.inr (Or.inr (Or.inl ⟨inSecond, first, firstHigher,
          (leftProfile first firstHigher).mp inFirst, (symmetric _ _ _).mp combined⟩))
      · have secondHigher := strict second first selected ((symmetric _ _ _).mp combined) secondSame
        exact Or.inl ⟨first, second, firstHigher, secondHigher,
          (leftProfile first firstHigher).mp inFirst, (rightProfile second secondHigher).mp inSecond, combined⟩
  · rintro (created | ⟨inLeft, absorbed⟩ | ⟨inRight, absorbed⟩ | ⟨inLeft, inRight⟩)
    · rcases created with ⟨first, second, firstHigher, secondHigher, inFirst, inSecond, combined⟩
      exact ⟨first, second, (leftProfile first firstHigher).mpr inFirst,
        (rightProfile second secondHigher).mpr inSecond, combined⟩
    · rcases absorbed with ⟨row, higher, present, combined⟩
      exact ⟨selected, row, inLeft, (rightProfile row higher).mpr present, combined⟩
    · rcases absorbed with ⟨row, higher, present, combined⟩
      exact ⟨row, selected, (leftProfile row higher).mpr present, inRight, (symmetric _ _ _).mp combined⟩
    · exact ⟨selected, selected, inLeft, inRight, diagonal selected⟩

/-- Creation from the common higher profile makes the selected bit inflationary. -/
theorem creates_retains (join : Row → Row → Row → Prop) (rank : Row → Nat)
    (selected : Row) (high left right : Rows Row)
    (leftProfile : Profile rank selected high left) (rightProfile : Profile rank selected high right)
    (created : Creates join rank selected high)
    (present : left selected ∨ right selected) : narrow join left right selected := by
  classical
  unfold narrow
  split
  next same => exact present.elim id (fun found => same ▸ found)
  next =>
    rcases created with ⟨first, second, firstHigher, secondHigher, inFirst, inSecond, combined⟩
    exact ⟨first, second, (leftProfile first firstHigher).mpr inFirst,
      (rightProfile second secondHigher).mpr inSecond, combined⟩

/-- Without creation, an absorbing higher row makes intersection Boolean disjunction. -/
theorem absorbs_or (join : Row → Row → Row → Prop) (rank : Row → Nat)
    (diagonal : ∀ row, join row row row)
    (symmetric : ∀ first second row, join first second row ↔ join second first row)
    (strict : ∀ first second row, join first second row → row ≠ first → rank row < rank first)
    (selected : Row) (high left right : Rows Row)
    (leftProfile : Profile rank selected high left) (rightProfile : Profile rank selected high right)
    (notCreated : ¬ Creates join rank selected high) (absorbed : Absorbs join rank selected high) :
    narrow join left right selected ↔ left selected ∨ right selected := by
  classical
  unfold narrow
  split
  next same => simp only [same, or_self]
  next =>
    rw [product_at join rank diagonal symmetric strict selected high left right leftProfile rightProfile]
    simp only [notCreated, absorbed, false_or, and_true]
    constructor
    · rintro (inLeft | inRight | ⟨inLeft, _⟩)
      · exact Or.inl inLeft
      · exact Or.inr inRight
      · exact Or.inl inLeft
    · exact fun present => present.elim Or.inl (fun found => Or.inr (Or.inl found))

/-- Without creation or absorption, intersection is Boolean conjunction. -/
theorem neither_and (join : Row → Row → Row → Prop) (rank : Row → Nat)
    (diagonal : ∀ row, join row row row)
    (symmetric : ∀ first second row, join first second row ↔ join second first row)
    (strict : ∀ first second row, join first second row → row ≠ first → rank row < rank first)
    (selected : Row) (high left right : Rows Row)
    (leftProfile : Profile rank selected high left) (rightProfile : Profile rank selected high right)
    (notCreated : ¬ Creates join rank selected high) (notAbsorbed : ¬ Absorbs join rank selected high) :
    narrow join left right selected ↔ left selected ∧ right selected := by
  classical
  unfold narrow
  split
  next same => simp only [same, and_self]
  next =>
    rw [product_at join rank diagonal symmetric strict selected high left right leftProfile rightProfile]
    simp only [notCreated, notAbsorbed, false_or, and_false]

/-- Creation or target absorption retains the occurrence bit for every pair of matching profiles. -/
theorem occurrence_increases (join : Row → Row → Row → Prop) (rank : Row → Nat)
    (selected : Row) (leftHigh rightHigh left right : Rows Row)
    (leftProfile : Profile rank selected leftHigh left) (rightProfile : Profile rank selected rightHigh right)
    (createsOrAbsorbs : CreatesBetween join rank selected leftHigh rightHigh ∨
      Absorbs join rank selected rightHigh)
    (present : left selected) : narrow join left right selected := by
  classical
  unfold narrow
  split
  · exact present
  · rcases createsOrAbsorbs with created | absorbed
    · rcases created with ⟨first, second, firstHigher, secondHigher, inFirst, inSecond, combined⟩
      exact ⟨first, second, (leftProfile first firstHigher).mpr inFirst,
        (rightProfile second secondHigher).mpr inSecond, combined⟩
    · rcases absorbed with ⟨row, higher, inHigh, combined⟩
      exact ⟨selected, row, present, (rightProfile row higher).mpr inHigh, combined⟩

/-- Without creation or target absorption, an included occurrence profile cannot gain the row. -/
theorem occurrence_decreases (join : Row → Row → Row → Prop) (rank : Row → Nat)
    (symmetric : ∀ first second row, join first second row ↔ join second first row)
    (strict : ∀ first second row, join first second row → row ≠ first → rank row < rank first)
    (selected : Row) (leftHigh rightHigh left right : Rows Row)
    (included : ∀ row, rank selected < rank row → leftHigh row → rightHigh row)
    (leftProfile : Profile rank selected leftHigh left) (rightProfile : Profile rank selected rightHigh right)
    (notCreated : ¬ CreatesBetween join rank selected leftHigh rightHigh)
    (notAbsorbed : ¬ Absorbs join rank selected rightHigh)
    (present : narrow join left right selected) : left selected := by
  classical
  unfold narrow at present
  split at present
  · exact present
  · rcases present with ⟨first, second, inFirst, inSecond, combined⟩
    by_cases firstSame : selected = first
    · exact firstSame ▸ inFirst
    · have firstHigher := strict first second selected combined firstSame
      have firstHigh := (leftProfile first firstHigher).mp inFirst
      by_cases secondSame : selected = second
      · subst second
        exact False.elim (notAbsorbed ⟨first, firstHigher, included first firstHigher firstHigh,
          (symmetric _ _ _).mp combined⟩)
      · have secondHigher := strict second first selected ((symmetric _ _ _).mp combined) secondSame
        exact False.elim (notCreated ⟨first, second, firstHigher, secondHigher, firstHigh,
          (rightProfile second secondHigher).mp inSecond, combined⟩)

/-- Fixed included higher profiles select one direction for all lower-bit edits. -/
theorem profile_direction (join : Row → Row → Row → Prop) (rank : Row → Nat)
    (symmetric : ∀ first second row, join first second row ↔ join second first row)
    (strict : ∀ first second row, join first second row → row ≠ first → rank row < rank first)
    (selected : Row) (leftHigh rightHigh : Rows Row)
    (included : ∀ row, rank selected < rank row → leftHigh row → rightHigh row) :
    (∀ left right, Profile rank selected leftHigh left → Profile rank selected rightHigh right →
      left selected → narrow join left right selected) ∨
    (∀ left right, Profile rank selected leftHigh left → Profile rank selected rightHigh right →
      narrow join left right selected → left selected) := by
  classical
  by_cases grows : CreatesBetween join rank selected leftHigh rightHigh ∨ Absorbs join rank selected rightHigh
  · exact Or.inl (fun left right a b => occurrence_increases join rank selected leftHigh rightHigh left right a b grows)
  · exact Or.inr (fun left right a b => occurrence_decreases join rank symmetric strict selected
      leftHigh rightHigh left right included a b (fun created => grows (Or.inl created))
      (fun absorbed => grows (Or.inr absorbed)))

end MicroCFTA.EqualityFixedRowProfile
