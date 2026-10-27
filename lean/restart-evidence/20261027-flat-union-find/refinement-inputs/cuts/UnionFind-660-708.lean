def Satisfies (forest : Forest) (assignment : Nat → α) : Prop :=
  ∀ left right, SameClass forest left right → assignment left = assignment right

/-- Singleton initialization imposes no equality between distinct values. -/
theorem initial_satisfies (variables : List Nat) (assignment : Nat → α) :
    Satisfies (withInitialValues variables) assignment := by
  intro left right same
  exact congrArg assignment ((initial_classes variables left right).mp same)

/-- Compression preserves exactly the assignments permitted by the forest. -/
theorem findRoot_satisfies (valid : Total forest)
    (result : findRoot fuel forest uv = some found) (assignment : Nat → α) :
    Satisfies found.forest assignment ↔ Satisfies forest assignment := by
  simp only [Satisfies, findRoot_classes valid result]

/-- Union adds exactly the requested value equality to the assignment constraints. -/
theorem union_satisfies (valid : Total forest)
    (result : union leftFuel rightFuel forest left right = some output) (assignment : Nat → α) :
    Satisfies output assignment ↔
      Satisfies forest assignment ∧ assignment left = assignment right := by
  have classes := (union_correct valid result).2
  constructor
  · intro after
    refine ⟨fun x y h => after x y ((classes x y).mpr (Or.inl h)), ?_⟩
    obtain ⟨lr, ls, lp⟩ := valid left
    obtain ⟨rr, rs, rp⟩ := valid right
    exact after left right ((classes left right).mpr
      (Or.inr (Or.inl ⟨⟨lr, ls, lp, lp⟩, ⟨rr, rs, rp, rp⟩⟩)))
  · rintro ⟨before, equality⟩ x y h
    rcases (classes x y).mp h with direct | ⟨xl, yr⟩ | ⟨xr, yl⟩
    · exact before x y direct
    · exact (before x left xl).trans (equality.trans (before y right yr).symm)
    · exact (before x right xr).trans (equality.symm.trans (before y left yl).symm)

/-- Roots of allocated variables stay inside the allocation domain. -/
def ClosedDomain (forest : Forest) (domain : List Nat) : Prop :=
  ∀ uv ∈ domain, ∀ root size, Reaches forest uv root size → root ∈ domain

/-- Singleton initialization keeps every allocated representative in the domain. -/
theorem initial_closed (variables domain : List Nat) : ClosedDomain (withInitialValues variables) domain := by
  intro uv member root size path
  have same := (reaches_unique path (.root (read_initial variables uv))).1
  simpa [same] using member

/-- Compression preserves allocation-domain closure. -/
theorem findRoot_closed (valid : Total forest) (closed : ClosedDomain forest domain)
    (result : findRoot fuel forest uv = some found) : ClosedDomain found.forest domain := by
  intro other member root size path
  exact closed other member root size ((findRoot_reaches_iff valid result ..).mp path)
