import MicroCFTA.RecursiveJoinTyped
import MicroCFTA.KeyedTermMass

/-!
# Retained mass and ranked sampling through a typed recursive join

Each size split multiplies operand masses. The sampler selects among live
splits by those masses. Structural counts determine every rank offset.
-/
namespace MicroCFTA.RecursiveJoinMass
open Language GeneratorCombinators Probability SamplerReplay
open RecursiveCallbackTermination RecursiveJoinFields RecursiveJoinTyped
open GroupedRecord (Group Classes Valid)
open KeyedTermMass (SameGroup map_left_group map_right_group apply_group merge_same)

/-- Map every source class without changing its mass or replay ranks. -/
def mapClasses (transform : Value → Result) (classes : Classes Value) : Classes Result :=
  fun size => GroupedRecord.map transform (classes size)

/-- The source mass-aware product combines every size split in count order. -/
def product (combine : Left → Right → Result) (left : Classes Left) (right : Classes Right) : Classes Result :=
  GroupedRecord.productClasses (mapClasses (fun first second => combine first second) left) right

/-- Product records are coherent when their independent operand records are coherent. -/
theorem product_valid (combine : Left → Right → Result) (left : Classes Left) (right : Classes Right)
    (leftValid : ∀ size, Valid (left size)) (rightValid : ∀ size, Valid (right size)) :
    ∀ size, Valid (product combine left right size) :=
  GroupedRecord.productClasses_valid _ _
    (fun size => GroupedRecord.map_valid _ _ (leftValid size)) rightValid

/-- Retained masses multiply at each split and add across the complete size class. -/
theorem product_mass (combine : Left → Right → Result) (left : Classes Left) (right : Classes Right) (size : Nat) :
    (product combine left right size).mass =
      ((List.range (size + 1)).map fun split => (left split).mass * (right (size - split)).mass).sum := by
  unfold product GroupedRecord.productClasses GroupedRecord.merge
  dsimp only
  induction List.range (size + 1) with
  | nil => rfl
  | cons split rest ih => simpa [GroupedRecord.massSum, mapClasses, GroupedRecord.apply, GroupedRecord.map] using congrArg ((left split).mass * (right (size - split)).mass + ·) ih

/-- Product class order is the independent source size split and left-major operand order. -/
theorem product_values (combine : Left → Right → Result) (left : Classes Left) (right : Classes Right) (size : Nat) :
    Decoder.values (product combine left right size).members.plan =
      (List.range (size + 1)).flatMap fun split =>
        (Decoder.values (left split).members.plan).flatMap fun first =>
          (Decoder.values (right (size - split)).members.plan).map (combine first) := by
  simp [product, GroupedRecord.productClasses_values, mapClasses, GroupedRecord.map,
    mapRecord, Decoder.values, Decoder.applyValues, List.flatMap_map]

/-- A value projection retains key mass, the complete rank law, and ordered decoder values. -/
def Projects (transform : Value → Result) (source : Group Value) (target : Group Result) : Prop :=
  SameGroup source target ∧ Decoder.values target.members.plan = (Decoder.values source.members.plan).map transform

/-- Local grouped maps establish their projection contract without a sampler premise. -/
theorem projects_map (transform : Value → Result) (source : Group Value) :
    Projects transform source (GroupedRecord.map transform source) :=
  ⟨map_right_group _ _ _ ⟨rfl, rfl, rfl⟩, rfl⟩

/-- Different value types retain all product masses and replay ranks. -/
theorem product_same (combineLeft : Left₁ → Right₁ → Result₁) (combineRight : Left₂ → Right₂ → Result₂)
    (left₁ : Classes Left₁) (right₁ : Classes Right₁) (left₂ : Classes Left₂) (right₂ : Classes Right₂)
    (leftSame : ∀ size, SameGroup (left₁ size) (left₂ size))
    (rightSame : ∀ size, SameGroup (right₁ size) (right₂ size)) (size : Nat) :
    SameGroup (product combineLeft left₁ right₁ size) (product combineRight left₂ right₂ size) := by
  apply merge_same
  have related : ∀ splits : List Nat, RecursiveRankMass.Related SameGroup
      (splits.map fun split => GroupedRecord.apply
        (GroupedRecord.map (fun first second => combineLeft first second) (left₁ split)) (right₁ (size - split)))
      (splits.map fun split => GroupedRecord.apply
        (GroupedRecord.map (fun first second => combineRight first second) (left₂ split)) (right₂ (size - split))) := by
    intro splits
    induction splits with
    | nil => exact .nil
    | cons split rest ih =>
        exact .cons (apply_group _ _ _ _
          (map_right_group _ _ _ (map_left_group _ _ _ (leftSame split))) (rightSame (size - split))) ih
  exact related _

/-- Commuting operand projections preserve the whole mass-aware product record. -/
theorem product_projects (combineLeft : Left₁ → Right₁ → Result₁) (combineRight : Left₂ → Right₂ → Result₂)
    (projectLeft : Left₁ → Left₂) (projectRight : Right₁ → Right₂) (projectResult : Result₁ → Result₂)
    (left₁ : Classes Left₁) (right₁ : Classes Right₁) (left₂ : Classes Left₂) (right₂ : Classes Right₂)
    (leftProjects : ∀ size, Projects projectLeft (left₁ size) (left₂ size))
    (rightProjects : ∀ size, Projects projectRight (right₁ size) (right₂ size))
    (commutes : ∀ first second, projectResult (combineLeft first second) = combineRight (projectLeft first) (projectRight second))
    (size : Nat) : Projects projectResult (product combineLeft left₁ right₁ size) (product combineRight left₂ right₂ size) := by
  refine ⟨product_same _ _ _ _ _ _ (fun size => (leftProjects size).1) (fun size => (rightProjects size).1) size, ?_⟩
  rw [product_values, product_values]
  simp only [List.map_flatMap]
  congr 1
  funext split
  rw [(leftProjects split).2, (rightProjects (size - split)).2]
  simp only [List.flatMap_map, List.map_map]
  congr 1
  funext first
  congr 1
  funext second
  exact (commutes first second).symm

/-- Each typed local leaf supplies its grouped classes with a correlated value and term. -/
abbrev LeafClasses (Symbol : Type) := {Value : Type} → Leaf Symbol Value → Classes (Value × EngineTerm Symbol)

/-- Fold the independent user-value records through a heterogeneous source chain. -/
def values (leaves : LeafClasses Symbol) (source : Classes Operand) : Chain Symbol Operand Result → Classes Result
  | .nil => source
  | .cons argument rest => values leaves
      (product (fun function value => function value) source (mapClasses Prod.fst (leaves argument))) rest

/-- Fold correlated user values, the operation term, and the argument forest. -/
def paired (leaves : LeafClasses Symbol) (source : Classes (Operand × Accumulated Symbol)) :
    Chain Symbol Operand Result → Classes (Result × Accumulated Symbol)
  | .nil => source
  | .cons argument rest => paired leaves
      (product (fun before after => (before.1 after.1, (before.2.1, before.2.2 ++ [after.2]))) source (leaves argument)) rest

/-- Fold the independent term records with the source forest append operation. -/
def terms (leaves : LeafClasses Symbol) (source : Classes (Accumulated Symbol)) :
    Chain Symbol Operand Result → Classes (Accumulated Symbol)
  | .nil => source
  | .cons argument rest => terms leaves
      (product (fun before after => (before.1, before.2 ++ [after])) source (mapClasses Prod.snd (leaves argument))) rest

/-- The complete source chain preserves the user-value projection and its full rank law. -/
theorem paired_values (leaves : LeafClasses Symbol) (chain : Chain Symbol Operand Result)
    (source : Classes (Operand × Accumulated Symbol)) (target : Classes Operand)
    (projects : ∀ size, Projects Prod.fst (source size) (target size)) (size : Nat) :
    Projects Prod.fst (paired leaves source chain size) (values leaves target chain size) := by
  induction chain generalizing size with
  | nil => exact projects size
  | cons argument rest ih =>
      apply ih
      intro size
      exact product_projects _ _ Prod.fst Prod.fst Prod.fst _ _ _ _ projects
        (fun size => projects_map _ _) (fun _ _ => rfl) size

/-- The complete source chain preserves every private term and its full rank law. -/
theorem paired_terms (leaves : LeafClasses Symbol) (chain : Chain Symbol Operand Result)
    (source : Classes (Operand × Accumulated Symbol)) (target : Classes (Accumulated Symbol))
    (projects : ∀ size, Projects Prod.snd (source size) (target size)) (size : Nat) :
    Projects Prod.snd (paired leaves source chain size) (terms leaves target chain size) := by
  induction chain generalizing target size with
  | nil => exact projects size
  | cons argument rest ih =>
      apply ih
      intro size
      exact product_projects _ _ Prod.snd Prod.snd Prod.snd _ _ _ _ projects
        (fun size => projects_map _ _) (fun _ _ => rfl) size

/-- Every argument supplies a valid grouped record at every exact size. -/
def LeavesValid (leaves : LeafClasses Symbol) : Chain Symbol Operand Result → Prop
  | .nil => True
  | .cons argument rest => (∀ size, Valid (leaves argument size)) ∧ LeavesValid leaves rest

/-- Correlated record construction preserves normalized sampling and complete rank coverage. -/
theorem paired_valid (leaves : LeafClasses Symbol) (chain : Chain Symbol Operand Result)
    (source : Classes (Operand × Accumulated Symbol)) (sourceValid : ∀ size, Valid (source size))
    (leavesValid : LeavesValid leaves chain) : ∀ size, Valid (paired leaves source chain size) := by
  induction chain with
  | nil => exact sourceValid
  | cons argument rest ih => exact ih _ (product_valid _ _ _ sourceValid leavesValid.1) leavesValid.2

/-- The separate user-value records satisfy the same complete grouped invariant. -/
theorem values_valid (leaves : LeafClasses Symbol) (chain : Chain Symbol Operand Result)
    (source : Classes Operand) (sourceValid : ∀ size, Valid (source size))
    (leavesValid : LeavesValid leaves chain) : ∀ size, Valid (values leaves source chain size) := by
  induction chain with
  | nil => exact sourceValid
  | cons argument rest ih => exact ih _ (product_valid _ _ _ sourceValid
      (fun size => GroupedRecord.map_valid _ _ (leavesValid.1 size))) leavesValid.2

/-- The separate term records retain the same grouped invariant. -/
theorem terms_valid (leaves : LeafClasses Symbol) (chain : Chain Symbol Operand Result)
    (source : Classes (Accumulated Symbol)) (sourceValid : ∀ size, Valid (source size))
    (leavesValid : LeavesValid leaves chain) : ∀ size, Valid (terms leaves source chain size) := by
  induction chain generalizing source with
  | nil => exact sourceValid
  | cons argument rest ih => exact ih _ (product_valid _ _ _ sourceValid
      (fun size => GroupedRecord.map_valid _ _ (leavesValid.1 size))) leavesValid.2

/-- Ordered value projection commutes with every source rank decoder. -/
theorem projects_decode (transform : Value → Result) (source : Group Value) (target : Group Result)
    (projects : Projects transform source target) (rank : Nat) :
    (Decoder.decode source.members.plan rank).map transform = Decoder.decode target.members.plan rank := by
  rw [Decoder.decode_correct, Decoder.decode_correct, projects.2, List.getElem?_map]

/-- Retaining replay ranks identifies the complete sampled distribution under projection. -/
theorem projects_ranked (transform : Value → Result) (source : Group Value) (target : Group Result)
    (projects : Projects transform source target) (sourceValid : Valid source) (targetValid : Valid target) :
    Probability.map (fun entry => (entry.1, transform entry.2)) source.members.sampling.ranked = target.members.sampling.ranked :=
  RecursiveRankMass.ranked_projection transform _ _ _ _ sourceValid.1.1.2 targetValid.1.1.2
    (projects_decode transform source target projects) projects.1.2.2

/-- Full user-value and rank probabilities follow from local operand record validity. -/
theorem ranked_values (leaves : LeafClasses Symbol) (chain : Chain Symbol Operand Result)
    (source : Classes (Operand × Accumulated Symbol)) (sourceValid : ∀ size, Valid (source size))
    (leavesValid : LeavesValid leaves chain) (size : Nat) :
    Probability.map (fun entry => (entry.1, entry.2.1)) (paired leaves source chain size).members.sampling.ranked =
      (values leaves (mapClasses Prod.fst source) chain size).members.sampling.ranked :=
  projects_ranked _ _ _ (paired_values leaves chain source _ (fun _ => projects_map _ _) size)
    (paired_valid leaves chain source sourceValid leavesValid size)
    (values_valid leaves chain _ (fun size => GroupedRecord.map_valid _ _ (sourceValid size)) leavesValid size)

/-- Full term-forest and rank probabilities follow from local operand record validity. -/
theorem ranked_terms (leaves : LeafClasses Symbol) (chain : Chain Symbol Operand Result)
    (source : Classes (Operand × Accumulated Symbol)) (sourceValid : ∀ size, Valid (source size))
    (leavesValid : LeavesValid leaves chain) (size : Nat) :
    Probability.map (fun entry => (entry.1, entry.2.2)) (paired leaves source chain size).members.sampling.ranked =
      (terms leaves (mapClasses Prod.snd source) chain size).members.sampling.ranked :=
  projects_ranked _ _ _ (paired_terms leaves chain source _ (fun _ => projects_map _ _) size)
    (paired_valid leaves chain source sourceValid leavesValid size)
    (terms_valid leaves chain _ (fun size => GroupedRecord.map_valid _ _ (sourceValid size)) leavesValid size)

/-- An empty structural class has zero retained mass. -/
theorem empty_mass (group : Group Value) (valid : Valid group) (empty : Decoder.count group.members.plan = 0) :
    group.mass = 0 := by
  have nonnegative := valid.2.1
  have notPositive : ¬0 < group.mass := by intro positive; have := valid.2.2.mp positive; omega
  grind

/-- A source minimum supplies zero counts at each smaller size. -/
def NoBelow (classes : Classes Value) (minimum : Nat) : Prop :=
  ∀ size, size < minimum → Decoder.count (classes size).members.plan = 0

/-- Minimum padding cannot remove any retained mass from a valid source class. -/
theorem mass_zero_below (classes : Classes Value) (minimum : Nat)
    (valid : ∀ size, Valid (classes size)) (lower : NoBelow classes minimum) (size : Nat) (below : size < minimum) :
    (classes size).mass = 0 := empty_mass _ (valid size) (lower size below)

/-- No product member exists below the sum of its independent operand minima. -/
theorem product_lower (combine : Left → Right → Result) (left : Classes Left) (right : Classes Right)
    (leftMinimum rightMinimum : Nat) (leftLower : NoBelow left leftMinimum) (rightLower : NoBelow right rightMinimum) :
    NoBelow (product combine left right) (leftMinimum + rightMinimum) := by
  intro size below
  rw [Decoder.count_correct, product_values]
  have empty : (List.range (size + 1)).flatMap (fun split =>
      (Decoder.values (left split).members.plan).flatMap fun first =>
        (Decoder.values (right (size - split)).members.plan).map (combine first)) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro split member
    have within : split ≤ size := by have := List.mem_range.mp member; omega
    by_cases smaller : split < leftMinimum
    · have zero := leftLower split smaller
      rw [Decoder.count_correct] at zero
      rw [List.length_eq_zero_iff.mp zero]
      rfl
    · have zero := rightLower (size - split) (by omega)
      rw [Decoder.count_correct] at zero
      simp [List.length_eq_zero_iff.mp zero]
  rw [empty]
  rfl

end MicroCFTA.RecursiveJoinMass