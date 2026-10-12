import MicroCFTA.RecursiveJoinQuery
import MicroCFTA.SupportSpineAlternatives

/-!
# Size-independent source languages for recursive support assembly

Support graphs describe membership and omit rank multiplicity and size.
The local source interpretation erases size only after each finite leaf
has supplied a size witness. Recursive derivations retain those witnesses.
-/
namespace MicroCFTA.RecursiveJoinSupportSemantics
open Language GeneratorCombinators

/-- Interpret one typed source body under independently supplied key languages. -/
def denotes : KeyedSource.Recipe Key Root Value → (Key → Root → Prop) → Value → Prop
  | .finite source, _, value | .retained _ _ source, _, value => ∃ size, value ∈ FiniteSource.classMembers source size
  | .occurrence key, environment, value => environment key value
  | .map transform inner, environment, value => ∃ original, denotes inner environment original ∧ value = transform original
  | .pay inner, environment, value => denotes inner environment value
  | .choice left right, environment, value => denotes left environment value ∨ denotes right environment value
  | .ap functions arguments, environment, value => ∃ function argument,
      denotes functions environment function ∧ denotes arguments environment argument ∧ value = function argument

/-- Source body interpretation is monotone in each recursive key language. -/
theorem denotes_mono (recipe : KeyedSource.Recipe Key Root Value) (left right : Key → Root → Prop)
    (included : ∀ key value, left key value → right key value) (value : Value) :
    denotes recipe left value → denotes recipe right value := by
  induction recipe with
  | finite source | retained mass positive source => exact id
  | occurrence key => exact included key value
  | map transform inner ih => rintro ⟨original, accepted, rfl⟩; exact ⟨original, ih original accepted, rfl⟩
  | pay inner ih => exact ih value
  | choice left right ihl ihr => exact Or.imp (ihl value) (ihr value)
  | ap functions arguments ihf iha =>
      rintro ⟨function, argument, acceptedFunction, acceptedArgument, rfl⟩
      exact ⟨function, argument, ihf function acceptedFunction, iha argument acceptedArgument, rfl⟩

/-- A source interpretation can use any componentwise equal key language. -/
theorem denotes_congr (recipe : KeyedSource.Recipe Key Root Value) (left right : Key → Root → Prop)
    (same : ∀ key value, left key value ↔ right key value) (value : Value) :
    denotes recipe left value ↔ denotes recipe right value :=
  ⟨denotes_mono recipe left right (fun key value => (same key value).mp) value,
    denotes_mono recipe right left (fun key value => (same key value).mpr) value⟩

/-- Every size-indexed derivation belongs to any source language closed under its bodies. -/
theorem derives_closed (program : Key → KeyedSource.Recipe Key Root Root) (environment : Key → Root → Prop)
    (closed : ∀ key value, denotes (program key) environment value → environment key value)
    (recipe : KeyedSource.Recipe Key Root Value) (value : Value) (size : Nat)
    (derived : KeyedSource.Derives program recipe value size) : denotes recipe environment value := by
  induction derived with
  | finite source value size member | retained mass positive source value size member => exact ⟨size, member⟩
  | occurrence key value size child ih => exact closed key value ih
  | map transform inner value size child ih => exact ⟨value, ih, rfl⟩
  | pay inner value size child ih => exact ih
  | left left right value size child ih => exact Or.inl ih
  | right left right value size child ih => exact Or.inr ih
  | ap functions arguments function argument leftSize rightSize left right ihl ihr => exact ⟨function, argument, ihl, ihr, rfl⟩

/-- The language of all finite size-indexed derivations at one recursive key. -/
def members (program : Key → KeyedSource.Recipe Key Root Root) (key : Key) (value : Root) : Prop :=
  ∃ size, KeyedSource.Derives program (program key) value size

/-- Each size-independent body member has a finite derivation with a concrete size. -/
theorem denotes_derives (program : Key → KeyedSource.Recipe Key Root Root)
    (recipe : KeyedSource.Recipe Key Root Value) (value : Value) :
    denotes recipe (members program) value → ∃ size, KeyedSource.Derives program recipe value size := by
  induction recipe with
  | finite source => rintro ⟨size, member⟩; exact ⟨size, .finite source value size member⟩
  | retained mass positive source => rintro ⟨size, member⟩; exact ⟨size, .retained mass positive source value size member⟩
  | occurrence key => rintro ⟨size, member⟩; exact ⟨size, .occurrence key value size member⟩
  | map transform inner ih =>
      rintro ⟨original, accepted, rfl⟩
      obtain ⟨size, child⟩ := ih original accepted
      exact ⟨size, .map transform inner original size child⟩
  | pay inner ih =>
      intro accepted
      obtain ⟨size, child⟩ := ih value accepted
      exact ⟨size + 1, .pay inner value size child⟩
  | choice left right ihl ihr =>
      rintro (accepted | accepted)
      · obtain ⟨size, child⟩ := ihl value accepted; exact ⟨size, .left left right value size child⟩
      · obtain ⟨size, child⟩ := ihr value accepted; exact ⟨size, .right left right value size child⟩
  | ap functions arguments ihf iha =>
      rintro ⟨function, argument, acceptedFunction, acceptedArgument, rfl⟩
      obtain ⟨leftSize, left⟩ := ihf function acceptedFunction
      obtain ⟨rightSize, right⟩ := iha argument acceptedArgument
      exact ⟨leftSize + rightSize, .ap functions arguments function argument leftSize rightSize left right⟩

/-- Support membership forgets only the witnessed size of a finite source derivation. -/
theorem denotes_iff_derives (program : Key → KeyedSource.Recipe Key Root Root)
    (recipe : KeyedSource.Recipe Key Root Value) (value : Value) :
    denotes recipe (members program) value ↔ ∃ size, KeyedSource.Derives program recipe value size := by
  constructor
  · exact denotes_derives program recipe value
  · rintro ⟨size, derived⟩
    exact derives_closed program (members program) (fun key value => denotes_derives program (program key) value) recipe value size derived

/-- Flat choice lowering preserves the union of the original branch languages. -/
theorem denotes_alternatives (recipes : List (KeyedSource.Recipe Key Root Value))
    (environment : Key → Root → Prop) (value : Value) :
    denotes (KeyedNaryAlignment.alternatives recipes) environment value ↔
      ∃ recipe ∈ recipes, denotes recipe environment value := by
  induction recipes with
  | nil => simp [KeyedNaryAlignment.alternatives, KeyedNaryAlignment.empty, denotes, FiniteSource.classMembers]
  | cons first rest ih =>
      cases rest with
      | nil => simp [KeyedNaryAlignment.alternatives]
      | cons second rest => simp only [KeyedNaryAlignment.alternatives, denotes, ih, List.mem_cons, exists_eq_or_imp]

end MicroCFTA.RecursiveJoinSupportSemantics
