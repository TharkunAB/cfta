import MicroCFTA.InternedValueMassHeap
import MicroCFTA.InternedFreshOrdinaryConstruction
import MicroCFTA.InternedNestedConstructionGrowth

/-!
# Causal payload bounds for full repaired source construction

The original syntax transforms an initial bound on captured values and all
stored payloads. Every actual stopping state retains the transformed store
bound. Warm first-writer values use that same causal store invariant.
-/
namespace MicroCFTA.InternedFreshOrdinaryResultMass
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges ordinaryLevel)
local notation "Stored" => InternedValueMassHeap.Stored
local notation "mass" => InternedValueMass.value
local notation "edgeMass" => InternedValueMass.edge
variable {Symbol Guard : Type}

/-- One constructor pays for its literal list and retains the earlier store. -/
def inflate (length bound : Nat) : Nat := max bound (1 + length * (1 + bound))

/-- Constructor bounds retain every earlier payload bound. -/
theorem inflate_ge (length bound : Nat) : bound ≤ inflate length bound := Nat.le_max_left _ _

/-- A larger initial bound supports the same literal constructor list. -/
theorem inflate_mono (length : Nat) {first last : Nat} (enough : first ≤ last) :
    inflate length first ≤ inflate length last := by
  have multiplied := Nat.mul_le_mul_left length (Nat.add_le_add_left enough 1)
  unfold inflate
  omega

mutual
/-- Compute a complete source payload bound from original syntax and initial stores. -/
def transform : Syntax Symbol Guard → Nat → Nat
  | .empty, bound | .var _, bound => bound
  | .node rows, bound => inflate rows.length (rowsTransform rows bound)
  | .union values, bound => inflate values.length (manyTransform values bound)
  | .binder _ body, bound =>
      let depth := transform body bound
      let ordinary := transform body depth
      let actual := transform body ordinary
      1 + 3 * actual
termination_by expression => sizeOf expression

/-- Source children execute in order, with each actual prefix's transformed store. -/
def manyTransform : List (Syntax Symbol Guard) → Nat → Nat
  | [], bound => bound
  | first :: rest, bound => manyTransform rest (transform first bound)
termination_by expressions => sizeOf expressions

/-- Each row constructs children, emits one edge, then executes its tail. -/
def rowsTransform : List (EdgeSyntax Symbol Guard) → Nat → Nat
  | [], bound => bound
  | .mk _ _ children :: rest, bound =>
      rowsTransform rest (inflate children.length (manyTransform children bound))
termination_by expressions => sizeOf expressions
end

mutual
/-- Every full syntax transformer retains its initial bound. -/
theorem transform_ge (expression : Syntax Symbol Guard) (bound : Nat) : bound ≤ transform expression bound := by
  cases expression with
  | empty | var => simp only [transform]; exact Nat.le_refl _
  | node rows => rw [transform]; exact Nat.le_trans (rowsTransform_ge rows bound) (inflate_ge _ _)
  | union values => rw [transform]; exact Nat.le_trans (manyTransform_ge values bound) (inflate_ge _ _)
  | binder smart body =>
      have first := transform_ge body bound
      have second := transform_ge body (transform body bound)
      have third := transform_ge body (transform body (transform body bound))
      simp only [transform]
      omega
termination_by sizeOf expression

/-- An ordered source list retains its initial bound. -/
theorem manyTransform_ge (expressions : List (Syntax Symbol Guard)) (bound : Nat) : bound ≤ manyTransform expressions bound := by
  cases expressions with
  | nil => rw [manyTransform]; exact Nat.le_refl _
  | cons first rest => rw [manyTransform]; exact Nat.le_trans (transform_ge first bound) (manyTransform_ge rest _)
termination_by sizeOf expressions

/-- An ordered row list retains its initial bound. -/
theorem rowsTransform_ge (expressions : List (EdgeSyntax Symbol Guard)) (bound : Nat) : bound ≤ rowsTransform expressions bound := by
  cases expressions with
  | nil => rw [rowsTransform]; exact Nat.le_refl _
  | cons first rest =>
      cases first
      rw [rowsTransform]
      exact Nat.le_trans (manyTransform_ge _ bound) (Nat.le_trans (inflate_ge _ _) (rowsTransform_ge rest _))
termination_by sizeOf expressions
end

mutual
/-- Full source bounds are monotone in the initial store and capture bound. -/
theorem transform_mono (expression : Syntax Symbol Guard) {first last : Nat} (enough : first ≤ last) :
    transform expression first ≤ transform expression last := by
  cases expression with
  | empty | var => simpa only [transform] using enough
  | node rows => simpa only [transform] using inflate_mono rows.length (rowsTransform_mono rows enough)
  | union values => simpa only [transform] using inflate_mono values.length (manyTransform_mono values enough)
  | binder smart body =>
      have bound := transform_mono body (transform_mono body (transform_mono body enough))
      simp only [transform]
      omega
termination_by sizeOf expression

/-- The ordered child transformer is monotone. -/
theorem manyTransform_mono (expressions : List (Syntax Symbol Guard)) {first last : Nat} (enough : first ≤ last) :
    manyTransform expressions first ≤ manyTransform expressions last := by
  cases expressions with
  | nil => simpa only [manyTransform] using enough
  | cons value rest => simpa only [manyTransform] using manyTransform_mono rest (transform_mono value enough)
termination_by sizeOf expressions

/-- The ordered row transformer is monotone. -/
theorem rowsTransform_mono (expressions : List (EdgeSyntax Symbol Guard)) {first last : Nat} (enough : first ≤ last) :
    rowsTransform expressions first ≤ rowsTransform expressions last := by
  cases expressions with
  | nil => simpa only [rowsTransform] using enough
  | cons value rest =>
      cases value
      simpa only [rowsTransform] using rowsTransform_mono rest (inflate_mono _ (manyTransform_mono _ enough))
termination_by sizeOf expressions
end

private theorem values_le (values : List (Value Symbol Guard)) (bound : Nat)
    (inputs : ∀ value ∈ values, mass value ≤ bound) :
    InternedValueMass.values values ≤ values.length * (1 + bound) := by
  induction values with
  | nil => simp only [InternedValueMass.values, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons first rest ih =>
      have own := inputs first List.mem_cons_self
      have tail := ih (fun value member => inputs value (List.mem_cons_of_mem _ member))
      simp only [InternedValueMass.values, List.length_cons, Nat.succ_mul]
      omega

private theorem edges_le (edges : List (EdgeValue Symbol Guard)) (bound : Nat)
    (inputs : ∀ edge ∈ edges, edgeMass edge ≤ bound) :
    InternedValueMass.edges edges ≤ edges.length * (1 + bound) := by
  induction edges with
  | nil => simp only [InternedValueMass.edges, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons first rest ih =>
      have own := inputs first List.mem_cons_self
      have tail := ih (fun edge member => inputs edge (List.mem_cons_of_mem _ member))
      simp only [InternedValueMass.edges, List.length_cons, Nat.succ_mul]
      omega

private abbrev Checked (bound : Nat) (outcome : Outcome Symbol Guard A) (post : A → Prop) : Prop :=
  Stored bound outcome.state ∧ ∀ value state, outcome = .done value state → post value

private theorem done_checked (bound : Nat) (value : A) (state : State Symbol Guard)
    (post : A → Prop) (stored : Stored bound state) (result : post value) : Checked bound (.done value state) post := by
  refine ⟨stored, ?_⟩
  intro other after same
  cases same
  exact result

private theorem bind_checked (outcome : Outcome Symbol Guard A)
    (next : A → State Symbol Guard → Outcome Symbol Guard B) (firstBound lastBound : Nat)
    (firstPost : A → Prop) (post : B → Prop) (enough : firstBound ≤ lastBound)
    (first : Checked firstBound outcome firstPost)
    (later : ∀ value state, Stored firstBound state → firstPost value → Checked lastBound (next value state) post) :
    Checked lastBound (outcome.bind next) post := by
  cases outcome with
  | pending key state =>
      refine ⟨first.1.mono enough, ?_⟩
      intro value after impossible
      cases impossible
  | done value state => exact later value state first.1 (first.2 value state rfl)

end MicroCFTA.InternedFreshOrdinaryResultMass
