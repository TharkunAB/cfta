import MicroCFTA.InternedValueMassHeap
import MicroCFTA.InternedNestedConstructionGrowth
import MicroCFTA.InternedFreshOrdinaryAllocationBudget
import MicroCFTA.InternedStoredEncodingWidth

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

end MicroCFTA.InternedFreshOrdinaryResultMass
/-!
# Numeric payload bounds for bounded constructor widths

A fixed literal width and the initial constructor allocation budget dominate
the complete syntax mass transformer. Every unit pays one conservative
growth step. This bound can later use a stored value's initial mass without
retaining its full encoded syntax in the numeric resource condition.
-/
namespace MicroCFTA.InternedFreshOrdinaryUniformMass
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedFreshOrdinaryAllocationBudget
open InternedFreshOrdinaryResultMass
open InternedStoredEncodingWidth (Width Many Rows)
variable {Symbol Guard : Type}

/-- One step pays for any literal list within the fixed width. -/
def grow (width bound : Nat) : Nat := (width + 3) * (bound + 1)

/-- Iterate the same numeric growth rule from the original payload bound. -/
def evolve (width : Nat) : Nat → Nat → Nat
  | 0, bound => bound
  | count + 1, bound => grow width (evolve width count bound)

/-- Each numeric growth step retains the preceding payload bound. -/
theorem grow_ge (width bound : Nat) : bound ≤ grow width bound := by
  simp only [grow, Nat.add_mul, Nat.mul_add]
  omega

/-- Larger initial payload bounds remain ordered after one growth step. -/
theorem grow_mono (width : Nat) {first last : Nat} (enough : first ≤ last) :
    grow width first ≤ grow width last :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_right enough 1)

/-- A literal constructor list fits one growth step. -/
theorem inflate_bound (width length bound : Nat) (fits : length ≤ width) :
    inflate length bound ≤ grow width bound := by
  have multiplied := Nat.mul_le_mul_right (1 + bound) fits
  have retained := grow_ge width bound
  simp only [inflate, Nat.max_le]
  refine ⟨retained, ?_⟩
  simp only [grow, Nat.add_mul, Nat.mul_add] at multiplied ⊢
  omega

/-- Larger initial bounds remain ordered through the same finite schedule. -/
theorem evolve_mono (width count : Nat) {first last : Nat} (enough : first ≤ last) :
    evolve width count first ≤ evolve width count last := by
  induction count with
  | zero => exact enough
  | succ count ih => exact grow_mono width ih

/-- Additional growth steps retain the earlier finite bound. -/
theorem evolve_count_mono (width : Nat) {first last : Nat} (enough : first ≤ last) (bound : Nat) :
    evolve width first bound ≤ evolve width last bound := by
  induction enough with
  | refl => exact Nat.le_refl _
  | @step last _ ih => exact Nat.le_trans ih (grow_ge width (evolve width last bound))

/-- Consecutive numeric schedules compose at their exact intermediate bound. -/
theorem evolve_add (width first last bound : Nat) :
    evolve width (first + last) bound = evolve width last (evolve width first bound) := by
  induction last with
  | zero => simp only [Nat.add_zero, evolve]
  | succ last ih => simp only [Nat.add_succ, evolve, ih]

private theorem binder_grow (width bound : Nat) : 1 + 3 * bound ≤ grow width bound := by
  simp only [grow, Nat.add_mul, Nat.mul_add]
  omega

mutual
/-- Initial width and constructor charges bound the complete source transformer. -/
theorem transform_bound (width : Nat) (expression : Syntax Symbol Guard) (bound : Nat)
    (fits : Width width expression) :
    transform expression bound ≤ evolve width (nodeBudget expression + edgeBudget expression) bound := by
  cases expression with
  | empty | var => simp only [transform, nodeBudget, edgeBudget, Nat.add_zero, evolve]; exact Nat.le_refl _
  | node rows =>
      simp only [Width] at fits
      have prior := rows_bound width rows bound fits.2
      have one := Nat.le_trans (inflate_bound width rows.length (rowsTransform rows bound) fits.1)
        (grow_mono width prior)
      have count : rowNodes rows + 1 + rowEdges rows = (rowNodes rows + rowEdges rows) + 1 := by omega
      simpa only [transform, nodeBudget, edgeBudget, count, evolve] using one
  | union members =>
      simp only [Width] at fits
      have prior := many_bound width members bound fits.2
      have one := Nat.le_trans (inflate_bound width members.length (manyTransform members bound) fits.1)
        (grow_mono width prior)
      have count : manyNodes members + 1 + manyEdges members = (manyNodes members + manyEdges members) + 1 := by omega
      simpa only [transform, nodeBudget, edgeBudget, count, evolve] using one
  | binder smart body =>
      simp only [Width] at fits
      let count := nodeBudget body + edgeBudget body
      have first : transform body bound ≤ evolve width count bound := transform_bound width body bound fits
      have second : transform body (transform body bound) ≤ evolve width (count + count) bound := by
        calc
          _ ≤ evolve width count (transform body bound) := transform_bound width body _ fits
          _ ≤ evolve width count (evolve width count bound) := evolve_mono width count first
          _ = _ := (evolve_add width count count bound).symm
      have third : transform body (transform body (transform body bound)) ≤
          evolve width (count + count + count) bound := by
        calc
          _ ≤ evolve width count (transform body (transform body bound)) := transform_bound width body _ fits
          _ ≤ evolve width count (evolve width (count + count) bound) := evolve_mono width count second
          _ = _ := (evolve_add width (count + count) count bound).symm
      have grown := Nat.le_trans (binder_grow width (transform body (transform body (transform body bound))))
        (grow_mono width third)
      have extra := evolve_count_mono width
        (show count + count + count + 1 ≤ 3 * nodeBudget body + 4 + 3 * edgeBudget body by dsimp [count]; omega) bound
      exact Nat.le_trans grown extra
termination_by sizeOf expression

/-- Ordered child schedules share the initial numeric width and accumulated charges. -/
theorem many_bound (width : Nat) (expressions : List (Syntax Symbol Guard)) (bound : Nat)
    (fits : Many width expressions) :
    manyTransform expressions bound ≤ evolve width (manyNodes expressions + manyEdges expressions) bound := by
  cases expressions with
  | nil => simp only [manyTransform, manyNodes, manyEdges, Nat.add_zero, evolve]; exact Nat.le_refl _
  | cons first rest =>
      simp only [Many] at fits
      have own := transform_bound width first bound fits.1
      have tail := many_bound width rest (transform first bound) fits.2
      have composed := Nat.le_trans tail (evolve_mono width (manyNodes rest + manyEdges rest) own)
      rw [← evolve_add] at composed
      have count : manyNodes (first :: rest) + manyEdges (first :: rest) =
          (nodeBudget first + edgeBudget first) + (manyNodes rest + manyEdges rest) := by
        simp only [manyNodes, manyEdges]
        omega
      simpa only [manyTransform, count] using composed
termination_by sizeOf expressions

/-- Ordered raw rows pay for each edge before continuing from its returned bound. -/
theorem rows_bound (width : Nat) (expressions : List (EdgeSyntax Symbol Guard)) (bound : Nat)
    (fits : Rows width expressions) :
    rowsTransform expressions bound ≤ evolve width (rowNodes expressions + rowEdges expressions) bound := by
  cases expressions with
  | nil => simp only [rowsTransform, rowNodes, rowEdges, Nat.add_zero, evolve]; exact Nat.le_refl _
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          simp only [Rows] at fits
          have childrenBound := many_bound width children bound fits.2.1
          have edgeBound := Nat.le_trans (inflate_bound width children.length (manyTransform children bound) fits.1)
            (grow_mono width childrenBound)
          have tail := rows_bound width rest (inflate children.length (manyTransform children bound)) fits.2.2
          have composed := Nat.le_trans tail (evolve_mono width (rowNodes rest + rowEdges rest) edgeBound)
          change rowsTransform rest (inflate children.length (manyTransform children bound)) ≤
            evolve width (rowNodes rest + rowEdges rest)
              (evolve width (manyNodes children + manyEdges children + 1) bound) at composed
          rw [← evolve_add] at composed
          have count : rowNodes (.mk symbol guard children :: rest) + rowEdges (.mk symbol guard children :: rest) =
              (manyNodes children + manyEdges children + 1) + (rowNodes rest + rowEdges rest) := by
            simp only [rowNodes, rowEdges]
            omega
          simpa only [rowsTransform, count] using composed
termination_by sizeOf expressions
end

end MicroCFTA.InternedFreshOrdinaryUniformMass
