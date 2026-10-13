import MicroCFTA.InternedRootProfile
import MicroCFTA.InternedNestedConstruction

/-!
# Pure root profiles for complete constructor syntax

This interpretation records root references or an opaque result. A smart
binder removes its fresh symbolic local. A raw binder is opaque. External
reference maps commute with interpretation, including maps that identify
different captured names. This is a pure model; source cache correspondence
is a separate obligation.
-/
namespace MicroCFTA.InternedProfileSemantics
open InternedNestedConstruction

/-- A generic root profile can use symbolic locals in addition to source reference names. -/
abbrev Abstract (Atom : Type) := Option (List Atom)

/-- Change each literal root name while preserving opacity. -/
def mapNames (function : Atom → Other) (value : Abstract Atom) : Abstract Other := value.map (List.map function)

/-- Union combines reference alternatives and preserves an opaque operand. -/
def combine : Abstract Atom → Abstract Atom → Abstract Atom
  | some first, some second => some (first ++ second)
  | _, _ => none

/-- Combine all root alternatives in source order. -/
def combineMany : List (Abstract Atom) → Abstract Atom
  | [] => some []
  | first :: rest => combine first (combineMany rest)

/-- Only a pure empty reference list denotes an empty result. -/
def isEmpty : Abstract Atom → Bool
  | some [] => true
  | _ => false

/-- Leaving a smart binder removes its symbolic local from pure root alternatives. -/
def lower : Abstract (Sum Unit Atom) → Abstract Atom
  | none => none
  | some names => some (names.filterMap (fun name => match name with | .inl _ => none | .inr value => some value))

mutual
/-- Interpret the complete source syntax without selecting canonical cache identities. -/
def evaluate {Atom : Type} (expression : Syntax Symbol Guard) (environment : List (Abstract Atom)) : Abstract Atom :=
  match expression with
  | .empty => some []
  | .var index => environment[index]?.getD (some [])
  | .node edges => if evaluateEdges edges environment then none else some []
  | .union members => combineMany (evaluateMany members environment)
  | .binder false _ => none
  | .binder true body => lower (evaluate body (some [.inl ()] :: environment.map (mapNames Sum.inr)))
termination_by sizeOf expression

/-- Retain the source order of abstract child computations. -/
def evaluateMany {Atom : Type} (expressions : List (Syntax Symbol Guard)) (environment : List (Abstract Atom)) : List (Abstract Atom) :=
  match expressions with
  | [] => []
  | first :: rest => evaluate first environment :: evaluateMany rest environment
termination_by sizeOf expressions

/-- A node is nonempty when at least one declared edge has no empty child. -/
def evaluateEdges {Atom : Type} (edges : List (EdgeSyntax Symbol Guard)) (environment : List (Abstract Atom)) : Bool :=
  match edges with
  | [] => false
  | .mk _ _ children :: rest => (evaluateMany children environment).all (fun child => !isEmpty child) || evaluateEdges rest environment
termination_by sizeOf edges
end

/-- Mapping literal names preserves the empty decision. -/
theorem isEmpty_map (function : Atom → Other) (value : Abstract Atom) : isEmpty (mapNames function value) = isEmpty value := by
  cases value with
  | none => rfl
  | some names => cases names <;> rfl

/-- Mapping names commutes with one abstract union. -/
theorem combine_map (function : Atom → Other) (first second : Abstract Atom) :
    combine (mapNames function first) (mapNames function second) = mapNames function (combine first second) := by
  cases first <;> cases second <;> simp [combine, mapNames]

/-- Mapping names commutes with all ordered union operands. -/
theorem combineMany_map (function : Atom → Other) (values : List (Abstract Atom)) :
    combineMany (values.map (mapNames function)) = mapNames function (combineMany values) := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, combineMany, ih, combine_map]

/-- A map on external names leaves the distinguished fresh local unchanged. -/
theorem lower_map (function : Atom → Other) (value : Abstract (Sum Unit Atom)) :
    lower (mapNames (Sum.map id function) value) = mapNames function (lower value) := by
  cases value with
  | none => rfl
  | some names =>
      simp only [mapNames, Option.map_some, lower]
      congr 1
      induction names with
      | nil => rfl
      | cons first rest ih => cases first <;> simp [ih]

/-- Extending the scope by one local commutes with every external-name map. -/
theorem local_map (function : Atom → Other) (environment : List (Abstract Atom)) :
    (some [Sum.inl ()] :: environment.map (mapNames Sum.inr)).map (mapNames (Sum.map id function)) =
      some [.inl ()] :: (environment.map (mapNames function)).map (mapNames Sum.inr) := by
  simp [mapNames, List.map_map, Function.comp_def]

mutual
/-- Full syntax interpretation commutes with arbitrary maps of external names. -/
theorem evaluate_map {Atom Other : Type} (function : Atom → Other) (expression : Syntax Symbol Guard)
    (environment : List (Abstract Atom)) :
    evaluate expression (environment.map (mapNames function)) = mapNames function (evaluate expression environment) := by
  cases expression with
  | empty => simp [evaluate, mapNames]
  | var index =>
      rw [evaluate, evaluate]
      cases found : environment[index]? <;> simp [List.getElem?_map, found, mapNames]
  | node edges =>
      rw [evaluate, evaluate, evaluateEdges_map function edges environment]
      cases evaluateEdges edges environment <;> rfl
  | union members =>
      rw [evaluate, evaluate, evaluateMany_map function members environment, combineMany_map]
  | binder smart body =>
      cases smart with
      | false => simp [evaluate, mapNames]
      | true =>
          rw [evaluate, evaluate, ← local_map function environment,
            evaluate_map (Sum.map id function) body _, lower_map]
termination_by sizeOf expression

/-- The map law retains the order of every actual abstract child profile. -/
theorem evaluateMany_map {Atom Other : Type} (function : Atom → Other) (expressions : List (Syntax Symbol Guard))
    (environment : List (Abstract Atom)) :
    evaluateMany expressions (environment.map (mapNames function)) = (evaluateMany expressions environment).map (mapNames function) := by
  cases expressions with
  | nil => simp [evaluateMany]
  | cons first rest => simp only [evaluateMany, evaluate_map function first environment, evaluateMany_map function rest environment, List.map_cons]
termination_by sizeOf expressions

/-- Renaming external references cannot change source empty-child decisions in the pure interpretation. -/
theorem evaluateEdges_map {Atom Other : Type} (function : Atom → Other) (edges : List (EdgeSyntax Symbol Guard))
    (environment : List (Abstract Atom)) :
    evaluateEdges edges (environment.map (mapNames function)) = evaluateEdges edges environment := by
  cases edges with
  | nil => simp [evaluateEdges]
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [evaluateEdges, evaluateMany_map function children environment, evaluateEdges_map function rest environment,
            List.all_map, Function.comp_def, isEmpty_map]
termination_by sizeOf edges
end

end MicroCFTA.InternedProfileSemantics
