import MicroCFTA.InternedConstructorTemplates

/-!
# Root reference profiles

A profile records literal references below root union alternatives. An
ordinary node or Mu makes the profile opaque. List order and duplicate
counts do not affect profile equivalence.
-/
namespace MicroCFTA.InternedRootProfile
open InternedConstructorTemplates
open InternedBinderProtocol (Reference)

/-- None is opaque. A present list contains the root reference alternatives. -/
abbrev Profile := Option (List Reference)

/-- An opaque operand makes a union opaque; pure operands append their references. -/
def combine : Profile → Profile → Profile
  | some first, some second => some (first ++ second)
  | _, _ => none

mutual
/-- Ordinary nodes and Mu records are opaque at the union root. -/
def profile : Value Symbol Guard → Profile
  | .empty => some []
  | .reference name => some [name]
  | .node .. | .mu .. => none
  | .union _ members _ _ => many members
termination_by value => sizeOf value

/-- Root alternatives combine their literal references until an opaque operand occurs. -/
def many : List (Value Symbol Guard) → Profile
  | [] => some []
  | first :: rest => combine (profile first) (many rest)
termination_by values => sizeOf values
end

/-- Profiles agree on opacity and on their exact set of literal references. -/
def Equivalent (first second : Profile) : Prop :=
  (first = none ↔ second = none) ∧ ∀ name, name ∈ first.getD [] ↔ name ∈ second.getD []

/-- A pure profile represents exactly one literal reference. -/
def Single (name : Reference) (names : List Reference) : Prop :=
  name ∈ names ∧ ∀ other ∈ names, other = name

/-- Root self filtering preserves an all-self profile; otherwise it removes the selected name. -/
def normalize (name : Reference) : Profile → Profile
  | none => none
  | some names => some (if names.all (· == name) then names else names.filter (· != name))

/-- The raw profile of a callback consists of fixed captures and its optional argument. -/
def response (captured : List Reference) (uses : Bool) (name : Reference) : List Reference :=
  captured ++ if uses then [name] else []

/-- The source probe applies the actual root self normalization to that raw profile. -/
def probe (captured : List Reference) (uses : Bool) (name : Reference) : Profile :=
  normalize name (some (response captured uses name))

end MicroCFTA.InternedRootProfile
