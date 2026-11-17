import MicroCFTA.SourceSynthesisFiniteTypeWitnesses
import MicroCFTA.EnumerationPendingAssignment

namespace MicroCFTA.SourceSynthesisTypeFragmentAssignment
open Language Fragments EnumerationState
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
set_option autoImplicit false

/- Note [Finite evaluation of structurally typed fragments]
The fragment grammar records Type constructor layouts and marked raw holes.
The snapshot hypothesis checks the exact representative lookup used by the
existing evaluator. It does not assert typing of the evaluator's output.
The outer induction follows the supplied evaluation fuel.
The inner induction follows the fragment grammar.
The arrow marker is fixed syntax. It is not an independently typed child.
No runtime evaluator, native operation, or worker budget changes here.
Actual source preservation of the marked role remains a separate producer.
-/

/-- A finite Type fragment has marked holes and the original Type constructor layouts. -/
inductive TypeFragment (catalog : List (String × Nat)) (marked : Nat → Prop) : Fragment Symbol → Prop where
  | hole (uv : Nat) (known : marked uv) : TypeFragment catalog marked (.hole uv)
  | leaf (name : String) (present : name ∈ ["var1", "var2", "var3", "var4"]) :
      TypeFragment catalog marked (.node (literal name) [])
  | node (name : String) (children : List (Fragment Symbol))
      (present : (name, children.length) ∈ catalog)
      (checked : ∀ child ∈ children, TypeFragment catalog marked child) :
      TypeFragment catalog marked (.node (literal name) children)
  | arrow (argument result : Fragment Symbol)
      (first : TypeFragment catalog marked argument) (second : TypeFragment catalog marked result) :
      TypeFragment catalog marked
        (.node (literal "->") [.node (literal "(->)") [], argument, result])

theorem TypeFragment.fill_type
    (catalog : List (String × Nat)) (marked : Nat → Prop)
    (assignment : Nat → Term Symbol) (fragment : Fragment Symbol)
    (wellFormed : TypeFragment catalog marked fragment)
    (holes : ∀ uv, marked uv → TypeIn catalog (assignment uv)) :
    TypeIn catalog (fill assignment fragment)
 := by
  induction wellFormed with
  | hole uv known =>
      exact holes uv known
  | leaf name present =>
      exact TypeIn.leaf name present
  | node name children present _checked ih =>
      change TypeIn catalog (.node (literal name) (children.map (fill assignment)))
      apply TypeIn.node name (children.map (fill assignment))
      · simpa only [List.length_map] using present
      · intro term member
        obtain ⟨child, listed, rfl⟩ := List.mem_map.mp member
        exact ih child listed
  | arrow argument result _first _second left right =>
      simpa only [fill, List.map_cons, List.map_nil] using
        TypeIn.arrow (fill assignment argument) (fill assignment result) left right

theorem evaluateSlotsWith_type
    (catalog : List (String × Nat)) (values : List (UVarValue Symbol))
    (roots : Nat → Nat) (marked : Nat → Prop) (base : Nat → Term Symbol)
    (baseTyped : ∀ uv, marked uv → TypeIn catalog (base uv))
    (expanded : ∀ uv, marked uv → ∀ fragment,
      values[roots uv]? = some (.enumerated fragment) → TypeFragment catalog marked fragment) :
    ∀ fuel uv, marked uv →
      TypeIn catalog (EnumerationPendingAssignment.evaluateSlotsWith values roots base fuel uv)
 := by
  intro fuel
  induction fuel with
  | zero =>
      intro uv known
      exact baseTyped uv known
  | succ fuel ih =>
      intro uv known
      cases stored : values[roots uv]? with
      | none =>
          simpa only [EnumerationPendingAssignment.evaluateSlotsWith, stored] using baseTyped uv known
      | some value =>
          cases value with
          | unenumerated node bucket | eliminated =>
              simpa only [EnumerationPendingAssignment.evaluateSlotsWith, stored] using baseTyped uv known
          | enumerated fragment =>
              simp only [EnumerationPendingAssignment.evaluateSlotsWith, stored]
              exact TypeFragment.fill_type catalog marked
                (EnumerationPendingAssignment.evaluateSlotsWith values roots base fuel) fragment
                (expanded uv known fragment stored) ih

end MicroCFTA.SourceSynthesisTypeFragmentAssignment
