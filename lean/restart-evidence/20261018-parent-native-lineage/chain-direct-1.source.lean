import MicroCFTA.SourceCurrentPositionalOriginDescent

/-!
# Finite positive continuation chains at a fixed child index

Each step may reconstruct a different result. Its next anchor is exactly
the selected retained child. Structural mass decreases between those
explicit anchors. No initial-source occurrence map is needed for this
conditional chain theorem. Actual outer executions require a separate
proof that their consecutive anchors satisfy this relation.
-/
namespace MicroCFTA.SourceCurrentPositionalOriginChain
open InternedConstructorTemplates InternedEdgeResidency
open SourceCurrentActualRequiredRowOrigins (Link)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "mass" => InternedValueMass.value

/-- A step selects the next anchor from a positive row of an arbitrary linked reconstruction. -/
def Below (childIndex : Nat) (next anchor : Node) : Prop :=
  ∃ result row records, Link childIndex anchor result ∧ row ∈ nodeEdges result ∧
    SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records) ∧
    records ≠ [] ∧ row.children[childIndex]? = some next

/-- Each consecutive anchor has strictly smaller complete structural mass. -/
theorem mass_lt {childIndex : Nat} {next anchor : Node} (step : Below childIndex next anchor) :
    mass next < mass anchor := by
  obtain ⟨result,row,records,link,member,positive,nonempty,present⟩ := step
  obtain ⟨_,_,_,_,_,_,smaller⟩ :=
    SourceCurrentPositionalOriginDescent.continuation link member positive nonempty present
  exact smaller

/-- Fixed-index positive continuation steps form a well-founded relation. -/
theorem wellFounded (childIndex : Nat) : WellFounded (Below childIndex) :=
  Subrelation.wf (fun _ _ actual => mass_lt actual) (measure mass).wf

/-- A finite consecutive chain consumes one unit of its initial anchor mass at every step. -/
theorem budget (childIndex : Nat) (anchors : Nat → Node) (count : Nat)
    (steps : ∀ index, index < count → Below childIndex (anchors (index + 1)) (anchors index)) :
    mass (anchors count) + count ≤ mass (anchors 0) := by
  induction count with
  | zero => omega
  | succ count ih =>
    have earlier := ih (fun index inside => steps index (by omega))
    have last := mass_lt (steps count (by omega))
    omega

/-- No infinite sequence can supply these exact consecutive positive continuation steps. -/
theorem no_infinite (childIndex : Nat) (anchors : Nat → Node)
    (steps : ∀ index, Below childIndex (anchors (index + 1)) (anchors index)) : False := by
  have bounded := budget childIndex anchors (mass (anchors 0)) (fun index _ => steps index)
  have positive := InternedValueMass.value_pos (anchors (mass (anchors 0)))
  omega

end MicroCFTA.SourceCurrentPositionalOriginChain
