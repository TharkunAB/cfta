import MicroCFTA.SourceInternedIntersectionRowsCompletion
import MicroCFTA.IntersectionFlatMemoKeyPhysical

/-!
# Empty, closed-self, and ordered ordinary intersection dispatch

These branches use the stored source reference and free-name metadata.
Empty operands return first. A closed self-call returns its existing record.
The ordinary branch orders node identities before the hash join. The domain
reader below retains reset and repeated-pair decisions explicitly.
-/
namespace MicroCFTA.SourceInternedIntersectionDispatch
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency InternedFreshProbeKeys
open SourceInternedIntersectionRows

/-- The ordinary-node part of the source constructor-tag order. -/
def greater (left right : Value Symbol Unit) : Bool :=
  match left, right with
  | .node first .., .node second .. => decide (second.identity < first.identity)
  | _, _ => false

/-- Either source operand is the literal EmptyNode. -/
def hasEmpty (pair : Value Symbol Unit × Value Symbol Unit) : Bool :=
  pair.1.referenceOf == .empty || pair.2.referenceOf == .empty

/-- Source self-intersection checks canonical equality and cached closedness. -/
def closedSelf (pair : Value Symbol Unit × Value Symbol Unit) : Bool :=
  pair.1.referenceOf == pair.2.referenceOf && pair.1.free.isEmpty

/-- Physical reference equality identifies the complete payload at a coherent cache. -/
theorem self_record (state : State Symbol Unit) (facts : Facts state)
    (pair : Value Symbol Unit × Value Symbol Unit) (inputs : Inputs state pair)
    (same : closedSelf pair = true) : pair.1 = pair.2 := by
  have references : pair.1.referenceOf = pair.2.referenceOf := by
    simp only [closedSelf, Bool.and_eq_true, beq_iff_eq] at same
    exact same.1
  exact resident_reference_injective state facts.coherent _ _ inputs.1.resident inputs.2.resident references

/-- Swapping a strictly ordered ordinary pair cannot require another swap. -/
theorem greater_swap (left right : Value Symbol Unit) (swap : greater left right = true) :
    greater right left = false := by
  cases left <;> cases right <;> simp_all [greater] <;> omega

/-- Operand normalization retains the two complete records and changes only their order. -/
def ordered (pair : Value Symbol Unit × Value Symbol Unit) : Value Symbol Unit × Value Symbol Unit :=
  if greater pair.1 pair.2 then (pair.2, pair.1) else pair

/-- Ordered child construction after source empty and self shortcuts. -/
def dispatch [DecidableEq Symbol] : Nat → (Value Symbol Unit × Value Symbol Unit) → Work Symbol Unit (Value Symbol Unit)
  | 0, _ => .pure .empty
  | fuel + 1, pair =>
      if hasEmpty pair then .pure .empty
      else if closedSelf pair then .pure pair.1
      else node (dispatch fuel) (nodeEdges (ordered pair).1) (nodeEdges (ordered pair).2)

/-- Empty operands return before self comparison and before any constructor effects. -/
theorem empty_dispatch [DecidableEq Symbol] (fuel : Nat) (pair : Value Symbol Unit × Value Symbol Unit)
    (empty : hasEmpty pair = true) : dispatch (fuel + 1) pair = .pure .empty := by
  simp [dispatch, empty]

/-- A closed equal pair returns its literal existing record and leaves both caches unchanged. -/
theorem self_dispatch [DecidableEq Symbol] (fuel : Nat) (pair : Value Symbol Unit × Value Symbol Unit)
    (nonempty : hasEmpty pair = false) (same : closedSelf pair = true) (state : State Symbol Unit) :
    run (dispatch (fuel + 1) pair) state = (pair.1, state) := by
  simp [dispatch, nonempty, same, run]

/-- Source domain decisions before the ordinary payload branch. -/
inductive Decision where
  | empty | reset | self | swap | repeated | ordinary
  deriving DecidableEq, Repr

/-- The node identity is used only after ordinary nonempty operands are established. -/
def ordinaryIdentity : Value Symbol Unit → Nat
  | .node entry .. => entry.identity
  | _ => 0

/-- Source domain lookup retains the reset-before-self and sort-before-repeat guard order. -/
def decision (domain : IntersectionFlatMemoKeyDomain.DomainKey) (pair : Value Symbol Unit × Value Symbol Unit) : Decision :=
  if hasEmpty pair then .empty
  else if pair.1.free.isEmpty && pair.2.free.isEmpty && !domain.free.isEmpty then .reset
  else if closedSelf pair then .self
  else if greater pair.1 pair.2 then .swap
  else if (ordinaryIdentity pair.1,
      ordinaryIdentity pair.2) ∈ domain.seen then .repeated
  else .ordinary

end MicroCFTA.SourceInternedIntersectionDispatch
