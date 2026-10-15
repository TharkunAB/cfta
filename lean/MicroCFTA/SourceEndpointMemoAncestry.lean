import MicroCFTA.SourceEndpointReachability
import MicroCFTA.InternedProbeProvenance

/-!
# Physical key separation for descendant-helper calls

The helper can recurse through ordinary children and union members when the
cached depth is positive. Mu stops the helper. Earlier true children can stop
a scan before a possible call. These relations do not model memo publication,
pending cells, or concurrent calls.
-/
namespace MicroCFTA.SourceEndpointMemoAncestry
open Cache InternedBinderProtocol InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance

/-- A possible recursive helper call retains an original child of a positive-depth input. -/
inductive Step : Value Symbol Guard → Value Symbol Guard → Prop where
  | node {entry : Interned NodeKey} {edges : List (EdgeValue Symbol Guard)}
      {depth : Nat} {free : List Reference} {edge : EdgeValue Symbol Guard} {child : Value Symbol Guard}
      (positive : depth ≠ 0) (selected : edge ∈ edges) (member : child ∈ edge.children) :
      Step child (.node entry edges depth free)
  | union {entry : Interned NodeKey} {members : List (Value Symbol Guard)}
      {depth : Nat} {free : List Reference} {child : Value Symbol Guard}
      (positive : depth ≠ 0) (member : child ∈ members) :
      Step child (.union entry members depth free)

/-- A nonempty chain of possible recursive helper calls follows the original stored records. -/
inductive Descendant : Value Symbol Guard → Value Symbol Guard → Prop where
  | single (step : Step child parent) : Descendant child parent
  | tail (path : Descendant child middle) (step : Step middle parent) : Descendant child parent

variable {Symbol Guard : Type} {child parent middle ancestor : Value Symbol Guard}
variable {heap : State Symbol Guard}

/-- Every possible recursive call reads a strict subrecord of its parent. -/
theorem Step.smaller [SizeOf Symbol] [SizeOf Guard] (step : Step child parent) :
    sizeOf child < sizeOf parent := by
  cases step with
  | @node entry edges depth free edge child positive selected member =>
      have outer := List.sizeOf_lt_of_mem selected
      cases edge with
      | mk edgeEntry children =>
          have inner := List.sizeOf_lt_of_mem member
          simp only [Value.node.sizeOf_spec, EdgeValue.mk.sizeOf_spec, EdgeValue.children] at *
          omega
  | union positive member =>
      have smaller := List.sizeOf_lt_of_mem member
      simp only [Value.union.sizeOf_spec]
      omega

/-- Each nonempty chain strictly decreases the stored-record size. -/
theorem Descendant.smaller [SizeOf Symbol] [SizeOf Guard] (path : Descendant child ancestor) :
    sizeOf child < sizeOf ancestor := by
  induction path with
  | single step => exact step.smaller
  | tail path step smaller => exact Nat.lt_trans smaller step.smaller

/-- Each possible helper child remains available in the same physical heap. -/
theorem Step.available (step : Step child parent) (available : Available heap parent) :
    Available heap child := by
  cases step with
  | node positive selected member =>
      exact available.children _ (List.mem_flatMap.mpr ⟨_, selected, member⟩)
  | union positive member => exact available.children _ member

/-- All records on a possible helper-call chain remain available. -/
theorem Descendant.available (path : Descendant child ancestor) :
    Available heap ancestor → Available heap child := by
  induction path with
  | single step => exact step.available
  | tail path step childAvailable => exact fun available => childAvailable (step.available available)

/-- A coherent available child cannot use its parent's physical memo key. -/
theorem Step.reference_ne (step : Step child parent) (coherent : Coherent heap)
    (available : Available heap parent) : child.referenceOf ≠ parent.referenceOf := by
  intro same
  have equal := InternedFreshProbeKeys.resident_reference_injective heap coherent child parent
    (step.available available).resident available.resident same
  have smaller := step.smaller
  rw [equal] at smaller
  exact Nat.lt_irrefl _ smaller

/-- No descendant helper call can demand an active ancestor's physical key on available inputs. -/
theorem Descendant.reference_ne (path : Descendant child ancestor) (coherent : Coherent heap)
    (available : Available heap ancestor) : child.referenceOf ≠ ancestor.referenceOf := by
  intro same
  have equal := InternedFreshProbeKeys.resident_reference_injective heap coherent child ancestor
    (path.available available).resident available.resident same
  have smaller := path.smaller
  rw [equal] at smaller
  exact Nat.lt_irrefl _ smaller

end MicroCFTA.SourceEndpointMemoAncestry
