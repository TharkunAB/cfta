import MicroCFTA.SourceSynthesisUniverseRowTransform

/-!
# Composition of the actual universe child substitutions

The first input map replaces RecU with the diagonal cutoff.
The second input map replaces that cutoff with the probe reference.
Closed marker records remain unchanged in both maps.
The composite map has the same complete children as the direct probe map.
These equations do not assert callback completion or canonical row order.
-/
namespace MicroCFTA.SourceSynthesisUniverseProbeChildren
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedStoredSubstitution InternedStoredSubstitutionScope
open InternedStoredSubstitutionRebind SourceRecursiveIntersectionControl

variable {Symbol Guard : Type}

/-- The two actual input maps agree with the direct map on each source child. -/
theorem input_compose (uId : Nat) (probe : Reference) (child : Value Symbol Guard)
    (kind : child.free = [] ∨ child = .reference (.interned uId)) :
    input (replacement (.intersection (pair uId uId).1 (pair uId uId).2) (.reference probe))
        (input (replacement (.interned uId) (repeatedValue (pair uId uId))) child) =
      input (replacement (.interned uId) (.reference probe)) child := by
  rcases kind with closed | rfl
  · rw [input_closed child (replacement (.interned uId) (repeatedValue (pair uId uId))) closed]
    rw [input_closed child
      (replacement (.intersection (pair uId uId).1 (pair uId uId).2) (.reference probe)) closed]
    exact (input_closed child (replacement (.interned uId) (.reference probe)) closed).symm
  · simp [input, replacement, repeatedValue]

/-- Source child order and complete closed marker records survive probe composition. -/
theorem children_compose (uId : Nat) (probe : Reference) (marker : Value Symbol Guard)
    (source : EdgeValue Symbol Guard) (closed : marker.free = [])
    (kinds : ∀ child ∈ source.children, child = marker ∨ child = .reference (.interned uId)) :
    (SourceSynthesisUniverseRowTransform.children uId source).map
        (input (replacement (.intersection (pair uId uId).1 (pair uId uId).2) (.reference probe))) =
      source.children.map (input (replacement (.interned uId) (.reference probe))) := by
  unfold SourceSynthesisUniverseRowTransform.children
  rw [List.map_map]
  apply List.map_congr_left
  intro child member
  apply input_compose uId probe child
  rcases kinds child member with same | same
  · left
    rw [same]
    exact closed
  · exact Or.inr same

/-- Both child maps give the same literal edge request, including its complete key. -/
theorem makeEdge_compose (top : Guard) (uId : Nat) (probe : Reference) (marker : Value Symbol Guard)
    (source : EdgeValue Symbol Guard) (closed : marker.free = [])
    (kinds : ∀ child ∈ source.children, child = marker ∨ child = .reference (.interned uId)) :
    makeEdge source.entry.key.symbol top
        ((SourceSynthesisUniverseRowTransform.children uId source).map
          (input (replacement (.intersection (pair uId uId).1 (pair uId uId).2) (.reference probe)))) =
      makeEdge source.entry.key.symbol top
        (source.children.map (input (replacement (.interned uId) (.reference probe)))) := by
  rw [children_compose uId probe marker source closed kinds]

end MicroCFTA.SourceSynthesisUniverseProbeChildren
