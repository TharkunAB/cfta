import MicroCFTA.SourceSynthesisUniverseProbeChildren

/-!
# Probe composition through any actual cutoff name

The source owner name maps to the selected cutoff name.
The cutoff then maps to the requested probe name.
Closed marker records keep their complete original values.
-/
set_option autoImplicit false

namespace MicroCFTA.SourceSynthesisUniverseProbeCutoffComposition
open InternedConstructorTemplates InternedBinderProtocol
open InternedStoredSubstitution InternedStoredSubstitutionScope
open InternedStoredSubstitutionRebind

variable {Symbol Guard : Type}

/-- The same source child map composes through any selected cutoff reference. -/
theorem input_compose_at (owner : Nat) (cutoff probe : Reference)
    (child : Value Symbol Guard)
    (kind : child.free = [] ∨ child = .reference (.interned owner)) :
    input (replacement cutoff (.reference probe))
        (input (replacement (.interned owner) (.reference cutoff)) child) =
      input (replacement (.interned owner) (.reference probe)) child := by
  rcases kind with closed | rfl
  · rw [input_closed child (replacement (.interned owner) (.reference cutoff)) closed]
    rw [input_closed child (replacement cutoff (.reference probe)) closed]
    exact (input_closed child (replacement (.interned owner) (.reference probe)) closed).symm
  · simp [input, replacement]

end MicroCFTA.SourceSynthesisUniverseProbeCutoffComposition

#print axioms MicroCFTA.SourceSynthesisUniverseProbeCutoffComposition.input_compose_at
