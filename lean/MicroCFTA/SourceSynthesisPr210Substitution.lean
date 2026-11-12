import MicroCFTA.SourceSynthesisPr210TypeReflection

/-!
# Substitution through the PR210 constructor encoding

PR210 is merged. These laws use its reviewed head
79f74df2c3c9d3c864e57a960cb64c8c28883ec9.
Constructor escaping makes every encoded scheme satisfy AliasSafe.
Escaping also commutes with simultaneous raw substitution.
These laws do not assert universe admission or Program acceptance.
-/
namespace MicroCFTA.SourceSynthesisPr210Substitution
open SourceSynthesisTypeSyntax (Ty)
open SourceSynthesisPr210ConstructorEscape (escapeConstructor escapeConstructor_separate)
open SourceSynthesisPr210TypeReflection (encodeTy)
open SourceSynthesisTypeSubstitutionWitnesses (AliasSafe substTy)

/-- Every escaped scheme excludes constant leaves that look like variables. -/
theorem encodeTy_aliasSafe (scheme : Ty) : AliasSafe (encodeTy scheme) := by
  induction scheme using Ty.rec
    (motive_2 := fun types => ∀ typ ∈ types, AliasSafe (encodeTy typ)) with
  | tVar name =>
      simp only [encodeTy, AliasSafe]
  | tFun argument result first second =>
      simpa only [encodeTy, AliasSafe] using And.intro first second
  | tCons name arguments children =>
      simp only [encodeTy, AliasSafe]
      refine ⟨fun _empty => (escapeConstructor_separate name).1, ?_⟩
      intro child member
      obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
      exact children original included
  | nil =>
      rename_i typ member
      cases member
  | cons first rest own later =>
      rename_i typ member
      rcases List.mem_cons.mp member with rfl | member
      · exact own
      · exact later typ member

/-- Escape each selected image to commute encoding with simultaneous substitution. -/
theorem substTy_encodeTy (rho : String → Ty) (scheme : Ty) :
    substTy (fun name => encodeTy (rho name)) (encodeTy scheme) =
      encodeTy (substTy rho scheme) := by
  induction scheme using Ty.rec
    (motive_2 := fun types => ∀ typ ∈ types,
      substTy (fun name => encodeTy (rho name)) (encodeTy typ) =
        encodeTy (substTy rho typ)) with
  | tVar name =>
      simp only [encodeTy, substTy]
  | tFun argument result first second =>
      simp only [encodeTy, substTy]
      rw [first, second]
  | tCons name arguments children =>
      have mapped :
          (arguments.map encodeTy).map (substTy (fun name => encodeTy (rho name))) =
            (arguments.map (substTy rho)).map encodeTy := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro child member
        exact children child member
      simpa only [encodeTy, substTy] using
        congrArg (Ty.tCons (escapeConstructor name)) mapped
  | nil =>
      rename_i typ member
      cases member
  | cons first rest own later =>
      rename_i typ member
      rcases List.mem_cons.mp member with rfl | member
      · exact own
      · exact later typ member

end MicroCFTA.SourceSynthesisPr210Substitution
