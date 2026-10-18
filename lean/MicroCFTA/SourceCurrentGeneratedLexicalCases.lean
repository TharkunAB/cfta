import MicroCFTA.SourceCurrentRetainedMuDirectedCase

/-!
# Actual lexical calls for the source-generated relation

The lexical input relation supplies the existing ordered slot relation.
Actual variable execution then gives both generated directions. Fixed
captures use equal maps on their free names. Reference slots use their
resolved generated pairs. No observation law is an input to these proofs.
Root self filtering remains a separate operation.
-/
namespace MicroCFTA.SourceCurrentGeneratedLexicalCases
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment)
open SourceCurrentRetainedMuDirectedCase (Generated Inputs)
open SourceCurrentReaderReplacementSlots (Paired Slot)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The generated lexical spine supplies both resolved slot directions in source order. -/
theorem paired (reader : State Symbol Guard) (first second : Environment Symbol Guard)
    (left right : List (Value Symbol Guard)) (inputs : Inputs reader first second left right) :
    Paired (fun a b => Generated reader a b ∧ Generated reader b a) first second left right := by
  induction left generalizing right with
  | nil => cases inputs; exact .nil
  | cons value rest ih =>
      cases inputs with
      | reference head backward tail => exact .cons ⟨head,backward⟩ (ih _ tail)
      | fixed value agree tail =>
          refine .cons ?_ (ih _ tail)
          cases value with
          | reference name =>
              change Generated reader ((first name).getD _) ((second name).getD _) ∧
                Generated reader ((second name).getD _) ((first name).getD _)
              rw [agree name (by simp [Value.free])]
              exact ⟨.refl _,.refl _⟩
          | empty | node | union | mu => exact ⟨rfl,agree⟩

/-- Actual variable reconstruction retains both generated directions and the same output heap. -/
theorem variable_call (reader : State Symbol Guard) (coherent : Coherent reader)
    (first second : Environment Symbol Guard) (left right : List (Value Symbol Guard))
    (inputs : Inputs reader first second left right) (available : Values reader left) (index : Nat)
    (result other : Value Symbol Guard) (after later : State Symbol Guard)
    (called : (build (.var index) left reader).bind (fun value current => execute value first current) =
      .done result after)
    (returned : (build (.var index) right reader).bind (fun value current => execute value second current) =
      .done other later) :
    (Generated reader result other ∧ Generated reader other result) ∧ after = later := by
  exact SourceCurrentReaderReplacementSlots.reference
    (fun a b => Generated reader a b ∧ Generated reader b a)
    (fun value => ⟨.refl value,.refl value⟩) reader coherent first second left right
    (paired reader first second left right inputs) available index result other after later called returned

end MicroCFTA.SourceCurrentGeneratedLexicalCases
