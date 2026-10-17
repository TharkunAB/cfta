import MicroCFTA.SourceCurrentMemoMergeResourceControl

/-!
# Local resource certificates for general Merge instructions

Each constructor job derives its next heap bound from its current heap.
Sequential certificates check actual returned values at the reached heap.
Recursive calls retain their existing physical contract. Their numeric
bounds and strict request heights are separate obligations.
-/
namespace MicroCFTA.SourceCurrentMemoMergeResourceCertificate
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Effect Contract)
open SourceCurrentMemoMergeResourceControl (Fits primitiveGrowth)
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Literal work derives its next bound for every proved current heap bound. -/
def Checked (width : Nat) (clear : Guard → Bool) (code : Code Symbol Guard Output)
    (before : State Symbol Guard) (post : State Symbol Guard → Output → Prop) : Prop :=
  match code with
  | .pure value => post before value
  | .work job => Effect before (run job before).2 ∧
      (∀ bound, Fits bound before → Fits (primitiveGrowth width bound) (run job before).2) ∧
      post (run job before).2 (run job before).1
  | .select inputs => Values before inputs ∧ ClosedValues inputs ∧ ∀ fuel values after,
      SourceMergedSelection.select clear fuel inputs before = .done values after →
        Effect before after → post after values
  | .request input => Available before input ∧ ∀ output after,
      Effect before after → Contract input before output after → post after output
  | .bind first next => ∃ intermediate : State Symbol Guard → _ → Prop,
      Checked width clear first before intermediate ∧ ∀ value middle,
        Effect before middle → intermediate middle value → Checked width clear (next value) middle post

/-- Sequential certificates share the complete actual intermediate heap. -/
theorem bind_checked (width : Nat) (clear : Guard → Bool)
    (first : Code Symbol Guard First) (next : First → Code Symbol Guard Output) (before : State Symbol Guard)
    (intermediate : State Symbol Guard → First → Prop) (post : State Symbol Guard → Output → Prop)
    (checked : Checked width clear first before intermediate)
    (later : ∀ value middle, Effect before middle → intermediate middle value →
      Checked width clear (next value) middle post) :
    Checked width clear (.bind first next) before post := ⟨intermediate, checked, later⟩

/-- A stronger returned property can discharge a weaker returned property. -/
theorem Checked.mono {width : Nat} {clear : Guard → Bool} {code : Code Symbol Guard Output}
    {before : State Symbol Guard} {post nextPost : State Symbol Guard → Output → Prop}
    (checked : Checked width clear code before post)
    (implies : ∀ after output, post after output → nextPost after output) :
    Checked width clear code before nextPost := by
  induction code generalizing before with
  | pure => exact implies _ _ checked
  | work => exact ⟨checked.1, checked.2.1, implies _ _ checked.2.2⟩
  | select => exact ⟨checked.1, checked.2.1,
      fun fuel values after done effect => implies _ _ (checked.2.2 fuel values after done effect)⟩
  | request => exact ⟨checked.1, fun output after effect returned => implies _ _ (checked.2 output after effect returned)⟩
  | bind first next firstIH nextIH =>
      obtain ⟨intermediate, firstChecked, later⟩ := checked
      exact ⟨intermediate, firstChecked,
        fun value middle effect valid => nextIH value (later value middle effect valid) implies⟩

/-- Removing numeric work transfers retains the existing physical certificate. -/
theorem Checked.erase {width : Nat} {clear : Guard → Bool} {code : Code Symbol Guard Output}
    {before : State Symbol Guard} {post : State Symbol Guard → Output → Prop}
    (checked : Checked width clear code before post) :
    SourceCurrentMemoMergeEffects.Certified Contract clear code before post := by
  induction code generalizing before with
  | pure => exact checked
  | work => exact ⟨checked.1, checked.2.2⟩
  | select => exact checked
  | request => exact checked
  | bind first next firstIH nextIH =>
      obtain ⟨intermediate, firstChecked, later⟩ := checked
      exact ⟨intermediate, firstIH firstChecked,
        fun value middle effect valid => nextIH value (later value middle effect valid)⟩

end MicroCFTA.SourceCurrentMemoMergeResourceCertificate
