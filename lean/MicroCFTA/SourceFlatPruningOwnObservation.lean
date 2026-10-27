import MicroCFTA.SourceFlatPruningCachedOwn

/-!
# The actual singleton own-prefix payload

The consumer retains every optional staged action. The projected native child
and suspended bucket lists agree without comparing action functions.
-/

namespace MicroCFTA.SourceFlatPruningCachedOwn

open EnumerationState EnumerationFlatCached InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "FlatStage" => Value Symbol Constraint × List Suspended ×
  Option (EnumerationFlatState.Action Symbol Constraint (Fragments.Fragment Symbol))
local notation "OldStage" => Value Symbol Constraint × List Suspended ×
  Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))

/-- Related stages have the same ordered native values and suspended buckets. -/
theorem staged_inputs_eq {flat : List FlatStage} {earlier : List OldStage}
    (related : Language.All₂ StageRelated flat earlier) :
    flat.map (fun stage => (stage.1, stage.2.1)) =
      earlier.map (fun stage => (stage.1, stage.2.1)) := by
  induction related with
  | nil => rfl
  | cons head _ ih =>
      simp only [List.map_cons, head.1, head.2.1, ih]

/-- An actual old singleton determines the full flat payload and its projected inputs. -/
theorem prepare_completed
    {flat : Cached Symbol Constraint}
    {earlier : EnumerationExpandableIndex.Cached Symbol Constraint}
    (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (symbol : Symbol) (oldStaged : List OldStage) (residual : Option Constraint)
    (oldMiddle : EnumerationExpandableIndex.Cached Symbol Constraint)
    (observed : SourcePruningEnumerationCachedOwn.prepare heap scs edge earlier =
      some [((symbol, oldStaged, residual), oldMiddle)]) :
    ∃ (flatStaged : List FlatStage) (flatMiddle : Cached Symbol Constraint),
      prepare heap scs edge flat = some [((symbol, flatStaged, residual), flatMiddle)] ∧
      flatStaged.map (fun stage => (stage.1, stage.2.1)) =
        oldStaged.map (fun stage => (stage.1, stage.2.1)) ∧
      Related flatMiddle oldMiddle ∧ Language.All₂ StageRelated flatStaged oldStaged := by
  have compared := prepare_related related heap scs edge
  rw [observed] at compared
  cases actual : prepare heap scs edge flat with
  | none =>
      simp only [actual, PreparedRelated] at compared
  | some rows =>
      simp only [actual, PreparedRelated] at compared
      change Language.All₂
        (fun left right => left.1.1 = right.1.1 ∧
          Language.All₂ StageRelated left.1.2.1 right.1.2.1 ∧
          left.1.2.2 = right.1.2.2 ∧ Related left.2 right.2)
        rows [((symbol, oldStaged, residual), oldMiddle)] at compared
      have length := Language.All₂.length_eq compared
      cases rows with
      | nil => cases compared
      | cons row rest =>
          cases rest with
          | cons _ _ =>
              simp only [List.length_cons, List.length_nil] at length
              omega
          | nil =>
              cases compared with
              | cons fields _tail =>
                  obtain ⟨⟨actualSymbol, flatStaged, actualResidual⟩, flatMiddle⟩ := row
                  obtain ⟨symbolSame, stages, residualSame, caches⟩ := fields
                  change actualSymbol = symbol at symbolSame
                  change actualResidual = residual at residualSame
                  subst actualSymbol
                  subst actualResidual
                  exact ⟨flatStaged, flatMiddle, rfl, staged_inputs_eq stages, caches, stages⟩

end MicroCFTA.SourceFlatPruningCachedOwn
