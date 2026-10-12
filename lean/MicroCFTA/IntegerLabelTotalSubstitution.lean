import MicroCFTA.IntegerLabelCodec
import MicroCFTA.FormulaTotalSubstitution

/-!
# Total source label specialization

The source uses the total Formula.substitute API. The earlier checked label
model still gives sufficient conditions for the finite settlement proofs.
This adapter proves that those successful results equal the current source
policy, and executes the total policy on all other formulas.
-/
namespace MicroCFTA.IntegerLabelTotalSubstitution
open FullSyntax IntegerLabelCodec

/-- Source exactLabel uses total substitution before the singleton query. -/
def exactLabel (point : List Int) (label : Symbol) : Symbol :=
  if symbolic label then
    let named := FormulaTotalSubstitution.substitute (replacements point) label.2
    (label.1, match LatticeSingleton.onlyPoint SourceGuards.valueName named with
      | none => named
      | some value => IntegerLiteral.refinement SourceGuards.valueName value)
  else label

/-- Every successful checked specialization gives the current total source result. -/
theorem checked_agrees (point : List Int) (label output : Symbol)
    (success : IntegerLabelCodec.exactLabel point label = .ok output) : exactLabel point label = output := by
  unfold IntegerLabelCodec.exactLabel at success
  unfold exactLabel
  split at success
  · rename_i opened
    rw [ite_eq_left opened]
    cases replaced : FormulaSubstitution.checked (replacements point) label.2 with
    | error error => simp [replaced, Bind.bind, Except.bind] at success
    | ok named =>
        rw [FormulaTotalSubstitution.checked_agrees _ _ _ replaced]
        cases singleton : LatticeSingleton.onlyPoint SourceGuards.valueName named <;>
          simpa [replaced, singleton, Bind.bind, Except.bind, Pure.pure, Except.pure] using success
  · rename_i closed
    rw [ite_eq_right closed]
    exact Except.ok.inj success

/-- Total specialization always retains the constructor name. -/
theorem exactLabel_name (point : List Int) (label : Symbol) : (exactLabel point label).1 = label.1 := by
  unfold exactLabel
  split <;> rfl

/-- Every current specialization passes the existing label matcher, without a checked-success premise. -/
theorem exactLabel_matches (point : List Int) (label : Symbol) : fills label (exactLabel point label) = true := by
  by_cases opened : symbolic label = true
  · simp [fills, opened, exactLabel_name]
  · have closed : symbolic label = false := by simpa using opened
    simp [exactLabel, fills, closed]

end MicroCFTA.IntegerLabelTotalSubstitution
