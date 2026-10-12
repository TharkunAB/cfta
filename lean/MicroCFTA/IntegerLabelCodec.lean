import MicroCFTA.IntegerTermCodec
import MicroCFTA.IntegerLiteral
import MicroCFTA.SourceFormula

/-!
# Integer labels and the source point reader

Generated leaves use the canonical value equality. `onlyPoint` is proved to
read that equality for every integer. Label specialization keeps the source
constructor name and uses a restricted checked substitution model before
singleton refinement replacement. `IntegerLabelTotalSubstitution` models the
current total source API and proves agreement on every checked success.
The checked error branch is not a current source exception.
-/
namespace MicroCFTA.IntegerLabelCodec
open FullSyntax

/-- The complete source constructor label and its refinement. -/
abbrev Symbol := String × Formula

/-- One internal open coordinate name, in the source's zero-based order. -/
def integerName (index : Nat) : String := "__microcfta_integer_" ++ toString index

/-- The source prefix test includes all names beginning with the reserved prefix. -/
def isIntegerName (name : String) : Bool := "__microcfta_integer_".toList.isPrefixOf name.toList

/-- A label is open when its refinement names any internal coordinate. -/
def symbolic (label : Symbol) : Bool := (freeNames label.2).any isIntegerName

/-- Literal substitutions use the remaining point in left-to-right order. -/
def replacements (point : List Int) : List (String × Term) :=
  point.zipIdx.map (fun (value, index) => (integerName index, .lit value))

/-- The exact refinement and printed name of a generated integer leaf. -/
def integerSymbol (value : Int) : Symbol :=
  (toString value, IntegerLiteral.refinement SourceGuards.valueName value)

/-- Source closePoints reads the refinement, independently of the leaf's printed name. -/
def leafValue (symbol : Symbol) : Option Int := LatticeSingleton.onlyPoint SourceGuards.valueName symbol.2

/-- The actual public singleton counter supplies the literal reader equation. -/
theorem leafValue_integer (value : Int) : leafValue (integerSymbol value) = some value :=
  IntegerLiteral.onlyPoint_literal SourceGuards.valueName value

/-- The checked specialization model; success agrees with current source exactLabel. -/
def exactLabel (point : List Int) (label : Symbol) : Except FormulaSubstitution.Error Symbol :=
  if symbolic label then do
    let named ← FormulaSubstitution.checked (replacements point) label.2
    pure (label.1, match LatticeSingleton.onlyPoint SourceGuards.valueName named with
      | none => named
      | some value => IntegerLiteral.refinement SourceGuards.valueName value)
  else .ok label

/-- Closed labels are exactly unchanged. -/
theorem exactLabel_closed (point : List Int) (label : Symbol) (closed : symbolic label = false) :
    exactLabel point label = .ok label := by simp [exactLabel, closed]

/-- Label specialization cannot change the constructor name used by labelStaticMatching. -/
theorem exactLabel_name (point : List Int) (label output : Symbol)
    (success : exactLabel point label = .ok output) : output.1 = label.1 := by
  unfold exactLabel at success
  split at success
  · cases replaced : FormulaSubstitution.checked (replacements point) label.2 with
    | error error => simp [replaced, Bind.bind, Except.bind] at success
    | ok named =>
        simp only [replaced, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at success
        have name := congrArg (fun symbol : Symbol => symbol.1) success.symm
        exact name
  · cases success; rfl

/-- The actual compiler permits symbolic labels by name and checks closed labels completely. -/
def fills (original found : Symbol) : Bool :=
  if symbolic original then found.1 == original.1 else decide (found = original)

/-- Every successful exactLabel output passes the source's original-outcome label match. -/
theorem exactLabel_matches (point : List Int) (label output : Symbol)
    (success : exactLabel point label = .ok output) : fills label output = true := by
  by_cases openLabel : symbolic label = true
  · simp [fills, openLabel, exactLabel_name point label output success]
  · have closed : symbolic label = false := by simpa using openLabel
    have same : label = output := Except.ok.inj ((exactLabel_closed point label closed).symm.trans success)
    simp [fills, same]

/-- Singleton refinement replacement preserves all one-variable integer solutions of the substituted formula. -/
theorem singleton_refinement_exact (named : Formula) (value : Int)
    (singleton : LatticeSingleton.onlyPoint SourceGuards.valueName named = some value) (candidate : Int) :
    LatticeSingleton.Admits SourceGuards.valueName named candidate ↔
      LatticeSingleton.Admits SourceGuards.valueName (IntegerLiteral.refinement SourceGuards.valueName value) candidate := by
  rw [IntegerLiteral.admits_iff]
  have unique := LatticeSingleton.onlyPoint_sound SourceGuards.valueName named value singleton
  exact ⟨unique.2 candidate, fun same => same ▸ unique.1⟩

/-- The exact source leaf reader discharges the complete fill/read inverse. -/
theorem read_fill (specialize : List Int → Symbol → Symbol) (point : List Int)
    (term : Language.Term (RecipeCompile.FillLabel Symbol)) (valid : IntegerTermCodec.LeafHoles term)
    (dimension : point.length = RecipeCompile.holes term) :
    IntegerTermCodec.readPoint leafValue term (RecipeCompile.fillTerm integerSymbol specialize point term).2 = some point :=
  IntegerTermCodec.read_fill integerSymbol specialize leafValue leafValue_integer point term valid dimension

/-- Actual integer labels, extraction, singleton reading, and polynomial ranking round-trip at every valid rank. -/
theorem rank_decode (specialize : List Int → Symbol → Symbol)
    (names : List Name) (formula : Formula) (points : LatticeAPI.Points)
    (success : LatticeAPI.points names (FullSyntax.lowerFormula formula) = .ok points)
    (original : Language.Term (RecipeCompile.FillLabel Symbol)) (valid : IntegerTermCodec.LeafHoles original)
    (dimension : RecipeCompile.holes original = names.length) (rank : Fin (LatticeSelect.pointCount points.levels)) :
    IntegerTermCodec.rankTerm integerSymbol specialize leafValue points original
      (IntegerTermCodec.decodeTerm integerSymbol specialize points original rank) = some rank.val :=
  IntegerTermCodec.rank_decode integerSymbol specialize leafValue leafValue_integer names formula points success original valid dimension rank

end MicroCFTA.IntegerLabelCodec
