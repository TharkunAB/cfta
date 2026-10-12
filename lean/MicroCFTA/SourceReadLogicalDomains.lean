import MicroCFTA.SourceCurrentReadTransport

/-!
# Ambient domains under planned-read name changes

The source avoid list contains constructor names at refinement-only paths.
Those names need not agree across planned reads. The proof retains their
sort-domain obligations. Each extra name must admit every value. Integer-only
environments meet this condition. No backend fresh-declaration acceptance is
assumed, and exact backend verdicts need not agree.
-/
namespace MicroCFTA.SourceReadLogicalDomains
open FullSyntax SourceFormula SourceObservations FormulaSubstitution
open SourceGuards (Guard Observations)

/-- Preserve the ambient obligations used by the existing quotient judgment. -/
def Ambient (sortDomain : Name → Value → Prop) (observed : Observations Formula)
    (guard : Guard Formula) (env : Name → Value) : Prop :=
  ∀ name ∈ SourceGuards.usedNames operations observed guard, sortDomain name (env name)

/-- A query admits both the guard's ambient values and its generated declarations. -/
def Admitted (sortDomain : Name → Value → Prop) (observed : Observations Formula)
    (guard : Guard Formula) (declarations : List (Name × Name)) (env : Name → Value) : Prop :=
  Ambient sortDomain observed guard env ∧ ∀ binding ∈ declarations, sortDomain binding.2 (env binding.1)

/-- Names present in only one avoid list must impose no additional sort restriction. -/
structure Compatible (sortDomain : Name → Value → Prop) (guard : Guard Formula)
    (first second : Observations Formula) : Prop where
  firstExtra : ∀ name ∈ SourceGuards.usedNames operations first guard,
    name ∉ SourceGuards.usedNames operations second guard → ∀ value, sortDomain name value
  secondExtra : ∀ name ∈ SourceGuards.usedNames operations second guard,
    name ∉ SourceGuards.usedNames operations first guard → ∀ value, sortDomain name value

/-- Equal avoid lists require no additional sort condition. -/
theorem compatible_equal (sortDomain : Name → Value → Prop) (guard : Guard Formula) (first second : Observations Formula)
    (equal : SourceGuards.usedNames operations first guard = SourceGuards.usedNames operations second guard) :
    Compatible sortDomain guard first second := by
  constructor <;> intro name member absent value
  · exact False.elim (absent (equal ▸ member))
  · exact False.elim (absent (equal.symm ▸ member))

/-- The all-integer environment has no additional sort restriction at a named value. -/
theorem integer_compatible (guard : Guard Formula) (first second : Observations Formula) :
    Compatible (fun (_ : Name) (_ : Int) => True) guard first second :=
  ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩

/-- Source ambient names are fixed by the actual fresh spelling map. -/
theorem forward_ambient (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (guard : Guard Formula) (first second : Observations Formula) (compatible : Compatible sortDomain guard first second)
    (env : Name → Value) (allowed : Ambient sortDomain second guard env) :
    Ambient sortDomain first guard (renamedEnvironment model env (SourceFreshTables.tableRenaming operations guard first second)) := by
  intro name member
  rw [FreshEnvironment.environment_names model env _ (SourceFreshTables.renaming_unique operations guard first second).1,
    SourceResolvedTables.fixed_used operations guard first second name member]
  by_cases shared : name ∈ SourceGuards.usedNames operations second guard
  · exact allowed name shared
  · exact compatible.firstExtra name member shared (env name)

/-- Target ambient names are absent from the source map's generated targets. -/
theorem reverse_fixed (guard : Guard Formula) (first second : Observations Formula) (name : Name)
    (used : name ∈ SourceGuards.usedNames operations second guard) :
    renameName ((SourceFreshTables.tableRenaming operations guard first second).map Prod.swap) name = name := by
  apply FormulaBinders.rename_absent
  simp only [List.map_map, Function.comp_def, Prod.fst_swap]
  rw [SourceFreshTables.tableRenaming, FreshEnvironment.fresh_targets]
  exact fun fresh => SourceActuals.fresh_avoids _ _ name fresh used

/-- The reverse spelling map also preserves every target ambient sort obligation. -/
theorem backward_ambient (sortDomain : Name → Value → Prop)
    (guard : Guard Formula) (first second : Observations Formula) (compatible : Compatible sortDomain guard first second)
    (env : Name → Value) (allowed : Ambient sortDomain first guard env) :
    Ambient sortDomain second guard (FreshEnvironment.liftEnvironment (SourceFreshTables.tableRenaming operations guard first second) env) := by
  intro name member
  rw [FreshEnvironment.liftEnvironment, reverse_fixed guard first second name member]
  by_cases shared : name ∈ SourceGuards.usedNames operations first guard
  · exact allowed name shared
  · exact compatible.secondExtra name member shared (env name)

/-- The derived finite query transport extends to the full ambient and declaration domains. -/
theorem entails_iff (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (guard : Guard Formula) (first second : Observations Formula) (compatible : Compatible sortDomain guard first second)
    (left right : SourceQueryTransport.Query)
    (transport : SourceQueryTransport.Transport model sortDomain (SourceFreshTables.tableRenaming operations guard first second) left right) :
    SourceEntailment.Entails model (Admitted sortDomain first guard left.declarations) left.antecedent left.consequent ↔
      SourceEntailment.Entails model (Admitted sortDomain second guard right.declarations) right.antecedent right.consequent := by
  constructor
  · intro proved env allowed assumed
    have related := transport.forward env
    exact related.2.2.mp (proved _ ⟨forward_ambient model sortDomain guard first second compatible env allowed.1,
      related.1.mpr allowed.2⟩ (related.2.1.mpr assumed))
  · intro proved env allowed assumed
    have related := transport.backward env
    exact related.2.2.mpr (proved _ ⟨backward_ambient sortDomain guard first second compatible env allowed.1,
      related.1.mp allowed.2⟩ (related.2.1.mp assumed))

/-- Mathematical query evidence transports without requiring equal backend verdicts. -/
theorem supports (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (guard : Guard Formula) (first second : Observations Formula) (compatible : Compatible sortDomain guard first second)
    (left right : SourceQueryTransport.Query)
    (transport : SourceQueryTransport.Transport model sortDomain (SourceFreshTables.tableRenaming operations guard first second) left right)
    (verdict : Guards.Verdict)
    (sound : Guards.Supports verdict (SourceEntailment.Entails model (Admitted sortDomain first guard left.declarations)
      left.antecedent left.consequent)) :
    Guards.Supports verdict (SourceEntailment.Entails model (Admitted sortDomain second guard right.declarations)
      right.antecedent right.consequent) := by
  have same := entails_iff model sortDomain guard first second compatible left right transport
  cases verdict with
  | yes => exact same.mp sound
  | no => exact fun proved => sound (same.mpr proved)
  | unknown => trivial

end MicroCFTA.SourceReadLogicalDomains
