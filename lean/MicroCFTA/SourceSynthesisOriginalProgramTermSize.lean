import MicroCFTA.SourceSynthesisProgramTermSize
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles
import MicroCFTA.InternedGuardedExecution

/-!
# Source component counts at the actual built root

The actual completed source build supplies its independent guarded meaning.
The source-size proof then supplies the Program projection of each accepted
typed term. The ordinary-symbol specialization uses the existing caller
syntax adapter and the symbol text. It has no name restriction.

These results do not supply enumeration depth, class order, ranks, native
word bounds, or a full Haskell execution correspondence. Different accepted
typed terms can still have the same projected Program.
-/
namespace MicroCFTA.SourceSynthesisOriginalProgramTermSize
open Language InternedConstructorTemplates InternedNestedFacts
open InternedProbeProvenance (Available)
open InternedNestedConstruction (Outcome)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw)
open SourceSynthesisProgramSourceSize (ProgramSize firstOrderRaw_size)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
open SourceSynthesisProgramTermSize (Program Projection toProgram accepted_projection)
open InternedGuardedLanguage (meaning)
open InternedFreshOrdinaryConstruction (build)

section Generic
variable {Symbol : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The same actual built root gives a counted projection of each accepted typed term. -/
theorem build_accepted (literal : String → Symbol) (text : Symbol → String)
    {count : Nat} {expression : Expression} (sized : ProgramSize count expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (mapSyntax literal expression) [] empty = .done value heap)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (term : Term Symbol) (accepted : meaning holds ambient value term) :
    ∃ program, Projection literal text term program ∧ toProgram literal text term = program ∧
      program.components = count := by
  have source : InternedGuardedSyntax.evaluate holds [] (mapSyntax literal expression) term := by
    rw [← InternedGuardedExecution.closed_language (mapSyntax literal expression) value heap built holds ambient]
    exact accepted
  obtain ⟨program, projected, counted⟩ := accepted_projection literal text sized holds [] term source
  exact ⟨program, projected, projected.toProgram_eq, counted⟩

/-- Successful source recursion derives the count at a supplied actual original build. -/
theorem firstOrderRaw_build_accepted (literal : String → Symbol) (text : Symbol → String)
    (lib : Library) (query : Query) (size : Int) (expression : Expression)
    (returned : firstOrderRaw lib query size = .ok expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (mapSyntax literal expression) [] empty = .done value heap)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (term : Term Symbol) (accepted : meaning holds ambient value term) :
    ∃ program, Projection literal text term program ∧ toProgram literal text term = program ∧
      program.components = size.toNat :=
  build_accepted literal text (firstOrderRaw_size lib query size expression returned)
    value heap built holds ambient term accepted

/-- Successful source recursion produces a completed build with its accepted-term count law. -/
theorem firstOrderRaw_complete (literal : String → Symbol) (text : Symbol → String)
    (lib : Library) (query : Query) (size : Int) (expression : Expression)
    (returned : firstOrderRaw lib query size = .ok expression) :
    ∃ value heap, build (mapSyntax literal expression) [] empty = .done value heap ∧
      Facts heap ∧ Available heap value ∧
      ∀ holds ambient term, meaning holds ambient value term →
        ∃ program, Projection literal text term program ∧ toProgram literal text term = program ∧
          program.components = size.toNat := by
  obtain ⟨value, heap, built⟩ :=
    InternedFreshOrdinaryClosedCompletion.closed_complete (mapSyntax literal expression)
  have verified := InternedFreshOrdinaryFacts.closed_verified (mapSyntax literal expression)
  refine ⟨value, heap, built, ?_, verified.result value heap built, ?_⟩
  · simpa only [built, Outcome.state] using verified.facts
  · intro holds ambient term accepted
    exact firstOrderRaw_build_accepted literal text lib query size expression returned value heap built
      holds ambient term accepted

end Generic

local notation "OrdinarySymbol" => SourceObservations.Label FullSyntax.Formula

/-- The actual ordinary-symbol caller build derives the repaired decoder and source count together. -/
theorem firstOrderRaw_ordinary [DecidableEq OrdinarySymbol]
    [DecidableEq (EdgeKey OrdinarySymbol Guard)] (lib : Library) (query : Query)
    (size : Int) (expression : Expression) (returned : firstOrderRaw lib query size = .ok expression) :
    ∃ (value : Value OrdinarySymbol Guard) (heap : State OrdinarySymbol Guard),
      build (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap ∧
      Facts heap ∧ Available heap value ∧
      ∀ holds ambient term, meaning holds ambient value term →
        ∃ program, Projection SourceSynthesisLabelProgramBuildRoles.literal Prod.fst term program ∧
          toProgram SourceSynthesisLabelProgramBuildRoles.literal Prod.fst term = program ∧
          program.components = size.toNat := by
  simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
    firstOrderRaw_complete SourceSynthesisLabelProgramBuildRoles.literal Prod.fst
      lib query size expression returned

end MicroCFTA.SourceSynthesisOriginalProgramTermSize
