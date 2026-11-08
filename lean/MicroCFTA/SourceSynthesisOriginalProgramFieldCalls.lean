import MicroCFTA.SourceSynthesisOriginalProgramTypeFields

/-!
# Original Program child calls supply their Type fields

Each selected physical child retains its actual ordered source build.
The original Program syntax certificate derives its annotation fields.
Application and filter routes therefore need no supplied value annotation.
The source Program certificate is an original syntactic input. These laws
do not identify an arbitrary later memo winner with an original source call.
-/
namespace MicroCFTA.SourceSynthesisOriginalProgramFieldCalls
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedFreshOrdinaryConstruction (build)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw typesOf)
open SourceSynthesisInitialTypeFields (Program)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisTypePathRoles (AnnotationFields)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable [DecidableEq (EdgeKey Symbol Guard)]

section Source
variable (lib : Library) (query : Query) (signed : Int) (whole : Expression)
variable (accepted : firstOrderRaw lib query signed = .ok whole)
variable (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
variable (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
variable {expressions : List (EdgeSyntax Symbol Guard)} {before after : State Symbol Guard}
variable {outputs : List (EdgeValue Symbol Guard)} {rowIndex : Nat} {symbol : Symbol}
include accepted built

/-- The exact physical child obtains its fields from its actual original Program build. -/
theorem program_slot (field : Expression) (program : Program lib query field)
    {guard : Guard} {children : List (Syntax Symbol Guard)}
    (call : RowCall expressions [] before outputs after heap rowIndex symbol guard children)
    (index : Nat) (syntaxLookup : children[index]? = some (ordinarySymbols field))
    (value : Value Symbol Guard) (physicalLookup : call.output.children[index]? = some value) :
    AnnotationFields (Origin lib) value := by
  obtain ⟨chosen, start, finish, selected, context, actual, _first, last⟩ :=
    SourceSynthesisOriginalProgramTypeFields.many_call children call.current call.middle heap call.context
      call.values call.called call.middle_growth index (ordinarySymbols field) syntaxLookup
  have fields := SourceSynthesisOriginalProgramTypeFields.at_prefix lib query signed whole accepted rootValue heap built
    field program start context chosen finish actual last
  have valuesLookup : call.values[index]? = some value := by
    simpa only [call.children_eq] using physicalLookup
  have same : chosen = value := Option.some.inj (selected.symm.trans valuesLookup)
  exact same ▸ fields

/-- Actual original application calls derive every Type route from original Program syntax. -/
theorem application_paths (function argument : Expression)
    (functionRole : Program lib query function) (argumentRole : Program lib query argument)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.applicationGuard
      [ordinarySymbols (typesOf lib query), ordinarySymbols (arrowMarker top),
        ordinarySymbols function, ordinarySymbols argument])
    (path : EqualityNormalize.Path) (region : SourceSynthesisGuardRegions.applicationRegion path) :
    ForestPath (Origin lib) (path.map Int.ofNat) call.output.children := by
  refine SourceSynthesisTypePathRoles.application_paths lib query signed whole accepted rootValue heap built
    function argument call ?_ ?_ path region
  · intro value selected
    exact program_slot lib query signed whole accepted rootValue heap built function functionRole call 2 rfl value
      (by simpa only [call.children_eq] using selected)
  · intro value selected
    exact program_slot lib query signed whole accepted rootValue heap built argument argumentRole call 3 rfl value
      (by simpa only [call.children_eq] using selected)

/-- Actual original filter calls derive every Type route from original candidate syntax. -/
theorem filter_paths (candidates : Expression) (candidateRole : Program lib query candidates)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.filterGuard
      [ordinarySymbols (typeNode top query.queryGoal), ordinarySymbols candidates])
    (path : EqualityNormalize.Path) (region : SourceSynthesisGuardRegions.filterRegion path) :
    ForestPath (Origin lib) (path.map Int.ofNat) call.output.children := by
  refine SourceSynthesisTypePathRoles.filter_paths lib query signed whole accepted rootValue heap built
    candidates call ?_ path region
  intro value selected
  exact program_slot lib query signed whole accepted rootValue heap built candidates candidateRole call 1 rfl value
    (by simpa only [call.children_eq] using selected)
end Source
end MicroCFTA.SourceSynthesisOriginalProgramFieldCalls
