import MicroCFTA.SourceSynthesisOriginalProgramFieldCalls
import MicroCFTA.SourcePruningEnumerationArityOrigins

/-!
# Mixed Type slots at original source calls

The actual ordered constructor call fixes the child count. Existing source
Type and Program field laws classify every returned slot. Program children
need no Type annotation on their own guards. These are original construction
facts. They do not classify later Parent rows or warm memo returns.
-/
namespace MicroCFTA.SourceSynthesisOriginalMixedTypeSlots
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedFreshOrdinaryConstruction (build)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw typesOf)
open SourceSynthesisInitialTypeFields (Program)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisTypePathRoles (AnnotationFields)
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

/-- The exact original application call classifies every actual mixed child slot. -/
theorem application (function argument : Expression)
    (functionRole : Program lib query function) (argumentRole : Program lib query argument)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.applicationGuard
      [ordinarySymbols (typesOf lib query), ordinarySymbols (arrowMarker top),
        ordinarySymbols function, ordinarySymbols argument]) :
    call.output.children.length = 4 ∧
      ∀ index value, call.output.children[index]? = some value →
        ((index = 2 ∨ index = 3) → AnnotationFields (Origin lib) value) ∧
        (¬ (index = 2 ∨ index = 3) → Annotated (Origin lib) value) := by
  have size := SourcePruningEnumerationArityOrigins.buildMany_length _ _ _ _ _ call.called
  have length : call.output.children.length = 4 := by
    simpa only [call.children_eq, List.length_cons, List.length_nil] using size
  obtain ⟨types, marker, first, second, _typesAvailable, _typesClosed, typesTyped,
      _markerAvailable, _markerClosed, markerTyped⟩ :=
    SourceSynthesisOriginalTypeFieldCalls.application_call lib query signed whole accepted rootValue heap built
      function argument call
  refine ⟨length, ?_⟩
  intro index value found
  refine ⟨?_, ?_⟩
  · intro assigned
    rcases assigned with rfl | rfl
    · exact SourceSynthesisOriginalProgramFieldCalls.program_slot lib query signed whole accepted rootValue heap built
        function functionRole call 2 rfl value found
    · exact SourceSynthesisOriginalProgramFieldCalls.program_slot lib query signed whole accepted rootValue heap built
        argument argumentRole call 3 rfl value found
  · intro unassigned
    have inside := (List.getElem?_eq_some_iff.mp found).1
    have position : index = 0 ∨ index = 1 := by omega
    rcases position with rfl | rfl
    · have same : value = types := Option.some.inj (found.symm.trans first)
      simpa only [same] using typesTyped
    · have same : value = marker := Option.some.inj (found.symm.trans second)
      simpa only [same] using markerTyped

/-- The exact original filter call classifies its goal and Program child. -/
theorem filter (candidates : Expression) (candidateRole : Program lib query candidates)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.filterGuard
      [ordinarySymbols (typeNode top query.queryGoal), ordinarySymbols candidates]) :
    call.output.children.length = 2 ∧
      ∀ index value, call.output.children[index]? = some value →
        (index = 1 → AnnotationFields (Origin lib) value) ∧
        (index ≠ 1 → Annotated (Origin lib) value) := by
  have size := SourcePruningEnumerationArityOrigins.buildMany_length _ _ _ _ _ call.called
  have length : call.output.children.length = 2 := by
    simpa only [call.children_eq, List.length_cons, List.length_nil] using size
  obtain ⟨goal, first, _goalAvailable, _goalClosed, goalTyped⟩ :=
    SourceSynthesisOriginalTypeFieldCalls.filter_call lib query signed whole accepted rootValue heap built candidates call
  refine ⟨length, ?_⟩
  intro index value found
  refine ⟨?_, ?_⟩
  · intro assigned
    subst index
    exact SourceSynthesisOriginalProgramFieldCalls.program_slot lib query signed whole accepted rootValue heap built
      candidates candidateRole call 1 rfl value found
  · intro unassigned
    have inside := (List.getElem?_eq_some_iff.mp found).1
    have position : index = 0 := by omega
    subst index
    have same : value = goal := Option.some.inj (found.symm.trans first)
    simpa only [same] using goalTyped
end Source
end MicroCFTA.SourceSynthesisOriginalMixedTypeSlots
