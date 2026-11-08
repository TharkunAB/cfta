import MicroCFTA.SourceSynthesisOriginalTypeAnnotations
import MicroCFTA.SourceCurrentStoredMuRetainedAlignment
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.SourceSynthesisOriginalGuardAlphabet

/-!
# Type operands at actual original Program row calls

The ordered child call supplies the exact Type slot. Its actual earlier
heap retains the original Mu certificate. Program children in other slots
need no Type annotation. The source scope is an original row call with an
empty lexical environment and the original completed heap as reader.
These laws do not classify every reached or open-domain caller.
-/
namespace MicroCFTA.SourceSynthesisOriginalTypeFieldCalls
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top generalize)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw typesOf)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceSynthesisOriginalTypeAnnotations (OriginalType)
open SourceEqualityAnnotationConstruction (Allowed)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "BasicContext" => InternedFreshOrdinaryContext.Context
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem many_call (expressions : List (Syntax Symbol Guard))
    (before after reader : State Symbol Guard) (context : BasicContext before [])
    (values : List (Value Symbol Guard)) (actual : buildMany expressions [] before = .done values after)
    (growth : Grows after reader) (index : Nat) (expression : Syntax Symbol Guard)
    (found : expressions[index]? = some expression) :
    ∃ value start finish, values[index]? = some value ∧ BasicContext start [] ∧
      build expression [] start = .done value finish ∧ Grows start reader ∧ Grows finish reader := by
  induction expressions generalizing before values index with
  | nil => simp only [List.getElem?_nil] at found; cases found
  | cons first rest ih =>
      cases one : build first [] before with
      | pending key state => simp only [buildMany, one, Outcome.bind] at actual; cases actual
      | done value middle =>
          cases tail : buildMany rest [] middle with
          | pending key state => simp only [buildMany, one, tail, Outcome.bind] at actual; cases actual
          | done remaining final =>
              have same := actual
              simp only [buildMany, one, tail, Outcome.bind, Outcome.done.injEq] at same
              obtain ⟨rfl, rfl⟩ := same
              have nextContext : BasicContext middle [] := by
                simpa only [one, Outcome.state] using context.build first
              have tailChecked := InternedFreshOrdinaryFacts.buildMany_verified rest [] middle
                nextContext.normal.facts nextContext.inputs
              have tailGrowth : Grows middle final := by
                simpa only [tail, Outcome.state] using tailChecked.growth
              have nextGrowth := grows_trans tailGrowth growth
              cases index with
              | zero =>
                  have field : first = expression := Option.some.inj found
                  subst expression
                  have checked := InternedFreshOrdinaryFacts.build_verified first [] before
                    context.normal.facts context.inputs
                  have firstGrowth : Grows before middle := by
                    simpa only [one, Outcome.state] using checked.growth
                  exact ⟨value, before, middle, rfl, context, one,
                    grows_trans firstGrowth nextGrowth, nextGrowth⟩
              | succ index =>
                  obtain ⟨chosen, start, finish, selected, entered, called, initial, last⟩ :=
                    ih middle nextContext remaining tail index found
                  exact ⟨chosen, start, finish, selected, entered, called, initial, last⟩

section Source
variable (lib : Library) (query : Query) (signed : Int) (whole : Expression)
variable (accepted : firstOrderRaw lib query signed = .ok whole)
variable (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
variable (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
variable {expressions : List (EdgeSyntax Symbol Guard)} {before after : State Symbol Guard}
variable {outputs : List (EdgeValue Symbol Guard)} {rowIndex : Nat} {symbol : Symbol}
include accepted built

private theorem typed_slot {guard : Guard} {children : List (Syntax Symbol Guard)}
    (call : RowCall expressions [] before outputs after heap rowIndex symbol guard children)
    (index : Nat) (field : Expression) (found : children[index]? = some (ordinarySymbols field))
    (allowed : Allowed (Origin lib) (ordinarySymbols field)) :
    ∃ value, call.output.children[index]? = some value ∧ Available heap value ∧
      value.free = [] ∧ Annotated (Origin lib) value := by
  obtain ⟨value, start, finish, selected, context, actual, first, _last⟩ :=
    many_call children call.current call.middle heap call.context call.values call.called
      call.middle_growth index (ordinarySymbols field) found
  have annotation := SourceSynthesisOriginalTypeAnnotations.build_typed lib query signed whole accepted
    rootValue heap built field start context first value finish actual allowed
  have middleContext : BasicContext call.middle [] := by
    simpa only [call.called, Outcome.state] using call.context.many children
  have made := InternedEdgeResidency.makeEdge_linked symbol guard call.values call.middle
    middleContext.normal.facts.coherent middleContext.normal.facts.linked
  have residentNext : InternedEdgeResidency.EdgeResident call.next call.output := by
    simpa only [call.made] using made.2
  have resident := InternedEdgeResidency.edge_grows call.next heap call.next_growth call.output residentNext
  have originalChecked := InternedFreshOrdinaryFacts.build_verified (ordinarySymbols whole) [] empty
    InternedNestedFacts.empty_facts (by intro value member; cases member)
  have finalFacts : InternedNestedFacts.Facts heap := by
    simpa only [built, Outcome.state] using originalChecked.facts
  have selectedOutput : call.output.children[index]? = some value := by
    simpa only [call.children_eq] using selected
  have available := finalFacts.cached.edges call.output.entry.key call.output resident value
    (List.mem_of_getElem? selectedOutput)
  have closed : value.free = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name member
    obtain ⟨input, absent, _⟩ := InternedFreshOrdinarySourceFreeNames.build_free_origins
      (ordinarySymbols field) [] start context.normal context.inputs context.freeNames context.profiles
      value finish actual name member
    cases absent
  exact ⟨value, by simpa only [call.children_eq] using selected, available, closed, annotation⟩

/-- An actual original generalized component call supplies its closed Type operand at slot zero. -/
theorem component_call (typ : Ty) (original : OriginalType lib typ)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol top
      [ordinarySymbols (generalize (typesOf lib query) typ)]) :
    ∃ value, call.output.children[0]? = some value ∧ Available heap value ∧
      value.free = [] ∧ Annotated (Origin lib) value := by
  apply typed_slot lib query signed whole accepted rootValue heap built call 0 _ rfl
  simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
    SourceSynthesisOriginalTypeAnnotations.generalized_allowed
      SourceSynthesisLabelProgramBuildRoles.literal lib query typ original

/-- An actual rigid argument call supplies its closed Type operand at slot zero. -/
theorem argument_call (typ : Ty)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol top
      [ordinarySymbols (typeNode top typ)]) :
    ∃ value, call.output.children[0]? = some value ∧ Available heap value ∧
      value.free = [] ∧ Annotated (Origin lib) value := by
  apply typed_slot lib query signed whole accepted rootValue heap built call 0 _ rfl
  simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
    SourceSynthesisOriginalTypeAnnotations.rigid_allowed SourceSynthesisLabelProgramBuildRoles.literal lib typ

/-- An actual application call supplies its closed universe and marker at the first two slots. -/
theorem application_call (function argument : Expression)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.applicationGuard
      [ordinarySymbols (typesOf lib query), ordinarySymbols (arrowMarker top),
        ordinarySymbols function, ordinarySymbols argument]) :
    ∃ types marker, call.output.children[0]? = some types ∧ call.output.children[1]? = some marker ∧
      Available heap types ∧ types.free = [] ∧ Annotated (Origin lib) types ∧
      Available heap marker ∧ marker.free = [] ∧ Annotated (Origin lib) marker := by
  have typesAllowed : Allowed (Origin lib) (ordinarySymbols (typesOf lib query)) := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
      SourceSynthesisOriginalTypeAnnotations.universe_allowed SourceSynthesisLabelProgramBuildRoles.literal lib query
  have markerAllowed : Allowed (Origin lib) (ordinarySymbols (arrowMarker top)) := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
      SourceSynthesisOriginalTypeAnnotations.marker_allowed SourceSynthesisLabelProgramBuildRoles.literal lib
  obtain ⟨types, first, availableTypes, closedTypes, annotatedTypes⟩ :=
    typed_slot lib query signed whole accepted rootValue heap built call 0 _ rfl typesAllowed
  obtain ⟨marker, second, availableMarker, closedMarker, annotatedMarker⟩ :=
    typed_slot lib query signed whole accepted rootValue heap built call 1 _ rfl markerAllowed
  exact ⟨types, marker, first, second, availableTypes, closedTypes, annotatedTypes,
    availableMarker, closedMarker, annotatedMarker⟩

/-- An actual filter call supplies its closed rigid goal at slot zero. -/
theorem filter_call (candidates : Expression)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.filterGuard
      [ordinarySymbols (typeNode top query.queryGoal), ordinarySymbols candidates]) :
    ∃ value, call.output.children[0]? = some value ∧ Available heap value ∧
      value.free = [] ∧ Annotated (Origin lib) value := by
  apply typed_slot lib query signed whole accepted rootValue heap built call 0 _ rfl
  simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
    SourceSynthesisOriginalTypeAnnotations.rigid_allowed
      SourceSynthesisLabelProgramBuildRoles.literal lib query.queryGoal
end Source
end MicroCFTA.SourceSynthesisOriginalTypeFieldCalls
