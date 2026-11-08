import MicroCFTA.SourceCurrentHereditaryTypePaths
import MicroCFTA.SourceSynthesisOriginalTypeRequired
import MicroCFTA.SourceSynthesisGuardRegions

/-!
# Type routes at original Program row calls

An ordinary Program value needs annotations only at child zero of its rows.
The other guards and siblings remain unrestricted. Actual original row calls
derive the direct Type fields. Nested Program fields use explicit local input
certificates at the exact ordered child positions. These certificates do not
follow from the existing strict Program role alone. Their original source
construction and preservation through later calls remain separate obligations.
-/
namespace MicroCFTA.SourceSynthesisTypePathRoles
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityAnnotationLanguage (Annotated)
open SourceEqualityProjectionGraph (select)
open SourceCurrentHereditaryTypePaths (TypePath ForestPath)
variable {Symbol Guard : Type}

/-- Empty or ordinary Program heads have annotated row children at position zero. -/
inductive AnnotationFields (valid : Guard → Prop) : Value Symbol Guard → Prop where
  | empty : AnnotationFields valid .empty
  | node (entry : Interned InternedBinderProtocol.NodeKey) (rows : List (EdgeValue Symbol Guard))
      (depth : Nat) (free : List InternedBinderProtocol.Reference)
      (typed : ∀ row ∈ rows, ∀ value, row.children[0]? = some value → Annotated valid value) :
      AnnotationFields valid (.node entry rows depth free)

/-- A row's annotated first child permits every continuation inside that Type. -/
theorem annotation_path {valid : Guard → Prop} {value : Value Symbol Guard}
    (fields : AnnotationFields valid value) (tail : List Int) : TypePath valid (0 :: tail) value := by
  cases fields with
  | empty => exact .annotated _ _ .empty
  | node entry rows depth free typed =>
      apply TypePath.ordinary
      intro row member child selected
      exact .annotated tail child (typed row member child (by simpa [select] using selected))

private theorem forest_typed {valid : Guard → Prop} {values : List (Value Symbol Guard)}
    {index : Nat} {value : Value Symbol Guard} (found : values[index]? = some value)
    (annotated : Annotated valid value) (tail : List Int) :
    ForestPath valid ((index : Int) :: tail) values := by
  intro child selected
  have same : value = child := Option.some.inj (found.symm.trans (by simpa [select] using selected))
  exact same ▸ TypePath.annotated tail value annotated

private theorem forest_program {valid : Guard → Prop} {values : List (Value Symbol Guard)}
    (index : Nat) (tail : List Int)
    (fields : ∀ value, values[index]? = some value → AnnotationFields valid value) :
    ForestPath valid ((index : Int) :: 0 :: tail) values := by
  intro child selected
  exact annotation_path (fields child (by simpa [select] using selected)) tail

open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedFreshOrdinaryConstruction (build)
open SourceSynthesisTypeSyntax
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw typesOf)
open SourceSynthesisGeneralizeSyntax (top)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
local notation "CurrentSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "CurrentGuard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable [DecidableEq (EdgeKey CurrentSymbol CurrentGuard)]

section Source
variable (lib : Library) (query : Query) (signed : Int) (whole : Expression)
variable (accepted : firstOrderRaw lib query signed = .ok whole)
variable (rootValue : Value CurrentSymbol CurrentGuard) (heap : State CurrentSymbol CurrentGuard)
variable (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
variable {expressions : List (EdgeSyntax CurrentSymbol CurrentGuard)} {before after : State CurrentSymbol CurrentGuard}
variable {outputs : List (EdgeValue CurrentSymbol CurrentGuard)} {rowIndex : Nat} {symbol : CurrentSymbol}
include accepted built

/-- Actual application fields and local Program inputs cover every source application Type route. -/
theorem application_paths (function argument : Expression)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.applicationGuard
      [ordinarySymbols (typesOf lib query), ordinarySymbols (arrowMarker top),
        ordinarySymbols function, ordinarySymbols argument])
    (functionFields : ∀ value, call.values[2]? = some value → AnnotationFields (Origin lib) value)
    (argumentFields : ∀ value, call.values[3]? = some value → AnnotationFields (Origin lib) value)
    (path : EqualityNormalize.Path) (region : SourceSynthesisGuardRegions.applicationRegion path) :
    ForestPath (Origin lib) (path.map Int.ofNat) call.output.children := by
  obtain ⟨types, marker, first, second, _, _, typesAnnotated, _, _, markerAnnotated⟩ :=
    SourceSynthesisOriginalTypeFieldCalls.application_call lib query signed whole accepted rootValue heap built
      function argument call
  rw [call.children_eq] at first second ⊢
  rcases region with direct | markerPath | functionPath | argumentPath
  · obtain ⟨tail, rfl⟩ := direct
    simpa [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using forest_typed first typesAnnotated (tail.map Int.ofNat)
  · obtain ⟨tail, rfl⟩ := markerPath
    simpa [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using forest_typed second markerAnnotated (tail.map Int.ofNat)
  · obtain ⟨tail, rfl⟩ := functionPath
    simpa [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using forest_program 2 (tail.map Int.ofNat) functionFields
  · obtain ⟨tail, rfl⟩ := argumentPath
    simpa [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using forest_program 3 (tail.map Int.ofNat) argumentFields

/-- Actual filter fields and the local candidate input cover every source filter Type route. -/
theorem filter_paths (candidates : Expression)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.filterGuard
      [ordinarySymbols (typeNode top query.queryGoal), ordinarySymbols candidates])
    (candidateFields : ∀ value, call.values[1]? = some value → AnnotationFields (Origin lib) value)
    (path : EqualityNormalize.Path) (region : SourceSynthesisGuardRegions.filterRegion path) :
    ForestPath (Origin lib) (path.map Int.ofNat) call.output.children := by
  obtain ⟨goal, first, _, _, annotated⟩ := SourceSynthesisOriginalTypeFieldCalls.filter_call
    lib query signed whole accepted rootValue heap built candidates call
  rw [call.children_eq] at first ⊢
  rcases region with direct | candidatePath
  · obtain ⟨tail, rfl⟩ := direct
    simpa [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using forest_typed first annotated (tail.map Int.ofNat)
  · obtain ⟨tail, rfl⟩ := candidatePath
    simpa [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using forest_program 1 (tail.map Int.ofNat) candidateFields

/-- Actual Required execution derives its returned first Type route before later Program edits. -/
theorem required_application_head (function argument : Expression)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.applicationGuard
      [ordinarySymbols (typesOf lib query), ordinarySymbols (arrowMarker top),
        ordinarySymbols function, ordinarySymbols argument])
    {fuel readFuel : Nat} {paths : List (List Int)} {results : List (Value CurrentSymbol CurrentGuard)}
    {finish : State CurrentSymbol CurrentGuard}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths call.output.children heap = .done results finish) :
    ForestPath (Origin lib) [0] results := by
  obtain ⟨result, found, annotated⟩ := SourceSynthesisOriginalTypeRequired.application
    lib query signed whole accepted rootValue heap built function argument call actual
  exact forest_typed found annotated []
end Source
end MicroCFTA.SourceSynthesisTypePathRoles
