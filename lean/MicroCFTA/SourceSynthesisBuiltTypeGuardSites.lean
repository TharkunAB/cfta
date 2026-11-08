import MicroCFTA.SourceSynthesisTypeGuardSites
import MicroCFTA.SourceSynthesisNormalizedVariablePaths
import MicroCFTA.SourceSynthesisProgramBuildRolesGeneric
import MicroCFTA.SourceCurrentBuildStructuralRowOrigins

/-!
# Full guards at actual original Type row calls

The source occurrence fixes the original row position and full guard.
Its captured RowCall fixes the actual child build and physical row result.
Every initial stored endpoint has its original Ty occurrence and size bound.
Symbol mapping includes the current Label representation without a change
to guards or child order. An ordinary source root derives its retained row
calls from the actual completed build, including canonical row selection.
Binder, lexical capture and warm stored-winner rows keep their separate
structural origin alternatives. This file does not identify such a winner
with the current Ty or assert a Type guard law for the complete heap.
-/
namespace MicroCFTA.SourceSynthesisBuiltTypeGuardSites
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedFreshOrdinaryConstruction (build buildEdges)
open SourceSynthesisTypeSyntax (Ty allTypes)
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard equalityClasses generalize)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren mapEdges mapEdge mapEdges_eq_map)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
local notation "SyntaxRowAt" => SourceSynthesisTypeGuardSites.RowAt
local notation "PhysicalRowAt" => SourceCurrentStoredLiteralRowLineage.RowAt
local notation "Context" => SourceCurrentConstrainedCapSourceHistory.Context
variable {Symbol : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- A captured mapped row call keeps Top or the exact original outer equality field. -/
theorem rowCall_guard_site (literal : String → Symbol) (typ : Ty) (constructors : List (String × Nat))
    {address : List SourceSynthesisTypeGuardSites.Position} {sourceIndex : Nat}
    {symbol : String} {guard : Guard} {children : List (Syntax String Guard)}
    {expressions : List (EdgeSyntax String Guard)} {inputs : List (Value Symbol Guard)}
    {before middle reader : State Symbol Guard} {rows : List (EdgeValue Symbol Guard)}
    (occurrence : SyntaxRowAt (generalize (allTypes top constructors) typ) address sourceIndex
      (.mk symbol guard children))
    (call : RowCall (mapEdges literal expressions) inputs before rows middle reader sourceIndex
      (literal symbol) guard (mapChildren literal children)) :
    call.output.entry.key.constraint = top ∨
      address = [] ∧ sourceIndex = 0 ∧ call.output.entry.key.constraint = eqGuard (equalityClasses typ) := by
  by_cases plain : guard = top
  · exact .inl (call.guard_eq.trans plain)
  · obtain ⟨root, index, fullGuard⟩ :=
      SourceSynthesisTypeGuardSites.generalize_nonTop typ constructors occurrence plain
    exact .inr ⟨root, index, call.guard_eq.trans fullGuard⟩

/-- A proper original source occurrence gives Top at its actual mapped row call. -/
theorem interior_call_top (literal : String → Symbol) (typ : Ty) (constructors : List (String × Nat))
    {address : List SourceSynthesisTypeGuardSites.Position} {sourceIndex : Nat}
    {symbol : String} {guard : Guard} {children : List (Syntax String Guard)}
    {expressions : List (EdgeSyntax String Guard)} {inputs : List (Value Symbol Guard)}
    {before middle reader : State Symbol Guard} {rows : List (EdgeValue Symbol Guard)}
    (occurrence : SyntaxRowAt (generalize (allTypes top constructors) typ) address sourceIndex
      (.mk symbol guard children))
    (proper : address ≠ [])
    (call : RowCall (mapEdges literal expressions) inputs before rows middle reader sourceIndex
      (literal symbol) guard (mapChildren literal children)) :
    call.output.entry.key.constraint = top :=
  call.guard_eq.trans (SourceSynthesisTypeGuardSites.generalize_interior_top typ constructors occurrence proper)

/-- Every initial physical field endpoint retains an original variable occurrence and its Ty size bound. -/
theorem rowCall_endpoint_origin (literal : String → Symbol) (typ : Ty) (constructors : List (String × Nat))
    {address : List SourceSynthesisTypeGuardSites.Position} {sourceIndex : Nat}
    {symbol : String} {guard : Guard} {children : List (Syntax String Guard)}
    {expressions : List (EdgeSyntax String Guard)} {inputs : List (Value Symbol Guard)}
    {before middle reader : State Symbol Guard} {rows : List (EdgeValue Symbol Guard)}
    (occurrence : SyntaxRowAt (generalize (allTypes top constructors) typ) address sourceIndex
      (.mk symbol guard children))
    (call : RowCall (mapEdges literal expressions) inputs before rows middle reader sourceIndex
      (literal symbol) guard (mapChildren literal children))
    (path : List Nat)
    (member : path ∈ EqualityNormalize.members (call.output.entry.key.constraint.equalities.getD [])) :
    (∃ name, (name, path) ∈ SourceSynthesisGeneralizeSyntax.occurrences typ) ∧ path.length < sizeOf typ := by
  rcases rowCall_guard_site literal typ constructors occurrence call with plain | ⟨_root, _index, fullGuard⟩
  · rw [plain] at member
    change path ∈ ([] : List (List Nat)) at member
    simp only [List.not_mem_nil] at member
  · have normalized : path ∈ EqualityNormalize.members ((eqGuard (equalityClasses typ)).equalities.getD []) := by
      simpa only [fullGuard] using member
    exact ⟨SourceSynthesisNormalizedVariablePaths.eqGuard_occurrence typ path normalized,
      SourceSynthesisNormalizedVariablePaths.eqGuard_length_lt_sizeOf typ path normalized⟩

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem mapped_source (literal : String → Symbol)
    {expressions : List (EdgeSyntax String Guard)} {index : Nat}
    {symbol : Symbol} {guard : Guard} {children : List (Syntax Symbol Guard)}
    (selected : (mapEdges literal expressions)[index]? = some (.mk symbol guard children)) :
    ∃ name sourceChildren,
      expressions[index]? = some (.mk name guard sourceChildren) ∧
      symbol = literal name ∧ children = mapChildren literal sourceChildren := by
  have mapped : (expressions[index]?).map (mapEdge literal) = some (.mk symbol guard children) := by
    simpa only [mapEdges_eq_map, List.getElem?_map] using selected
  cases found : expressions[index]? with
  | none => simp only [found, Option.map_none] at mapped; cases mapped
  | some expression =>
      cases expression with
      | mk name own sourceChildren =>
          have same : EdgeSyntax.mk (literal name) own (mapChildren literal sourceChildren) =
              .mk symbol guard children :=
            Option.some.inj (by simpa only [found, Option.map_some, mapEdge] using mapped)
          cases same
          exact ⟨name, sourceChildren, rfl, rfl, rfl⟩

/-- A completed ordinary generalized root derives the exact source call of every retained physical row. -/
theorem generalized_root_row (literal : String → Symbol) (typ : Ty) (constructors : List (String × Nat))
    {expressions : List (EdgeSyntax String Guard)}
    (ordinary : generalize (allTypes top constructors) typ = .node expressions)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (raw : Value Symbol Guard)
    (after : State Symbol Guard) (context : Context before inputs)
    (actual : build (mapSyntax literal (generalize (allTypes top constructors) typ)) inputs before = .done raw after)
    (row : EdgeValue Symbol Guard) (part : PhysicalRowAt raw row) :
    ∃ rows middle, ∃ (sourceIndex outputIndex : Nat), ∃ symbol guard children,
      buildEdges (mapEdges literal expressions) inputs before = .done rows middle ∧
      run (makeNode rows) middle = (raw, after) ∧
      (InternedEdgeResidency.nodeEdges raw)[outputIndex]? = some row ∧
      ∃ call : RowCall (mapEdges literal expressions) inputs before rows middle after sourceIndex
          (literal symbol) guard (mapChildren literal children),
        call.output = row ∧
        (row.entry.key.constraint = top ∨
          sourceIndex = 0 ∧ row.entry.key.constraint = eqGuard (equalityClasses typ)) := by
  have nodeDone : build (.node (mapEdges literal expressions)) inputs before = .done raw after := by
    simpa only [ordinary, mapSyntax] using actual
  have origin := SourceCurrentBuildStructuralRowOrigins.build_row_origin
    (.node (mapEdges literal expressions)) inputs before raw after context nodeDone row part
  cases origin with
  | node built made selected call same =>
      obtain ⟨name, sourceChildren, source, symbolEq, childrenEq⟩ := mapped_source literal call.source
      cases symbolEq
      cases childrenEq
      have occurrence := SourceSynthesisTypeGuardSites.RowAt.node source
      have originalOccurrence := occurrence
      rw [← ordinary] at originalOccurrence
      have classified := rowCall_guard_site literal typ constructors originalOccurrence call
      refine ⟨_, _, _, _, _, _, _, built, made, selected, call, same, ?_⟩
      rw [← same]
      rcases classified with plain | ⟨_root, index, fullGuard⟩
      · exact .inl plain
      · exact .inr ⟨index, fullGuard⟩

end MicroCFTA.SourceSynthesisBuiltTypeGuardSites
