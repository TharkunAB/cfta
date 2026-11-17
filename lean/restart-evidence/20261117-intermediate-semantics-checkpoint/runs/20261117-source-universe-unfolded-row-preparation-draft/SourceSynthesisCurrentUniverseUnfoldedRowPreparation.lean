import MicroCFTA.SourceSynthesisCurrentUniverseUnfoldedRowInputs
import MicroCFTA.SourcePruningEnumerationTopArrowInput

namespace MicroCFTA.SourceSynthesisCurrentUniverseUnfoldedRowPreparation
open Cache Language EnumerationState InternedConstructorTemplates InternedNestedFacts
open InternedBinderProtocol (NodeKey)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable [DecidableEq (EdgeKey Symbol Constraint)]
set_option autoImplicit false

/- Note [Source guards and actual arrow staging]
Actual unfolding retains the same original source row and full-U substitution.
Every original U row has the Top guard. The actual output row keeps that guard.
The catalog and distinguished arrow remain separate cases.
A catalog entry can have the same name as the arrow.
Only the real arrow case supplies the original marker at child zero.
Its actual Top preparation allocates no own class and keeps the inherited bucket.
The native endpoint is the actual completed unfold heap.
No terminal exclusion, child result, Type role or final assignment is assumed.
-/

theorem original_universe_unfolded_row_top
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (nativeBefore nativeAfter : InternedConstructorTemplates.State Symbol Constraint)
    (facts : Facts nativeBefore) (sourceGrowth : Grows sourceHeap nativeBefore)
    (fuel : Nat) (prepared : Node)
    (actual : SourcePruningEnumerationSelectedValue.run fuel
      (.mu entry body depth ordinary) nativeBefore = .done prepared nativeAfter)
    (row : Edge) (present : row ∈ InternedEdgeResidency.nodeEdges prepared) :
    row.entry.key.constraint = SourceSynthesisGeneralizeSyntax.top
 := by
  obtain ⟨sourceRow, member, _symbolSame, guardSame, _childrenSame, _classification⟩ :=
    SourceSynthesisCurrentUniverseUnfoldedRowInputs.original_universe_unfolded_row_inputs
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      nativeBefore nativeAfter facts sourceGrowth fuel prepared actual row present
  obtain ⟨bodyEntry, marker, arrow, rows, bodyEq, _markerRead, _arrowChildren, _arrowKey,
      _aligned, _markerClosed, _markerAvailable, kinds, _retained⟩ :=
    SourceSynthesisCurrentUniverseOwnership.current_stored_universe_rows
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
  have included : sourceRow ∈ canonicalEdges (arrow :: rows) := by
    simpa only [bodyEq, InternedEdgeResidency.nodeEdges] using member
  exact guardSame.trans (kinds sourceRow included).1

theorem original_universe_unfolded_row_preparation
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (nativeBefore nativeAfter : InternedConstructorTemplates.State Symbol Constraint)
    (facts : Facts nativeBefore) (sourceGrowth : Grows sourceHeap nativeBefore)
    (fuel : Nat) (prepared : Node)
    (actual : SourcePruningEnumerationSelectedValue.run fuel
      (.mu entry body depth ordinary) nativeBefore = .done prepared nativeAfter)
    (row : Edge) (present : row ∈ InternedEdgeResidency.nodeEdges prepared)
    (scs : List Suspended) (before middle : Cached) (symbol : Symbol)
    (staged : List Input) (residual : Option Constraint)
    (own : SourcePruningEnumerationCachedOwn.prepare nativeAfter scs row before =
      some [((symbol, staged, residual), middle)]) :
    ∃ sourceRow : Edge,
      sourceRow ∈ InternedEdgeResidency.nodeEdges body ∧
      row.entry.key.symbol = sourceRow.entry.key.symbol ∧
      row.entry.key.constraint = sourceRow.entry.key.constraint ∧
      row.children = sourceRow.children.map
        (InternedStoredSubstitution.input
          (InternedStoredSubstitutionRebind.replacement (.interned entry.identity)
            (.mu entry body depth ordinary))) ∧
      ((∃ (name : String) (arity : Nat),
          (name, arity) ∈ SourceSynthesisUniverseBody.descriptors
            (SourceSynthesisCurrentContext.constructorCatalog lib query) ∧
          row.entry.key.symbol = literal name ∧
          row.children = List.replicate arity (.mu entry body depth ordinary)) ∨
        ∃ (marker : Node) (markerEntry : Interned NodeKey) (markerRow : Edge),
          marker = .node markerEntry [markerRow] 0 [] ∧
          markerRow.children = [] ∧
          markerRow.entry.key = ⟨literal "(->)", [], SourceSynthesisGeneralizeSyntax.top⟩ ∧
          row.entry.key.symbol = literal "->" ∧
          row.children = [marker, .mu entry body depth ordinary, .mu entry body depth ordinary] ∧
          middle = before ∧ symbol = row.entry.key.symbol ∧ residual = none ∧
          staged[0]? = some (marker, descendScs 0 scs,
            SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
              (descendScs 0 scs) marker))
 := by
  have top := original_universe_unfolded_row_top lib query signed whole accepted rootValue sourceHeap built
    key entry body depth ordinary stored nativeBefore nativeAfter facts sourceGrowth fuel prepared actual row present
  obtain ⟨sourceRow, member, symbolSame, guardSame, childrenSame, classification⟩ :=
    SourceSynthesisCurrentUniverseUnfoldedRowInputs.original_universe_unfolded_row_inputs
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      nativeBefore nativeAfter facts sourceGrowth fuel prepared actual row present
  refine ⟨sourceRow, member, symbolSame, guardSame, childrenSame, ?_⟩
  rcases classification with catalog | arrow
  · exact Or.inl catalog
  · obtain ⟨marker, markerEntry, markerRow, markerEq, markerChildren, markerKey,
        rowSymbol, rowChildren⟩ := arrow
    obtain ⟨cacheSame, preparedSymbol, residualSame, first⟩ :=
      SourcePruningEnumerationTopArrowInput.top_arrow_preparation_first
        nativeAfter scs row marker (.mu entry body depth ordinary) (.mu entry body depth ordinary)
        before middle symbol staged residual top rowChildren own
    exact Or.inr ⟨marker, markerEntry, markerRow, markerEq, markerChildren, markerKey,
      rowSymbol, rowChildren, cacheSame, preparedSymbol, residualSame, first⟩

end MicroCFTA.SourceSynthesisCurrentUniverseUnfoldedRowPreparation
