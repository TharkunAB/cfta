import MicroCFTA.SourceSynthesisCurrentConstruction
import MicroCFTA.SourceSynthesisCurrentProgramStructure
import MicroCFTA.SourceSynthesisCurrentCandidateAppOperands
import MicroCFTA.SourceSynthesisCurrentInitialOuterNarrowRows
import MicroCFTA.SourceCurrentBuildStructuralRowOrigins
import MicroCFTA.SourceCurrentConstrainedCapSourceHistory
import MicroCFTA.SourceCurrentStoredRowCallGrowth

namespace MicroCFTA.SourceSynthesisCurrentFirstFilterSourceLink
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "ordinaryChildren" => SourceSynthesisUniverseCallerBoundary.ordinaryChildren
local notation "ordinaryEdges" => SourceSynthesisUniverseCallerBoundary.ordinaryEdges
local notation "Expression" => SourceSynthesisFirstOrderConstruction.Expression
local notation "Row" => SourceSynthesisFirstOrderConstruction.Row
local notation "appGuard" => SourceSynthesisGeneralizeSyntax.eqGuard
  [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]]
local notation "filterGuard" => SourceSynthesisGeneralizeSyntax.eqGuard [[[0], [1, 0]]]
local notation "top" => SourceSynthesisGeneralizeSyntax.top
open InternedNestedConstruction (Outcome work)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)

/-- The actual original root row retains its adjacent goal and candidate source builds. -/
theorem current_initial_filter_interval
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue heap)
    (rootRow : EdgeValue Symbol Guard)
    (rootMember : rootRow ∈ InternedEdgeResidency.nodeEdges rootValue) :
    let ctx := SourceSynthesisCurrentContext.context lib query
    ∃ (chunks : List (List Expression))
        (goalValue candidateValue : Value Symbol Guard)
        (candidateStart candidateAfter edgeAfter : State Symbol Guard),
      (SourceSynthesisSelections.permutations ctx.argumentEdges).mapM
        (fun selected => SourceSynthesisFirstOrderConstruction.relevantRows
          ctx true signed.toNat (selected.map Prod.fst)) = .ok chunks ∧
      whole = SourceSynthesisFirstOrderConstruction.ofType (.union chunks.flatten)
        (SourceSynthesisCurrentContext.typeNode query.queryGoal) ∧
      rootRow.entry.key.symbol = literal "filter" ∧
      rootRow.entry.key.constraint = filterGuard ∧
      rootRow.children = [goalValue, candidateValue] ∧
      InternedFreshOrdinaryConstruction.build
        (ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal)) [] empty =
          .done goalValue candidateStart ∧
      SourceCurrentConstrainedCapSourceHistory.Context candidateStart [] ∧
      InternedFreshOrdinaryConstruction.build
        (ordinarySymbols (.union chunks.flatten)) [] candidateStart =
          .done candidateValue candidateAfter ∧
      run (makeEdge (literal "filter") filterGuard [goalValue, candidateValue]) candidateAfter =
        (rootRow, edgeAfter) ∧
      run (makeNode [rootRow]) edgeAfter = (rootValue, heap) ∧
      Grows candidateAfter heap ∧
      ∀ candidate ∈ chunks.flatten,
        ∃ rows : List Row, candidate = .node rows ∧
          ∀ (types function argument : Expression),
            EdgeSyntax.mk "app" appGuard
              [types, SourceSynthesisTypeSyntax.arrowMarker top, function, argument] ∈ rows →
            types = SourceSynthesisTypeSyntax.allTypes top
              (SourceSynthesisCurrentContext.constructorCatalog lib query) ∧
            ((∃ functionRows : List Row, function = .node functionRows) ∨
              ∃ pools : List (List Row), function = .union (pools.map fun rows => .node rows)) := by
  dsimp only
  obtain ⟨chunks, chunksRun, wholeShape, factory⟩ :=
    SourceSynthesisCurrentCandidateAppOperands.current_candidate_app_operands
      lib query signed whole accepted
  have rootAt : SourceCurrentStoredLiteralRowLineage.RowAt rootValue rootRow := by
    cases rootValue <;>
      simp only [InternedEdgeResidency.nodeEdges, List.not_mem_nil] at rootMember
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp rootMember
    exact .node found
  have initial : SourceCurrentConstrainedCapSourceHistory.Context
      (empty : State Symbol Guard) [] :=
    SourceCurrentConstrainedCapSourceHistory.empty_context
  have part := SourceCurrentBuildStructuralRowOrigins.build_row_origin
    (ordinarySymbols whole) [] empty rootValue heap initial built rootRow rootAt
  rw [wholeShape] at part
  change SourceRow (.node [.mk (literal "filter") filterGuard
      [ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal),
        ordinarySymbols (.union chunks.flatten)]]) [] empty rootValue heap rootRow at part
  cases part with
  | @node expressions inputs before raw after rows middle symbol guard children row sourceIndex outputIndex
      rowsBuilt made selected call same =>
    cases sourceIndex with
    | succ index =>
      have source := call.source
      simp only [List.getElem?_cons_succ, List.getElem?_nil] at source
      cases source
    | zero =>
      have source := call.source
      change some (EdgeSyntax.mk (literal "filter") filterGuard
          [ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal),
            ordinarySymbols (.union chunks.flatten)]) = some (.mk symbol guard children) at source
      have fields := Option.some.inj source
      cases fields
      have current : call.current = empty := by
        have earlier := call.earlier
        have observed := congrArg Outcome.state earlier
        simpa only [List.take_zero, buildEdges, Outcome.state] using observed.symm
      have called : buildMany
          [ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal),
            ordinarySymbols (.union chunks.flatten)] [] empty =
          .done call.values call.middle := by
        simpa only [current] using call.called
      have observedRows : buildEdges
          [.mk (literal "filter") filterGuard
            [ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal),
              ordinarySymbols (.union chunks.flatten)]] [] empty =
          .done [call.output] call.next := by
        simp only [buildEdges, called, Outcome.bind, work, call.made]
      have endpoints : rows = [call.output] ∧ middle = call.next :=
        Outcome.done.inj (rowsBuilt.symm.trans observedRows)
      have rootMade : run (makeNode [rootRow]) call.next = (rootValue, heap) := by
        have roots : rows = [rootRow] :=
          endpoints.1.trans (congrArg (fun edge => [edge]) same)
        have aligned : (rows, middle) = ([rootRow], call.next) := Prod.ext roots endpoints.2
        exact (congrArg (fun pair : List (EdgeValue Symbol Guard) × State Symbol Guard =>
          run (makeNode pair.1) pair.2) aligned).symm.trans made
      cases goalDone : build
          (ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal)) [] empty with
      | pending key state =>
        simp only [buildMany, goalDone, Outcome.bind] at called
        cases called
      | done goalValue candidateStart =>
        cases candidateDone : build (ordinarySymbols (.union chunks.flatten)) [] candidateStart with
        | pending key state =>
          simp only [buildMany, goalDone, candidateDone, Outcome.bind] at called
          cases called
        | done candidateValue candidateAfter =>
          have paired : [goalValue, candidateValue] = call.values ∧ candidateAfter = call.middle := by
            simpa only [buildMany, goalDone, candidateDone, Outcome.bind, Outcome.done.injEq] using called
          have candidateContext : SourceCurrentConstrainedCapSourceHistory.Context candidateStart [] := by
            simpa only [goalDone, Outcome.state] using
              initial.build (ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal))
          refine ⟨chunks, goalValue, candidateValue, candidateStart, candidateAfter, call.next,
            chunksRun, wholeShape, ?_, ?_, ?_, rfl, candidateContext, candidateDone, ?_,
            rootMade, ?_, factory⟩
          · simpa only [same] using call.symbol_eq
          · simpa only [same] using call.guard_eq
          · rw [← same, call.children_eq, ← paired.1]
          · simpa only [← paired.1, ← paired.2, same] using call.made
          · simpa only [← paired.2] using call.middle_growth

/-- A row from actual initial narrowing supplies the same original source filter interval. -/
theorem current_narrowed_filter_interval
    {Typing Key : Type}
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue heap)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool)
    (fuel : Nat) (narrowed : Value Symbol Guard)
    (narrowedAfter : State Symbol Guard)
    (narrowedCall : SourcePruningOuterNarrow.narrow holeKey fits admits metadata
      fuel 0 rootValue heap = .done narrowed narrowedAfter)
    (rootRow : EdgeValue Symbol Guard)
    (narrowedMember : rootRow ∈ InternedEdgeResidency.nodeEdges narrowed) :
    let ctx := SourceSynthesisCurrentContext.context lib query
    ∃ (chunks : List (List Expression))
        (goalValue candidateValue : Value Symbol Guard)
        (candidateStart candidateAfter edgeAfter : State Symbol Guard),
      (SourceSynthesisSelections.permutations ctx.argumentEdges).mapM
        (fun selected => SourceSynthesisFirstOrderConstruction.relevantRows
          ctx true signed.toNat (selected.map Prod.fst)) = .ok chunks ∧
      whole = SourceSynthesisFirstOrderConstruction.ofType (.union chunks.flatten)
        (SourceSynthesisCurrentContext.typeNode query.queryGoal) ∧
      rootRow.entry.key.symbol = literal "filter" ∧
      rootRow.entry.key.constraint = filterGuard ∧
      rootRow.children = [goalValue, candidateValue] ∧
      InternedFreshOrdinaryConstruction.build
        (ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal)) [] empty =
          .done goalValue candidateStart ∧
      SourceCurrentConstrainedCapSourceHistory.Context candidateStart [] ∧
      InternedFreshOrdinaryConstruction.build
        (ordinarySymbols (.union chunks.flatten)) [] candidateStart =
          .done candidateValue candidateAfter ∧
      run (makeEdge (literal "filter") filterGuard [goalValue, candidateValue]) candidateAfter =
        (rootRow, edgeAfter) ∧
      run (makeNode [rootRow]) edgeAfter = (rootValue, heap) ∧
      Grows candidateAfter heap ∧
      ∀ candidate ∈ chunks.flatten,
        ∃ rows : List Row, candidate = .node rows ∧
          ∀ (types function argument : Expression),
            EdgeSyntax.mk "app" appGuard
              [types, SourceSynthesisTypeSyntax.arrowMarker top, function, argument] ∈ rows →
            types = SourceSynthesisTypeSyntax.allTypes top
              (SourceSynthesisCurrentContext.constructorCatalog lib query) ∧
            ((∃ functionRows : List Row, function = .node functionRows) ∨
              ∃ pools : List (List Row), function = .union (pools.map fun rows => .node rows)) := by
  apply current_initial_filter_interval lib query signed whole accepted
    rootValue heap built rootRow
  exact SourceSynthesisCurrentInitialOuterNarrowRows.initial_outer_narrow_rows
    lib query signed whole accepted rootValue heap built metadata holeKey fits admits
    fuel narrowed narrowedAfter narrowedCall rootRow narrowedMember

end MicroCFTA.SourceSynthesisCurrentFirstFilterSourceLink
