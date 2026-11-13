import MicroCFTA.SourceSynthesisCurrentConstruction
import MicroCFTA.SourceSynthesisCurrentProgramStructure
import MicroCFTA.SourceCurrentBuildStructuralRowOrigins
import MicroCFTA.SourceCurrentConstrainedCapSourceHistory
import MicroCFTA.SourceCurrentStoredRowCallGrowth
import MicroCFTA.SourceSynthesisCurrentCandidateAppOperands

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

private theorem filtered_candidate_role (candidate goal : Expression)
    (checked : SourceSynthesisProgramRoles.ProgramSyntax
      (SourceSynthesisFirstOrderConstruction.ofType candidate goal)) :
    SourceSynthesisProgramRoles.ProgramSyntax candidate := by
  change SourceSynthesisProgramRoles.ProgramSyntax
    (.node [.mk "filter" filterGuard [goal, candidate]]) at checked
  cases checked with
  | node _ rows =>
      have own := rows _ (List.mem_singleton_self _)
      generalize selected : (.mk "filter" filterGuard [goal, candidate] : Row) = row at own
      cases own with
      | annotated name annotation =>
          have lengths := congrArg (fun row : Row => match row with
            | .mk _ _ children => children.length) selected
          change (2 : Nat) = 1 at lengths
          omega
      | application actual _ _ =>
          rw [← selected] at actual
          have names := congrArg (fun expression : Expression => match expression with
            | .node [.mk name _ _] => name
            | _ => "") actual
          change ("app" : String) = "filter" at names
          exact False.elim ((by decide : ("app" : String) ≠ "filter") names)
      | filter actual candidateRole =>
          rename_i sourceCandidates sourceGoal
          rw [← selected] at actual
          have children := congrArg (fun expression : Expression => match expression with
            | .node [.mk _ _ children] => children
            | _ => []) actual
          change [sourceGoal, sourceCandidates] = [goal, candidate] at children
          have same : sourceCandidates = candidate :=
            (List.cons.inj (List.cons.inj children).2).1
          exact same ▸ candidateRole

private theorem stable_guard (input output : EqualityNormalize.Constraints)
    (prepared : EqualityNormalize.complete (EqualityNormalize.prepare input) = output)
    (stable : EqualityNormalize.congruenceStep output = some output) :
    SourceSynthesisGeneralizeSyntax.eqGuard input = (⟨some output, .top⟩ : Guard) := by
  have positive : 0 < EqualityTermination.normalizationBound input := Nat.zero_lt_succ _
  unfold SourceSynthesisGeneralizeSyntax.eqGuard EqualityNormalize.mkEqConstraints
  rw [prepared]
  cases bound : EqualityTermination.normalizationBound input with
  | zero => rw [bound] at positive; exact (Nat.not_lt_zero _ positive).elim
  | succ fuel =>
      simp only [EqualityNormalize.fixMaybe, stable, ite_true,
        SymbolicEqualityBridge.resultClasses]

private theorem app_payload : appGuard =
    (⟨some [[[0], [2, 0, 2]], [[1], [2, 0, 0]], [[2, 0, 1], [3, 0]]], .top⟩ : Guard) := by
  apply stable_guard <;> cbv

private theorem top_ne_app : (top : Guard) ≠ appGuard := by
  intro same
  have payload := congrArg (fun guard : Guard => guard.equalities) same
  rw [app_payload] at payload
  change (some [] : Option EqualityNormalize.Constraints) =
    some [[[0], [2, 0, 2]], [[1], [2, 0, 0]], [[2, 0, 1], [3, 0]]] at payload
  cases payload

/-- The selected original member retains its source app call and current catalog operands. -/
theorem current_candidate_source_app
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (chunks : List (List Expression))
    (chunksRun :
      (SourceSynthesisSelections.permutations
        (SourceSynthesisCurrentContext.context lib query).argumentEdges).mapM
        (fun selected => SourceSynthesisFirstOrderConstruction.relevantRows
          (SourceSynthesisCurrentContext.context lib query) true signed.toNat
          (selected.map Prod.fst)) = .ok chunks)
    (candidateStart candidateAfter : State Symbol Guard)
    (candidateValue : Value Symbol Guard) (ancestor : EdgeValue Symbol Guard)
    (part : SourceCurrentBuildStructuralRowOrigins.SourceRow
      (ordinarySymbols (.union chunks.flatten)) [] candidateStart candidateValue candidateAfter ancestor)
    (ancestorSymbol : ancestor.entry.key.symbol = literal "app")
    (ancestorGuard : ancestor.entry.key.constraint = appGuard) :
    ∃ (candidateIndex : Nat) (sourceRows : List Row)
        (values : List (Value Symbol Guard)) (unionMiddle : State Symbol Guard)
        (memberValue : Value Symbol Guard) (memberStart memberAfter : State Symbol Guard),
      chunks.flatten[candidateIndex]? = some (.node sourceRows) ∧
      InternedFreshOrdinaryConstruction.buildMany (ordinaryChildren chunks.flatten) [] candidateStart =
        .done values unionMiddle ∧
      run (makeUnion values) unionMiddle = (candidateValue, candidateAfter) ∧
      values[candidateIndex]? = some memberValue ∧
      InternedFreshOrdinaryConstruction.buildMany
        ((ordinaryChildren chunks.flatten).take candidateIndex) [] candidateStart =
          .done (values.take candidateIndex) memberStart ∧
      SourceCurrentConstrainedCapSourceHistory.Context memberStart [] ∧
      InternedFreshOrdinaryConstruction.build (ordinarySymbols (.node sourceRows)) [] memberStart =
        .done memberValue memberAfter ∧
      InternedFreshOrdinaryConstruction.buildMany
        ((ordinaryChildren chunks.flatten).drop (candidateIndex + 1)) [] memberAfter =
          .done (values.drop (candidateIndex + 1)) unionMiddle ∧
      Grows memberAfter candidateAfter ∧
      ∃ (rawRows : List (EdgeValue Symbol Guard)) (nodeMiddle : State Symbol Guard)
          (sourceRowIndex outputRowIndex : Nat) (function argument : Expression),
        InternedFreshOrdinaryConstruction.buildEdges (ordinaryEdges sourceRows) [] memberStart =
          .done rawRows nodeMiddle ∧
        run (makeNode rawRows) nodeMiddle = (memberValue, memberAfter) ∧
        (InternedEdgeResidency.nodeEdges memberValue)[outputRowIndex]? = some ancestor ∧
        ∃ call : SourceCurrentStoredMuRetainedAlignment.RowCall
            (ordinaryEdges sourceRows) [] memberStart rawRows nodeMiddle candidateAfter
            sourceRowIndex (literal "app") appGuard
            [ordinarySymbols (SourceSynthesisTypeSyntax.allTypes top
              (SourceSynthesisCurrentContext.constructorCatalog lib query)),
              ordinarySymbols (SourceSynthesisTypeSyntax.arrowMarker top),
              ordinarySymbols function, ordinarySymbols argument],
          call.output = ancestor ∧
          ((∃ functionRows : List Row, function = .node functionRows) ∨
            ∃ pools : List (List Row), function = .union (pools.map fun rows => .node rows))
 := by
  obtain ⟨actualChunks, actualChunksRun, wholeShape, candidateFacts⟩ :=
    SourceSynthesisCurrentCandidateAppOperands.current_candidate_app_operands
      lib query signed whole accepted
  have chunksSame : actualChunks = chunks := Except.ok.inj (actualChunksRun.symm.trans chunksRun)
  subst actualChunks
  have wholeRole :=
    (SourceSynthesisCurrentProgramStructure.current_root_structure lib query signed whole accepted).1
  rw [wholeShape] at wholeRole
  have candidateRole := filtered_candidate_role _ _ wholeRole
  change SourceCurrentBuildStructuralRowOrigins.SourceRow
    (.union (ordinaryChildren chunks.flatten)) [] candidateStart candidateValue candidateAfter ancestor at part
  cases part with
  | union built made source selected earlier context called suffix nested =>
      rename_i values unionMiddle expression memberValue memberStart memberAfter candidateIndex
      have mappedSource := source
      rw [← SourceSynthesisLabelProgramBuildRoles.mapChildren_ordinaryChildren,
        SourceSynthesisProgramBuildRolesGeneric.mapChildren_eq_map,
        List.getElem?_map] at mappedSource
      cases sourceChoice : chunks.flatten[candidateIndex]? with
      | none =>
          simp only [sourceChoice, Option.map_none] at mappedSource
          cases mappedSource
      | some candidate =>
          obtain ⟨sourceRows, rfl, operands⟩ :=
            candidateFacts candidate (List.mem_of_getElem? sourceChoice)
          have expressionSame : ordinarySymbols (.node sourceRows) = expression := by
            apply Option.some.inj
            simpa only [sourceChoice, Option.map_some,
              SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using mappedSource
          cases expressionSame
          have rowsChecked : ∀ row ∈ sourceRows, SourceSynthesisProgramRoles.ProgramRowSyntax row := by
            cases candidateRole with
            | union members checked =>
                have memberRole := checked _ (List.mem_of_getElem? sourceChoice)
                cases memberRole with
                | node rows checked => exact checked
          have afterContext : SourceCurrentConstrainedCapSourceHistory.Context memberAfter [] := by
            simpa only [called, InternedNestedConstruction.Outcome.state] using
              context.build (ordinarySymbols (.node sourceRows))
          have suffixChecked := InternedFreshOrdinaryFacts.buildMany_verified
            ((ordinaryChildren chunks.flatten).drop (candidateIndex + 1)) [] memberAfter
            afterContext.base.normal.facts afterContext.base.inputs
          have suffixGrowth : Grows memberAfter unionMiddle := by
            simpa only [suffix, InternedNestedConstruction.Outcome.state] using suffixChecked.growth
          have unionContext : SourceCurrentConstrainedCapSourceHistory.Context unionMiddle [] := by
            simpa only [suffix, InternedNestedConstruction.Outcome.state] using
              afterContext.many ((ordinaryChildren chunks.flatten).drop (candidateIndex + 1))
          have unionGrowth : Grows unionMiddle candidateAfter := by
            simpa only [made] using
              (InternedConstructorTemplates.run_correct (makeUnion values) unionMiddle
                unionContext.base.normal.facts.coherent.valid).2
          have memberGrowth := grows_trans suffixGrowth unionGrowth
          change SourceCurrentBuildStructuralRowOrigins.SourceRow
            (.node (ordinaryEdges sourceRows)) [] memberStart memberValue memberAfter ancestor at nested
          cases nested with
          | node rawBuilt nodeMade outputSelected call sameOutput =>
              rename_i rawRows nodeMiddle ownSymbol ownGuard nativeChildren sourceRowIndex outputRowIndex
              have mappedRow := call.source
              rw [← SourceSynthesisLabelProgramBuildRoles.mapEdges_ordinaryEdges,
                SourceSynthesisProgramBuildRolesGeneric.mapEdges_eq_map,
                List.getElem?_map] at mappedRow
              cases rowChoice : sourceRows[sourceRowIndex]? with
              | none =>
                  simp only [rowChoice, Option.map_none] at mappedRow
                  cases mappedRow
              | some row =>
                  cases row with
                  | mk name sourceGuard sourceChildren =>
                      have fields : EdgeSyntax.mk (literal name) sourceGuard (ordinaryChildren sourceChildren) =
                          .mk ownSymbol ownGuard nativeChildren := by
                        apply Option.some.inj
                        simpa only [rowChoice, Option.map_some,
                          SourceSynthesisProgramBuildRolesGeneric.mapEdge,
                          SourceSynthesisLabelProgramBuildRoles.mapChildren_ordinaryChildren] using mappedRow
                      cases fields
                      have outputName : call.output.entry.key.symbol = literal "app" := by
                        simpa only [sameOutput] using ancestorSymbol
                      have sourceName : name = "app" :=
                        congrArg Prod.fst (call.symbol_eq.symm.trans outputName)
                      have outputGuard : call.output.entry.key.constraint = appGuard := by
                        simpa only [sameOutput] using ancestorGuard
                      have sourceGuardSame : ownGuard = appGuard :=
                        call.guard_eq.symm.trans outputGuard
                      subst name
                      have sourceRole := rowsChecked _ (List.mem_of_getElem? rowChoice)
                      generalize selectedRow : (EdgeSyntax.mk "app" ownGuard sourceChildren : Row) =
                        sourceRow at sourceRole
                      cases sourceRole with
                      | annotated name annotation =>
                          have guardSame := congrArg (fun row : Row => match row with
                            | .mk _ guard _ => guard) selectedRow
                          change ownGuard = top at guardSame
                          exact False.elim (top_ne_app (guardSame.symm.trans sourceGuardSame))
                      | @application types function argument row actual _ _ =>
                          rw [← selectedRow] at actual
                          have rowSame : EdgeSyntax.mk "app" appGuard
                              [types, SourceSynthesisTypeSyntax.arrowMarker top, function, argument] =
                              EdgeSyntax.mk "app" ownGuard sourceChildren :=
                            (List.cons.inj (Syntax.node.inj actual)).1
                          cases rowSame
                          have appMember : EdgeSyntax.mk "app" appGuard
                              [types, SourceSynthesisTypeSyntax.arrowMarker top, function, argument] ∈ sourceRows :=
                            List.mem_of_getElem? rowChoice
                          obtain ⟨typesSame, functionShape⟩ := operands _ _ _ appMember
                          subst types
                          refine ⟨candidateIndex, sourceRows, values, unionMiddle,
                            memberValue, memberStart, memberAfter, sourceChoice, built, made,
                            selected, earlier, context, called, suffix, memberGrowth,
                            rawRows, nodeMiddle, sourceRowIndex, outputRowIndex,
                            function, argument, rawBuilt, nodeMade, outputSelected,
                            call.grows memberGrowth, sameOutput, functionShape⟩
                      | filter actual _ =>
                          rw [← selectedRow] at actual
                          have names := congrArg (fun expression : Expression => match expression with
                            | .node [.mk name _ _] => name
                            | _ => "") actual
                          change ("filter" : String) = "app" at names
                          exact False.elim ((by decide : ("filter" : String) ≠ "app") names)

end MicroCFTA.SourceSynthesisCurrentFirstFilterSourceLink
