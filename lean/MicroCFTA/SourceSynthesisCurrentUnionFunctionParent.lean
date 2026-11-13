import MicroCFTA.SourceSynthesisCurrentFunctionParent
import MicroCFTA.EqualityLeafProjectionUnion

/-!
# Identity rows in source function-pool unions

The actual application call supplies a union of source node pools.
Ordinary union construction retains the complete identity row and Type child.
This case includes the default size-two function pools.
Later edits require their actual origin history.
-/

namespace MicroCFTA.SourceSynthesisCurrentUnionFunctionParent
open Language Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top generalize)
open SourceSynthesisFirstOrderConstruction (Expression Row)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "ordinaryChildren" => SourceSynthesisUniverseCallerBoundary.ordinaryChildren
variable [DecidableEq FullSyntax.Formula] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq FullSyntax.Formula] in
private theorem node_build_receipt (sourceRows : List Row)
    (before : State Symbol Guard) (context : InternedFreshOrdinaryContext.Context before [])
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : build (ordinarySymbols (.node sourceRows)) [] before = .done value after) :
    ∃ rows nodeHeap,
      InternedFreshOrdinaryConstruction.buildEdges
        (SourceSynthesisUniverseCallerBoundary.ordinaryEdges sourceRows) [] before =
        .done rows nodeHeap ∧
      run (makeNode rows) nodeHeap = (value, after) ∧
      InternedNestedFacts.Facts nodeHeap ∧
      InternedNestedProvenance.Edges nodeHeap rows ∧
      EqualityLeafProjectionUnion.OrdinaryRoot value := by
  let nativeRows := SourceSynthesisUniverseCallerBoundary.ordinaryEdges sourceRows
  have lowered : (InternedFreshOrdinaryConstruction.buildEdges nativeRows [] before).bind
      (fun rows nodeHeap => InternedNestedConstruction.work (makeNode rows) nodeHeap) =
      .done value after := by
    simpa only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, build] using actual
  cases rowsDone : InternedFreshOrdinaryConstruction.buildEdges nativeRows [] before with
  | pending key state =>
      simp only [rowsDone, Outcome.bind] at lowered
      cases lowered
  | done rows nodeHeap =>
      have checked := InternedFreshOrdinaryFacts.buildEdges_verified nativeRows [] before
        context.normal.facts context.inputs
      have facts : InternedNestedFacts.Facts nodeHeap := by
        simpa only [rowsDone, Outcome.state] using checked.facts
      have resident := checked.result rows nodeHeap rowsDone
      have finished : InternedNestedConstruction.work (makeNode rows) nodeHeap =
          .done value after := by
        simpa only [rowsDone, Outcome.bind] using lowered
      have endpoints : (run (makeNode rows) nodeHeap).1 = value ∧
          (run (makeNode rows) nodeHeap).2 = after := by
        simpa only [InternedNestedConstruction.work, Outcome.done.injEq] using finished
      have made : run (makeNode rows) nodeHeap = (value, after) :=
        Prod.ext endpoints.1 endpoints.2
      have ordinary := EqualityLeafProjectionUnion.makeNode_ordinary rows nodeHeap
        facts.coherent facts.linked resident
      exact ⟨rows, nodeHeap, rfl, made, facts, resident,
        by simpa only [made] using ordinary⟩

omit [DecidableEq FullSyntax.Formula] in
private theorem node_pools_ordinary (pools : List (List Row))
    (before : State Symbol Guard) (context : InternedFreshOrdinaryContext.Context before [])
    (values : List (Value Symbol Guard)) (after : State Symbol Guard)
    (actual : buildMany (ordinaryChildren (pools.map fun rows => .node rows)) [] before =
      .done values after) :
    ∀ value ∈ values, EqualityLeafProjectionUnion.OrdinaryRoot value := by
  induction pools generalizing before values with
  | nil =>
      simp only [List.map_nil, SourceSynthesisUniverseCallerBoundary.ordinaryChildren,
        buildMany, Outcome.done.injEq] at actual
      obtain ⟨rfl, rfl⟩ := actual
      intro value member
      cases member
  | cons sourceRows pools ih =>
      cases first : build (ordinarySymbols (.node sourceRows)) [] before with
      | pending key state =>
          simp only [List.map_cons, SourceSynthesisUniverseCallerBoundary.ordinaryChildren,
            buildMany, first, Outcome.bind] at actual
          cases actual
      | done value middle =>
          cases tail : buildMany (ordinaryChildren (pools.map fun rows => .node rows)) [] middle with
          | pending key state =>
              simp only [List.map_cons, SourceSynthesisUniverseCallerBoundary.ordinaryChildren,
                buildMany, first, tail, Outcome.bind] at actual
              cases actual
          | done remaining final =>
              simp only [List.map_cons, SourceSynthesisUniverseCallerBoundary.ordinaryChildren,
                buildMany, first, tail, Outcome.bind, Outcome.done.injEq] at actual
              obtain ⟨rfl, rfl⟩ := actual
              obtain ⟨_rows, _nodeHeap, _built, _made, _facts, _resident, headOrdinary⟩ :=
                node_build_receipt sourceRows before context value middle first
              have nextContext : InternedFreshOrdinaryContext.Context middle [] := by
                simpa only [first, Outcome.state] using context.build (ordinarySymbols (.node sourceRows))
              have restOrdinary := ih middle nextContext remaining tail
              intro selected member
              rcases List.mem_cons.mp member with rfl | later
              · exact headOrdinary
              · exact restOrdinary selected later

omit [DecidableEq FullSyntax.Formula] in
private theorem union_ordinary (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (available : InternedNestedProvenance.Values state values)
    (ordinary : ∀ value ∈ values, EqualityLeafProjectionUnion.OrdinaryRoot value) :
    EqualityLeafProjectionUnion.OrdinaryRoot (run (makeUnion values) state).1 := by
  have nodes : ∀ value ∈ distinctNodes (values.flatMap unionMembers),
      EqualityLeafProjectionUnion.NodeRoot value := by
    intro value member
    obtain ⟨source, included, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    have plain := ordinary source included
    cases source <;> simp_all [EqualityLeafProjectionUnion.OrdinaryRoot, unionMembers,
      EqualityLeafProjectionUnion.NodeRoot]
  cases shape : distinctNodes (values.flatMap unionMembers) with
  | nil => simp only [makeUnion, shape, run, EqualityLeafProjectionUnion.OrdinaryRoot]
  | cons first rest =>
      cases rest with
      | nil =>
          have firstNode := nodes first (by simp only [shape, List.mem_singleton])
          cases first <;> simp_all [makeUnion, EqualityLeafProjectionUnion.OrdinaryRoot,
            EqualityLeafProjectionUnion.NodeRoot, run]
      | cons second tail =>
          have extracted := EqualityLeafProjectionUnion.ordinary_edges (first :: second :: tail)
            (by intro value member; exact nodes value (by rw [shape]; exact member))
          have resident := InternedEdgeResidency.ordinaryEdges_resident (first :: second :: tail) _ state facts.linked
            (fun value member => (InternedUnionFilterFusion.selected_available values state available value
              (by rw [shape]; exact member)).resident) extracted
          have output := EqualityLeafProjectionUnion.makeNode_ordinary _ state facts.coherent facts.linked resident
          simpa only [makeUnion, shape, extracted] using output

/-- The actual union function child retains its complete identity row and Type handle. -/
theorem actual_app_identity_union_function_parent
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
    (original : SourceSynthesisOriginalTypeAnnotations.OriginalType lib
      (.tFun (.tVar "a") (.tVar "a")))
    (pools : List (List Row)) (poolIndex : Nat) (functionRows : List Row)
    (poolSource : pools[poolIndex]? = some functionRows)
    (sourceIndex : Nat) (name : String)
    (identity : functionRows[sourceIndex]? = some (.mk name top
      [generalize (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query))
        (SourceSynthesisPr210TypeReflection.encodeTy (.tFun (.tVar "a") (.tVar "a")))]))
    (argument : Expression)
    {parentExpressions : List (EdgeSyntax Symbol Guard)} {before after : State Symbol Guard}
    {parentOutputs : List (EdgeValue Symbol Guard)} {parentIndex : Nat}
    (parent : SourceCurrentStoredMuRetainedAlignment.RowCall parentExpressions []
      before parentOutputs after heap parentIndex (literal "app")
      (SourceSynthesisGeneralizeSyntax.eqGuard
        [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
      [ordinarySymbols (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query)),
        ordinarySymbols (SourceSynthesisTypeSyntax.arrowMarker top),
        ordinarySymbols (.union (pools.map fun rows => .node rows)), ordinarySymbols argument]) :
    ∃ functionValue functionStart functionAfter values unionStart
        componentValue componentStart componentAfter rows nodeHeap,
      parent.output.children[2]? = some functionValue ∧
      InternedFreshOrdinaryContext.Context functionStart [] ∧
      build (ordinarySymbols (.union (pools.map fun rows => .node rows))) [] functionStart =
        .done functionValue functionAfter ∧
      Grows functionStart heap ∧ Grows functionAfter heap ∧
      buildMany (ordinaryChildren (pools.map fun rows => .node rows)) [] functionStart =
        .done values unionStart ∧
      run (makeUnion values) unionStart = (functionValue, functionAfter) ∧
      values[poolIndex]? = some componentValue ∧
      InternedFreshOrdinaryContext.Context componentStart [] ∧
      build (ordinarySymbols (.node functionRows)) [] componentStart =
        .done componentValue componentAfter ∧
      Grows componentStart heap ∧ Grows componentAfter heap ∧
      EqualityLeafProjectionUnion.OrdinaryRoot functionValue ∧
      InternedFreshOrdinaryConstruction.buildEdges
        (SourceSynthesisUniverseCallerBoundary.ordinaryEdges functionRows) [] componentStart =
        .done rows nodeHeap ∧
      run (makeNode rows) nodeHeap = (componentValue, componentAfter) ∧
      ∃ call : SourceCurrentStoredMuRetainedAlignment.RowCall
          (SourceSynthesisUniverseCallerBoundary.ordinaryEdges functionRows) []
          componentStart rows nodeHeap heap sourceIndex (literal name) top
          [ordinarySymbols (generalize
            (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query))
            (SourceSynthesisPr210TypeReflection.encodeTy (.tFun (.tVar "a") (.tVar "a"))))],
        ∃ canonicalIndex : Nat, ∃ typeValue,
          (InternedEdgeResidency.nodeEdges functionValue)[canonicalIndex]? = some call.output ∧
          call.output.children = [typeValue] ∧ Available heap typeValue ∧ typeValue.free = [] ∧
          SourceEqualityAnnotationLanguage.Annotated
            (SourceSynthesisNativeTypeTrace.Origin
              (SourceSynthesisCurrentSourceGuards.encodedLibrary lib)) typeValue ∧
          ∀ ambient : InternedGuardedLanguage.Env Symbol,
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
              ambient typeValue
              (.node (literal "->")
                [.node (literal "(->)") [], .node (literal "var1") [], .node (literal "var1") []]) := by
  let field : Expression := generalize
    (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query))
    (SourceSynthesisPr210TypeReflection.encodeTy (.tFun (.tVar "a") (.tVar "a")))
  let nativePools := ordinaryChildren (pools.map fun rows => .node rows)
  let nativeRows := SourceSynthesisUniverseCallerBoundary.ordinaryEdges functionRows
  obtain ⟨functionValue, functionStart, functionAfter, selectedFunction, functionContext,
    functionBuilt, firstGrowth, lastGrowth⟩ :=
    SourceSynthesisOriginalProgramTypeFields.many_call
      [ordinarySymbols (allTypes top (SourceSynthesisCurrentContext.constructorCatalog lib query)),
        ordinarySymbols (SourceSynthesisTypeSyntax.arrowMarker top),
        ordinarySymbols (.union (pools.map fun rows => .node rows)), ordinarySymbols argument]
      parent.current parent.middle heap parent.context parent.values parent.called
      parent.middle_growth 2 (ordinarySymbols (.union (pools.map fun rows => .node rows))) rfl
  have parentSlot : parent.output.children[2]? = some functionValue := by
    rw [parent.children_eq]
    exact selectedFunction
  have lowered : (buildMany nativePools [] functionStart).bind
      (fun values unionStart => InternedNestedConstruction.work (makeUnion values) unionStart) =
      .done functionValue functionAfter := by
    simpa only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, build] using functionBuilt
  cases manyDone : buildMany nativePools [] functionStart with
  | pending key state =>
      simp only [manyDone, Outcome.bind] at lowered
      cases lowered
  | done values unionStart =>
      have manyChecked := InternedFreshOrdinaryFacts.buildMany_verified nativePools [] functionStart
        functionContext.normal.facts functionContext.inputs
      have unionContext : InternedFreshOrdinaryContext.Context unionStart [] := by
        simpa only [manyDone, Outcome.state] using functionContext.many nativePools
      have valuesAvailable := manyChecked.result values unionStart manyDone
      have finished : InternedNestedConstruction.work (makeUnion values) unionStart =
          .done functionValue functionAfter := by
        simpa only [manyDone, Outcome.bind] using lowered
      have endpoints : (run (makeUnion values) unionStart).1 = functionValue ∧
          (run (makeUnion values) unionStart).2 = functionAfter := by
        simpa only [InternedNestedConstruction.work, Outcome.done.injEq] using finished
      have unionMade : run (makeUnion values) unionStart = (functionValue, functionAfter) :=
        Prod.ext endpoints.1 endpoints.2
      have unionChecked := InternedNestedFacts.union_verified values unionStart
        unionContext.normal.facts valuesAvailable
      have unionGrowth : Grows unionStart heap := grows_trans
        (by simpa only [InternedNestedConstruction.work, unionMade, Outcome.state] using unionChecked.growth)
        lastGrowth
      have sourcePool : nativePools[poolIndex]? = some (ordinarySymbols (.node functionRows)) := by
        change (ordinaryChildren (pools.map fun rows => .node rows))[poolIndex]? = _
        rw [← SourceSynthesisLabelProgramBuildRoles.mapChildren_ordinaryChildren,
          SourceSynthesisProgramBuildRolesGeneric.mapChildren_eq_map,
          List.getElem?_map, List.getElem?_map, poolSource]
        simp only [Option.map_some, SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols]
      obtain ⟨componentValue, componentStart, componentAfter, selectedComponent, componentContext,
        componentBuilt, componentFirstGrowth, componentLastGrowth⟩ :=
        SourceSynthesisOriginalProgramTypeFields.many_call nativePools functionStart unionStart heap
          functionContext values manyDone unionGrowth poolIndex
          (ordinarySymbols (.node functionRows)) sourcePool
      obtain ⟨rows, nodeHeap, rowsDone, nodeMade, facts, resident, _componentOrdinary⟩ :=
        node_build_receipt functionRows componentStart componentContext componentValue componentAfter componentBuilt
      have nodeChecked := InternedNestedFacts.node_verified rows nodeHeap facts resident
      have nodeGrowth : Grows nodeHeap heap := grows_trans
        (by simpa only [InternedNestedConstruction.work, nodeMade, Outcome.state] using nodeChecked.growth)
        componentLastGrowth
      have sourceLookup : nativeRows[sourceIndex]? =
          some (.mk (literal name) top [ordinarySymbols field]) := by
        change (SourceSynthesisUniverseCallerBoundary.ordinaryEdges functionRows)[sourceIndex]? = _
        rw [← SourceSynthesisLabelProgramBuildRoles.mapEdges_ordinaryEdges,
          SourceSynthesisProgramBuildRolesGeneric.mapEdges_eq_map, List.getElem?_map, identity]
        simp only [field, Option.map_some, SourceSynthesisProgramBuildRolesGeneric.mapEdge,
          SourceSynthesisProgramBuildRolesGeneric.mapChildren,
          SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols]
      obtain ⟨call⟩ := SourceCurrentStoredMuRetainedAlignment.row_call nativeRows []
        componentStart nodeHeap heap componentContext rows rowsDone nodeGrowth sourceIndex
        (literal name) top [ordinarySymbols field] sourceLookup
      obtain ⟨typeValue, typeSlot, available, closed, annotated, member⟩ :=
        SourceSynthesisCurrentIdentityNativeWitness.identity_component_native_member
          formulas solver lib query signed whole accepted rootValue heap built original call
      have children : call.output.children = [typeValue] := by
        have called := call.called
        cases childDone : build (ordinarySymbols field) [] call.current with
        | pending key state =>
            simp only [InternedFreshOrdinaryConstruction.buildMany, childDone, Outcome.bind] at called
            cases called
        | done child next =>
            have actual : [child] = call.values ∧ next = call.middle := by
              simpa only [InternedFreshOrdinaryConstruction.buildMany, childDone,
                Outcome.bind, Outcome.done.injEq] using called
            have one : call.output.children = [child] := call.children_eq.trans actual.1.symm
            have same : child = typeValue := by
              have found := typeSlot
              rw [one] at found
              exact Option.some.inj found
            simpa only [same] using one
      have notEmpty : typeValue ≠ .empty := by
        intro same
        have acceptedTerm := member (fun _ _ => False)
        simp only [same, InternedGuardedLanguage.meaning] at acceptedTerm
      have referenceNotEmpty : typeValue.referenceOf ≠ .empty := by
        intro same
        exact notEmpty ((EqualityLeafProjectionPhysical.reference_empty typeValue).mp same)
      have liveRow : EqualityLeafProjectionPhysical.dead call.output = false := by
        simpa only [EqualityLeafProjectionPhysical.dead, children, List.any_cons,
          List.any_nil, Bool.or_false] using (beq_eq_false_iff_ne.mpr referenceNotEmpty)
      have rawMember : call.output ∈ rows := List.mem_of_getElem? call.selected
      have kept : call.output ∈ canonicalEdges (surviving rows) :=
        (EqualityLeafProjectionPhysical.normalized_member nodeHeap facts.coherent rows
          resident call.output).mpr ⟨rawMember, liveRow⟩
      have componentMember : call.output ∈ InternedEdgeResidency.nodeEdges componentValue := by
        have edges := EqualityLeafProjectionPhysical.makeNode_edges rows nodeHeap facts.coherent
          facts.linked resident
        rw [nodeMade] at edges
        rw [edges]
        exact kept
      have allOrdinary : ∀ value ∈ values, EqualityLeafProjectionUnion.OrdinaryRoot value :=
        node_pools_ordinary pools functionStart functionContext values unionStart manyDone
      have functionOrdinary : EqualityLeafProjectionUnion.OrdinaryRoot functionValue := by
        have ordinary := union_ordinary values unionStart unionContext.normal.facts valuesAvailable allOrdinary
        simpa only [unionMade] using ordinary
      have allLive : ∀ value ∈ values, ∀ edge ∈ InternedEdgeResidency.nodeEdges value,
          EqualityLeafProjectionPhysical.dead edge = false := by
        intro value included edge found
        exact InternedLiveEdges.resident_live unionStart unionContext.normal.live value
          (valuesAvailable value included).resident edge found
      have retained := (EqualityLeafProjectionUnion.union_edges values unionStart
        unionContext.normal.facts.coherent unionContext.normal.facts.linked
        (fun value included => (valuesAvailable value included).resident)
        allOrdinary allLive call.output).mpr
          ⟨componentValue, List.mem_of_getElem? selectedComponent, componentMember⟩
      have actualMember : call.output ∈ InternedEdgeResidency.nodeEdges functionValue := by
        simpa only [unionMade] using retained
      obtain ⟨canonicalIndex, canonicalSlot⟩ := List.mem_iff_getElem?.mp actualMember
      exact ⟨functionValue, functionStart, functionAfter, values, unionStart,
        componentValue, componentStart, componentAfter, rows, nodeHeap, parentSlot,
        functionContext, functionBuilt, firstGrowth, lastGrowth, manyDone, unionMade,
        selectedComponent, componentContext, componentBuilt, componentFirstGrowth,
        componentLastGrowth, functionOrdinary, rowsDone, nodeMade, call,
        canonicalIndex, typeValue, canonicalSlot, children, available, closed, annotated, member⟩

end MicroCFTA.SourceSynthesisCurrentUnionFunctionParent
