import MicroCFTA.SourceSynthesisCurrentUniverseOwnership
import MicroCFTA.SourcePruningEnumerationSelectedValue
import MicroCFTA.SourceCurrentStoredSubstitutionCalls

namespace MicroCFTA.SourceSynthesisCurrentUniverseUnfoldedRowInputs
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment leaves manyLeaves edgeLeaves input encode encodeEdges)
open InternedStoredSubstitutionRebind (replacement)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable [DecidableEq (EdgeKey Symbol Constraint)]
set_option autoImplicit false

/- Note [Actual unfolded universe row inputs]
The actual selected Mu unfolds its stored body with the full Mu as replacement.
The existing indexed row execution theorem retains one original source row.
Its child trace supplies the same ordered stored calls at the actual heaps.
Source marker calls are closed. Source reference calls read the replacement.
The source catalog then fixes the actual row symbol and child count.
The arrow marker stays separate from the two Type operands.
No child Type result, future assignment, or completed model is assumed.
This row-shape theorem does not preserve Type roles through later intersections.
-/

omit [DecidableEq (EdgeKey Symbol Constraint)] in
private theorem output_origin {A B : Type} {R : A → B → Prop} {inputs : List A} {outputs : List B}
    (aligned : All₂ R inputs outputs) : ∀ value ∈ outputs, ∃ source ∈ inputs, R source value := by
  induction aligned with
  | nil => intro value member; cases member
  | @cons first value rest values own tail ih =>
      intro selected member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨first, List.mem_cons_self, own⟩
      · obtain ⟨source, present, related⟩ := ih selected later
        exact ⟨source, List.mem_cons_of_mem _ present, related⟩

omit [DecidableEq (EdgeKey Symbol Constraint)] in
private theorem captured_row_leaves (rows : List Edge) (row : Edge)
    (member : row ∈ rows) (leaf : Node) (present : leaf ∈ manyLeaves row.children) :
    leaf ∈ edgeLeaves rows := by
  induction rows with
  | nil => cases member
  | cons first rest ih =>
      cases first with
      | mk entry children =>
          rcases List.mem_cons.mp member with rfl | member
          · simpa only [edgeLeaves, EdgeValue.children] using
              List.mem_append_left (edgeLeaves rest) present
          · simpa only [edgeLeaves] using List.mem_append_right (manyLeaves children) (ih member)

private theorem calls_inputs (environment : Environment Symbol Constraint) (name : Reference)
    (marker : Node) (closed : marker.free = [])
    {originals outputs : List Node}
    {before after : InternedConstructorTemplates.State Symbol Constraint}
    (calls : Calls environment originals before outputs after)
    (kinds : ∀ child ∈ originals, child = marker ∨ child = .reference name) :
    outputs = originals.map (input environment) := by
  induction calls with
  | nil => rfl
  | cons original originals before middle after output outputs called rest ih =>
      have pureCall : InternedFreshOrdinaryStoredSubstitution.execute original environment before =
          .done (input environment original) before := by
        rcases kinds original List.mem_cons_self with same | same
        · subst original
          rw [InternedFreshOrdinaryStoredSubstitution.execute_eq marker environment before
            (.closed marker closed)]
          simpa only [InternedStoredSubstitutionScope.input_closed marker environment closed] using
            InternedStoredSubstitutionScope.execute_closed marker environment before closed
        · subst original
          rw [InternedFreshOrdinaryStoredSubstitution.execute_eq (.reference name) environment before
            (.reference name)]
          simpa only [input] using
            InternedStoredSubstitutionScope.execute_reference name environment before
      have outputSame : output = input environment original :=
        (Outcome.done.inj (pureCall.symm.trans called)).1.symm
      change output :: outputs = input environment original :: originals.map (input environment)
      rw [outputSame, ih (fun child member => kinds child (List.mem_cons_of_mem _ member))]

private theorem selected_mu_execute
    (entry : Interned NodeKey) (body depth ordinary : Node)
    (before after : InternedConstructorTemplates.State Symbol Constraint)
    (fuel : Nat) (prepared : Node)
    (actual : SourcePruningEnumerationSelectedValue.run fuel (.mu entry body depth ordinary) before =
      .done prepared after) :
    InternedFreshOrdinaryStoredSubstitution.execute body
      (replacement (.interned entry.identity) (.mu entry body depth ordinary)) before =
        .done prepared after := by
  cases unfolded : InternedFreshOrdinaryStoredSubstitution.unfold
      (.mu entry body depth ordinary) before with
  | pending key reached =>
      simp only [SourcePruningEnumerationSelectedValue.run, unfolded] at actual
      cases actual
  | done value reached =>
      have same : value = prepared ∧ reached = after := by
        simpa only [SourcePruningEnumerationSelectedValue.run, unfolded,
          MergedSourceComparison.Result.done.injEq] using actual
      obtain ⟨rfl, rfl⟩ := same
      simpa only [InternedFreshOrdinaryStoredSubstitution.unfold, replacement] using unfolded

theorem original_universe_unfolded_row_inputs
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
          row.children = [marker, .mu entry body depth ordinary, .mu entry body depth ordinary])
 := by
  obtain ⟨bodyEntry, marker, arrow, rows, bodyEq, markerRead, arrowChildren, arrowKey,
      aligned, markerClosed, _markerAvailable, kinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseOwnership.current_stored_universe_rows
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
  let sources := canonicalEdges (arrow :: rows)
  let fullUniverse : Node := .mu entry body depth ordinary
  let environment : Environment Symbol Constraint := replacement (.interned entry.identity) fullUniverse
  let context := leaves body
  have universeAvailable : Available nativeBefore fullUniverse :=
    facts.cached.nodes key fullUniverse (sourceGrowth.nodeRecords key fullUniverse stored)
  have bodyAvailable : Available nativeBefore body :=
    universeAvailable.children body (by simp only [fullUniverse, children, List.mem_cons_self])
  have replacements : InternedStoredSubstitution.Replacements nativeBefore environment := by
    intro name value found
    by_cases same : name = .interned entry.identity
    · simp only [environment, replacement, same, ite_true, Option.some.injEq] at found
      subst value
      exact universeAvailable
    · simp only [environment, replacement, same, ite_false] at found
      cases found
  have contextAvailable : Values nativeBefore context :=
    InternedStoredSubstitution.leaves_available body nativeBefore bodyAvailable
  have inputsAvailable : Values nativeBefore (context.map (input environment)) :=
    InternedStoredSubstitution.inputs_available body environment nativeBefore bodyAvailable replacements
  have executed := selected_mu_execute entry body depth ordinary nativeBefore nativeAfter fuel prepared actual
  change InternedFreshOrdinaryConstruction.build (encode context [] body)
    (context.map (input environment)) nativeBefore = .done prepared nativeAfter at executed
  have compiled : encode context [] body = .node (encodeEdges context [] sources) := by
    rw [bodyEq, encode.eq_def]
    simp only [Value.free, List.isEmpty_cons, Bool.false_eq_true, ite_false]
  rw [compiled] at executed
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp present
  obtain ⟨sourceIndex, sourceRow, rebuiltRows, middle, current, childAfter, next, values,
      found, _rebuilt, _rowsDone, _madeNode, _earlier, trace, _madeEdge, _later,
      symbolSame, guardSame, childrenSame, _arity⟩ :=
    SourceCurrentSubstitutionRowExecution.node_indexed context [] (context.map (input environment))
      sources nativeBefore prepared nativeAfter facts inputsAvailable executed index row selected
  have sourceMember : sourceRow ∈ sources := List.mem_of_getElem? found
  have contextEq : context = edgeLeaves sources := by
    dsimp only [context]
    rw [bodyEq, leaves.eq_def]
    simp only [Value.free, List.isEmpty_cons, Bool.false_eq_true, ite_false]
  have childAvailable : Values nativeBefore sourceRow.children := by
    intro child member
    have bodySources : Available nativeBefore (.node bodyEntry sources 0 [.interned entry.identity]) := by
      simpa only [bodyEq] using bodyAvailable
    exact bodySources.children child (List.mem_flatMap.mpr ⟨sourceRow, sourceMember, member⟩)
  have covered : ∀ leaf ∈ manyLeaves sourceRow.children, leaf ∈ context := by
    intro leaf member
    rw [contextEq]
    exact captured_row_leaves sources sourceRow sourceMember leaf member
  have calls := SourceCurrentStoredSubstitutionCalls.from_encoded context environment nativeBefore
    facts.coherent contextAvailable trace childAvailable covered
  have valuesSame : values = sourceRow.children.map (input environment) :=
    calls_inputs environment (.interned entry.identity) marker markerClosed calls
      (kinds sourceRow sourceMember).2
  have rowChildren : row.children = sourceRow.children.map (input environment) :=
    childrenSame.trans valuesSame
  have originalMember : sourceRow ∈ InternedEdgeResidency.nodeEdges body := by
    simpa only [bodyEq, InternedEdgeResidency.nodeEdges] using sourceMember
  have referenceInput : input environment (.reference (.interned entry.identity)) = fullUniverse := by
    simp only [input, environment, replacement, ite_true, Option.getD_some]
  refine ⟨sourceRow, originalMember, symbolSame, guardSame, rowChildren, ?_⟩
  have original := InternedProbeProvenance.canonicalEdges_member (arrow :: rows) sourceRow sourceMember
  rcases List.mem_cons.mp original with same | later
  · subst sourceRow
    right
    obtain ⟨markerEntry, markerRow, markerEq, markerChildren, markerKey⟩ := markerRead
    refine ⟨marker, markerEntry, markerRow, markerEq, markerChildren, markerKey, ?_, ?_⟩
    · exact symbolSame.trans (congrArg EdgeKey.symbol arrowKey)
    · rw [rowChildren, arrowChildren]
      simp only [List.map_cons, List.map_nil,
        InternedStoredSubstitutionScope.input_closed marker environment markerClosed, referenceInput]
  · left
    obtain ⟨descriptor, described, related⟩ := output_origin aligned sourceRow later
    refine ⟨descriptor.1, descriptor.2, described, ?_, ?_⟩
    · exact symbolSame.trans (congrArg EdgeKey.symbol related.2)
    · rw [rowChildren, related.1]
      simp only [List.map_replicate, referenceInput]

end MicroCFTA.SourceSynthesisCurrentUniverseUnfoldedRowInputs
