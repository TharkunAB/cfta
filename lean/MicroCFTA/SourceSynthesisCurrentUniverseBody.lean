import MicroCFTA.SourceSynthesisCurrentTypeFieldCalls
import MicroCFTA.SourceSynthesisUniverseBody

/-!
# Labeled callback of the current type universe

The proof executes the mapped source body in its incoming labeled heap.
It derives an ordinary body with depth zero and its exact local free name.
Cleanup retains the resulting Mu. The row theorem retains the same marker,
ordered catalog rows and final heap. The root build supplies its reservation.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseBody
open Cache Language SourceSynthesisTypeSyntax
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency InternedFreshProbeKeys InternedRecordCoherence
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work finish)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)
open InternedOrdinaryUnionReadback
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisUniverseBody (descriptors rowSyntax body_syntax)
open SourceSynthesisProgramBuildRolesGeneric
  (mapSyntax mapChildren mapEdges mapChildren_eq_map)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

section Callback
variable [DecidableEq (EdgeKey Symbol Guard)]

private def RowReadback (label : String) (top : Guard) (children : List (Value Symbol Guard))
    (value : Value Symbol Guard) : Prop :=
  ∃ entry edge, value = .node entry [edge] (maximumDepth children) (childFree children) ∧
    edge.children = children ∧ edge.entry.key = ⟨literal label, children.map Value.referenceOf, top⟩

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem canonical_singleton (edge : EdgeValue Symbol Guard) : canonicalEdges [edge] = [edge] := by
  simp [canonicalEdges, EnumerationBuilderCaches.canonicalIds, List.eraseDups_cons]

private theorem variables_build (count : Nat) (name : Reference) (state : State Symbol Guard) :
    buildMany (List.replicate count (.var 0)) [.reference name] state =
      .done (List.replicate count (.reference name)) state := by
  induction count with
  | zero => simp [List.replicate, buildMany]
  | succ count ih => simp [List.replicate_succ, buildMany, build, Outcome.bind, ih]

private theorem one_row (top : Guard) (label : String) (children : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state middle : State Symbol Guard)
    (facts : Facts state) (inputs : InternedNestedProvenance.Values state environment)
    (values : List (Value Symbol Guard))
    (built : buildMany children environment state = .done values middle)
    (live : values.any (fun child => child.referenceOf == .empty) = false) :
    ∃ value final, build (.node [.mk (literal label) top children]) environment state = .done value final ∧
      RowReadback label top values value := by
  have checked := buildMany_verified children environment state facts inputs
  have middleFacts : Facts middle := by simpa only [built, Outcome.state] using checked.facts
  have available := checked.result values middle built
  let made := run (makeEdge (literal label) top values) middle
  have edgeChecked := edge_verified (literal label) top values middle middleFacts available
  have edgeFacts : Facts made.2 := edgeChecked.facts
  have resident : EdgeResident made.2 made.1 := edgeChecked.result _ _ rfl
  have childrenEq : made.1.children = values :=
    InternedShallowValues.makeEdge_children (literal label) top values middle
      middleFacts.coherent middleFacts.cached available
  have keyEq : made.1.entry.key = ⟨literal label, values.map Value.referenceOf, top⟩ :=
    InternedOrdinaryAbsenceReplay.makeEdge_key (literal label) top values middle middleFacts.coherent
  have normalized : canonicalEdges (surviving [made.1]) = [made.1] := by
    simp only [surviving, List.filter_cons, childrenEq, live, Bool.not_false, ↓reduceIte,
      List.filter_nil, canonical_singleton]
  obtain ⟨entry, readback⟩ := identifyNode_readback [made.1] made.2 edgeFacts.coherent edgeFacts.linked
    (by intro edge member; have same := List.mem_singleton.mp member; subst edge; exact resident)
  have nodeEq : (run (makeNode [made.1]) made.2).1 =
      .node entry [made.1] (maximumDepth values) (childFree values) := by
    simpa only [makeNode, normalized, run, identifyNode, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, childrenEq] using readback
  refine ⟨(run (makeNode [made.1]) made.2).1, (run (makeNode [made.1]) made.2).2,
    ?_, entry, made.1, nodeEq, childrenEq, keyEq⟩
  simp only [build, buildEdges, built, Outcome.bind, work]
  rfl

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem input_reference (state : State Symbol Guard) (name : Reference)
    (available : Available state (.reference name)) :
    InternedNestedProvenance.Values state [.reference name] := by
  intro value member
  have same := List.mem_singleton.mp member
  subst value
  exact available

private theorem row_build (top : Guard) (descriptor : String × Nat) (name : Reference)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state (.reference name)) :
    ∃ value final, build (mapSyntax literal (rowSyntax top descriptor)) [.reference name] state = .done value final ∧
      RowReadback descriptor.1 top (List.replicate descriptor.2 (.reference name)) value := by
  obtain ⟨value, final, built, shape⟩ := one_row top descriptor.1
    (List.replicate descriptor.2 (.var 0)) _ state state facts
    (input_reference state name available) _ (variables_build descriptor.2 name state) (by
      apply List.any_eq_false.mpr
      intro child member
      have same := List.eq_of_mem_replicate member
      subst child
      simp [Value.referenceOf])
  refine ⟨value, final, ?_, shape⟩
  simpa only [rowSyntax, mapSyntax, mapEdges, mapChildren_eq_map,
    List.map_replicate] using built

private theorem rows_build (top : Guard) (rows : List (String × Nat)) (name : Reference)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state (.reference name)) :
    ∃ values final, buildMany (rows.map (fun descriptor => mapSyntax literal (rowSyntax top descriptor))) [.reference name] state = .done values final ∧
      All₂ (fun descriptor value =>
        RowReadback descriptor.1 top (List.replicate descriptor.2 (.reference name)) value) rows values := by
  induction rows generalizing state with
  | nil => exact ⟨[], state, by simp [buildMany], .nil⟩
  | cons descriptor rest ih =>
      obtain ⟨value, middle, head, shape⟩ := row_build top descriptor name state facts available
      have checked := build_verified (mapSyntax literal (rowSyntax top descriptor)) [.reference name] state facts
        (input_reference state name available)
      have middleFacts : Facts middle := by simpa only [head, Outcome.state] using checked.facts
      have later : Available middle (.reference name) := by
        simpa only [head, Outcome.state] using checked.available _ available
      obtain ⟨values, final, tail, shapes⟩ := ih middle middleFacts later
      exact ⟨value :: values, final, by simp only [List.map_cons, buildMany, head, Outcome.bind, tail],
        .cons shape shapes⟩

private theorem arrow_build (top : Guard) (name : Reference) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state (.reference name)) :
    ∃ marker value final,
      build (mapSyntax literal (arrowType top (.var 0) (.var 0))) [.reference name] state = .done value final ∧
      RowReadback "(->)" top [] marker ∧ RowReadback "->" top [marker, .reference name, .reference name] value := by
  obtain ⟨marker, middle, markerDone, markerShape⟩ := row_build top ("(->)", 0) name state facts available
  have markerBuilt : build (mapSyntax literal (arrowMarker top)) [.reference name] state = .done marker middle := by
    simpa only [rowSyntax, List.replicate_zero, arrowMarker] using markerDone
  have childrenDone : buildMany [mapSyntax literal (arrowMarker top), .var 0, .var 0] [.reference name] state =
      .done [marker, .reference name, .reference name] middle := by
    simp only [buildMany, markerBuilt, Outcome.bind, build]
    rfl
  have markerReadback := markerShape
  obtain ⟨entry, edge, markerEq, _, _⟩ := markerShape
  have live : [marker, .reference name, .reference name].any
      (fun child => child.referenceOf == .empty) = false := by
    simp [markerEq, Value.referenceOf]
  obtain ⟨value, final, done, shape⟩ := one_row top "->" _ _ state middle facts
    (input_reference state name available) _ childrenDone live
  refine ⟨marker, value, final, ?_, markerReadback, shape⟩
  simpa only [arrowType, mapSyntax, mapEdges, mapChildren] using done

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem output_origin {A B : Type} {R : A → B → Prop} {inputs : List A} {outputs : List B}
    (aligned : All₂ R inputs outputs) : ∀ value ∈ outputs, ∃ input ∈ inputs, R input value := by
  induction aligned with
  | nil => intro value member; cases member
  | @cons first value rest values own tail ih =>
      intro selected member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨first, List.mem_cons_self, own⟩
      · obtain ⟨input, present, related⟩ := ih selected later
        exact ⟨input, List.mem_cons_of_mem _ present, related⟩

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem first_two {A B : Type} {R : A → B → Prop} {first second : A} {rest : List A}
    {outputs : List B} (aligned : All₂ R (first :: second :: rest) outputs) :
    ∃ a b later, outputs = a :: b :: later ∧ R first a ∧ R second b := by
  cases aligned with
  | cons head tail =>
      cases tail with
      | cons next rest => exact ⟨_, _, _, rfl, head, next⟩

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem row_different (top : Guard) (first second : String) (different : first ≠ second)
    (leftChildren rightChildren : List (Value Symbol Guard)) (left right : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state)
    (leftResident : Resident state left) (rightResident : Resident state right)
    (leftShape : RowReadback first top leftChildren left)
    (rightShape : RowReadback second top rightChildren right) : left.referenceOf ≠ right.referenceOf := by
  intro equal
  have same := resident_reference_injective state coherent left right leftResident rightResident equal
  obtain ⟨le, lx, leftEq, _, leftKey⟩ := leftShape
  obtain ⟨re, rx, rightEq, _, rightKey⟩ := rightShape
  have edges := congrArg nodeEdges same
  rw [leftEq, rightEq] at edges
  have rowEq : lx = rx := (List.cons.inj edges).1
  have keys := leftKey.symm.trans ((congrArg (fun edge => edge.entry.key) rowEq).trans rightKey)
  exact different (congrArg Prod.fst (congrArg EdgeKey.symbol keys))

private def Good (name : Reference) (value : Value Symbol Guard) : Prop :=
  value.depth = 0 ∧ ∀ other ∈ value.free, other = name

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem good_reference (name : Reference) : Good name (.reference name) := by
  simp [Good, Value.depth, Value.free]

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem row_children (name : Reference) (label : String) (top : Guard)
    (children : List (Value Symbol Guard)) (value : Value Symbol Guard)
    (shape : RowReadback label top children value) (good : ∀ child ∈ children, Good name child) :
    ∀ edge ∈ nodeEdges value, ∀ child ∈ edge.children, Good name child := by
  obtain ⟨entry, source, rfl, childrenEq, _⟩ := shape
  intro edge included child member
  have same := List.mem_singleton.mp included
  subst edge
  rw [childrenEq] at member
  exact good child member

private theorem body_inputs (top : Guard) (catalog : List (String × Nat)) (name : Reference)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state (.reference name)) :
    ∃ marker arrow values middle,
      buildMany (mapSyntax literal (arrowType top (.var 0) (.var 0)) ::
        (descriptors catalog).map (fun descriptor => mapSyntax literal (rowSyntax top descriptor)))
        [.reference name] state = .done (arrow :: values) middle ∧
      RowReadback "(->)" top [] marker ∧ RowReadback "->" top [marker, .reference name, .reference name] arrow ∧
      All₂ (fun descriptor value =>
        RowReadback descriptor.1 top (List.replicate descriptor.2 (.reference name)) value)
        (descriptors catalog) values := by
  obtain ⟨marker, arrow, afterArrow, arrowDone, markerShape, arrowShape⟩ :=
    arrow_build top name state facts available
  have checked := build_verified (mapSyntax literal (arrowType top (.var 0) (.var 0))) [.reference name] state facts
    (input_reference state name available)
  have arrowFacts : Facts afterArrow := by simpa only [arrowDone, Outcome.state] using checked.facts
  have later : Available afterArrow (.reference name) := by
    simpa only [arrowDone, Outcome.state] using checked.available _ available
  obtain ⟨values, middle, rowsDone, shapes⟩ := rows_build top (descriptors catalog) name afterArrow arrowFacts later
  exact ⟨marker, arrow, values, middle, by simp only [buildMany, arrowDone, Outcome.bind, rowsDone],
    markerShape, arrowShape, shapes⟩

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem labeled_row_keys (top : Guard) (name : Reference)
    (rows : List (String × Nat)) (values : List (Value Symbol Guard))
    (aligned : All₂ (fun descriptor value =>
      RowReadback descriptor.1 top (List.replicate descriptor.2 (.reference name)) value) rows values) :
    All₂ (fun (descriptor : String × Nat) (row : EdgeValue Symbol Guard) =>
      row.children = List.replicate descriptor.2 (.reference name) ∧
      row.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref name), top⟩)
      rows (values.flatMap nodeEdges) := by
  induction aligned with
  | nil => exact .nil
  | @cons descriptor value rest values own tail ih =>
      obtain ⟨entry, edge, same, children, key⟩ := own
      simp only [List.flatMap_cons, same, nodeEdges, List.singleton_append]
      exact .cons ⟨children, by simpa [List.map_replicate, Value.referenceOf] using key⟩ ih

/-- The same callback retains its actual arrow, catalog rows, and resident records. -/
private theorem labeled_callback_rows (top : Guard) (catalog : List (String × Nat))
    (name : Reference) (state : State Symbol Guard) (facts : Facts state)
    (available : Available state (.reference name)) :
    ∃ (entry : Interned NodeKey) (marker : Value Symbol Guard)
      (arrow : EdgeValue Symbol Guard) (rows : List (EdgeValue Symbol Guard))
      (final : State Symbol Guard),
      callback (mapSyntax literal (allTypesBody top catalog)) [] name state =
        .done (.node entry (canonicalEdges (arrow :: rows)) 0 [name]) final ∧
      RowReadback "(->)" top [] marker ∧
      arrow.children = [marker, .reference name, .reference name] ∧
      arrow.entry.key = ⟨literal "->", [marker.referenceOf, .ref name, .ref name], top⟩ ∧
      All₂ (fun (descriptor : String × Nat) (row : EdgeValue Symbol Guard) =>
        row.children = List.replicate descriptor.2 (.reference name) ∧
        row.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref name), top⟩)
        (descriptors catalog) rows ∧
      Facts final ∧ Available final (.node entry (canonicalEdges (arrow :: rows)) 0 [name]) ∧
      (∀ row ∈ arrow :: rows, EdgeResident final row) ∧
      marker.free = [] ∧ Available final marker ∧
      (∀ row ∈ canonicalEdges (arrow :: rows), row.entry.key.constraint = top ∧
        ∀ child ∈ row.children, child = marker ∨ child = .reference name) ∧
      arrow ∈ canonicalEdges (arrow :: rows) := by
  obtain ⟨marker, arrow, values, middle, partsDone, markerShape, arrowShape, aligned⟩ :=
    body_inputs top catalog name state facts available
  have checked := buildMany_verified
    (mapSyntax literal (arrowType top (.var 0) (.var 0)) ::
      (descriptors catalog).map (fun descriptor => mapSyntax literal (rowSyntax top descriptor)))
    [.reference name] state facts (input_reference state name available)
  have middleFacts : Facts middle := by simpa only [partsDone, Outcome.state] using checked.facts
  have inputs := checked.result (arrow :: values) middle partsDone
  have resident : ∀ value ∈ arrow :: values, Resident middle value := fun value member => (inputs value member).resident
  have ordinary : ∀ value ∈ arrow :: values, Ordinary value := by
    intro value member
    rcases List.mem_cons.mp member with rfl | later
    · obtain ⟨entry, edge, same, _, _⟩ := arrowShape
      exact ⟨entry, [edge], _, _, same⟩
    · obtain ⟨descriptor, _, shape⟩ := output_origin aligned value later
      obtain ⟨entry, edge, same, _, _⟩ := shape
      exact ⟨entry, [edge], _, _, same⟩
  obtain ⟨first, second, remaining, valuesEq, firstShape, secondShape⟩ := first_two aligned
  have firstMem : first ∈ arrow :: values := by simp [valuesEq]
  have secondMem : second ∈ arrow :: values := by simp [valuesEq]
  have different : first.referenceOf ≠ second.referenceOf :=
    row_different top "var1" "var2" (by decide) [] [] first second middle middleFacts.coherent
      (resident first firstMem) (resident second secondMem) firstShape secondShape
  have unionEq := makeUnion_eq_makeNode (arrow :: values) middle middleFacts.coherent middleFacts.linked
    ordinary resident first second firstMem secondMem different
  have markerReadback := markerShape
  obtain ⟨markerEntry, markerEdge, markerEq, _, _⟩ := markerShape
  have markerGood : Good name marker := by
    simp [markerEq, Good, Value.depth, Value.free, maximumDepth, childFree, canonicalFree]
  have allGood : ∀ child ∈ ((arrow :: values).flatMap nodeEdges).flatMap EdgeValue.children, Good name child := by
    intro child member
    obtain ⟨edge, selected, included⟩ := List.mem_flatMap.mp member
    obtain ⟨value, input, edgeMember⟩ := List.mem_flatMap.mp selected
    rcases List.mem_cons.mp input with same | later
    · subst value
      apply row_children name "->" top _ arrow arrowShape ?_ edge edgeMember child included
      intro source present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl | rfl
      · exact markerGood
      · exact good_reference name
      · exact good_reference name
    · obtain ⟨descriptor, _, shape⟩ := output_origin aligned value later
      apply row_children name descriptor.1 top _ value shape ?_ edge edgeMember child included
      intro source present
      have same := List.eq_of_mem_replicate present
      subst source
      exact good_reference name
  obtain ⟨arrowEntry, arrowEdge, arrowEq, arrowChildren, arrowKey⟩ := arrowShape
  have witness : ∃ edge ∈ (arrow :: values).flatMap nodeEdges,
      EqualityLeafProjectionPhysical.dead edge = false ∧
      ∃ child ∈ edge.children, name ∈ child.free := by
    refine ⟨arrowEdge, ?_, ?_, .reference name, ?_, by simp [Value.free]⟩
    · apply List.mem_flatMap.mpr
      exact ⟨arrow, List.mem_cons_self, by simp [arrowEq, nodeEdges]⟩
    · simp [EqualityLeafProjectionPhysical.dead, arrowChildren, markerEq, Value.referenceOf]
    · simp [arrowChildren]
  obtain ⟨entry, nodeEq⟩ := makeNode_zero_singleton ((arrow :: values).flatMap nodeEdges) middle
    middleFacts.coherent middleFacts.linked (rows_resident _ middle middleFacts.linked resident) name
    (fun child member => (allGood child member).1)
    (fun child member => (allGood child member).2) witness
  let result := run (makeUnion (arrow :: values)) middle
  have resultEq : result.1 =
      .node entry (canonicalEdges (surviving ((arrow :: values).flatMap nodeEdges))) 0 [name] :=
    (congrArg Prod.fst unionEq).trans nodeEq
  have bodyDone : build (mapSyntax literal (allTypesBody top catalog)) [.reference name] state = .done result.1 result.2 := by
    simp only [body_syntax, mapSyntax, mapChildren_eq_map, List.map_cons,
      List.map_map, Function.comp_def, build, partsDone, Outcome.bind, work]
    rfl
  have done : callback (mapSyntax literal (allTypesBody top catalog)) [] name state = .done result.1 result.2 := by
    simp only [callback, bodyDone, Outcome.bind, work, resultEq, withoutSelfReference, run]
  have finalChecked := callback_verified (mapSyntax literal (allTypesBody top catalog)) [] name state facts
    (input_reference state name available)
  have finalFacts : Facts result.2 := by
    simpa only [done, Outcome.state] using finalChecked.facts
  have rawAligned := labeled_row_keys top name (descriptors catalog) values aligned
  have rawEq : (arrow :: values).flatMap nodeEdges = arrowEdge :: values.flatMap nodeEdges := by
    simp only [List.flatMap_cons, arrowEq, nodeEdges, List.singleton_append]
  have rawSurvive : surviving (arrowEdge :: values.flatMap nodeEdges) =
      arrowEdge :: values.flatMap nodeEdges := by
    unfold surviving
    apply List.filter_eq_self.mpr
    intro edge member
    rcases List.mem_cons.mp member with rfl | later
    · simp [arrowChildren, markerEq, Value.referenceOf]
    · obtain ⟨descriptor, _, related⟩ := output_origin rawAligned edge later
      simp [related.1, Value.referenceOf]
  have canonicalResult : result.1 =
      .node entry (canonicalEdges (arrowEdge :: values.flatMap nodeEdges)) 0 [name] := by
    simpa only [rawEq, rawSurvive] using resultEq
  have growth : Grows middle result.2 :=
    (InternedConstructorTemplates.run_correct (makeUnion (arrow :: values)) middle middleFacts.coherent.valid).2
  have rawResident : ∀ row ∈ arrowEdge :: values.flatMap nodeEdges, EdgeResident result.2 row := by
    intro row member
    apply edge_grows middle result.2 growth row
    exact rows_resident (arrow :: values) middle middleFacts.linked resident row (rawEq.symm ▸ member)
  have rawFields : ∀ row ∈ arrowEdge :: values.flatMap nodeEdges,
      row.entry.key.constraint = top ∧ ∀ child ∈ row.children, child = marker ∨ child = .reference name := by
    intro row member
    rcases List.mem_cons.mp member with same | later
    · subst row
      refine ⟨congrArg EdgeKey.constraint arrowKey, ?_⟩
      intro child included
      rw [arrowChildren] at included
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using included
    · obtain ⟨descriptor, _, related⟩ := output_origin rawAligned row later
      refine ⟨congrArg EdgeKey.constraint related.2, ?_⟩
      intro child included
      rw [related.1] at included
      exact Or.inr (List.eq_of_mem_replicate included)
  have markerClosed : marker.free = [] := by
    simp [markerEq, Value.free, childFree, canonicalFree]
  have markerAvailable : Available result.2 marker :=
    finalFacts.cached.edges arrowEdge.entry.key arrowEdge (rawResident arrowEdge List.mem_cons_self) marker
      (by rw [arrowChildren]; exact List.mem_cons_self)
  refine ⟨entry, marker, arrowEdge, values.flatMap nodeEdges, result.2,
    canonicalResult ▸ done, markerReadback, arrowChildren, ?_, rawAligned, finalFacts,
    ?_, rawResident, markerClosed, markerAvailable, ?_, ?_⟩
  · simpa only [List.map_cons, List.map_nil, Value.referenceOf] using arrowKey
  · rw [← canonicalResult]
    exact finalChecked.result _ _ done
  · intro row member
    exact rawFields row (canonicalEdges_member _ row member)
  · exact canonicalEdges_retains result.2 finalFacts.coherent _ arrowEdge rawResident List.mem_cons_self

/-- The actual mapped callback derives its ordinary node and exact local free name. -/
private theorem labeled_callback_node (top : Guard) (catalog : List (String × Nat))
    (name : Reference) (state : State Symbol Guard) (facts : Facts state)
    (available : Available state (.reference name)) :
    ∃ (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard))
      (final : State Symbol Guard),
      callback (mapSyntax literal (allTypesBody top catalog)) [] name state =
        .done (.node entry edges 0 [name]) final := by
  obtain ⟨entry, marker, arrow, rows, final, done, _⟩ :=
    labeled_callback_rows top catalog name state facts available
  exact ⟨entry, _, final, done⟩

end Callback

/-- The current catalog supplies the actual labeled callback body. -/
theorem current_types_callback_node
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (name : Reference)
    (state : State Symbol Guard) (facts : Facts state)
    (available : Available state (.reference name)) :
    ∃ (entry : Interned InternedBinderProtocol.NodeKey)
      (edges : List (EdgeValue Symbol Guard)) (final : State Symbol Guard),
      InternedFreshOrdinaryFacts.callback
        (ordinarySymbols (allTypesBody top
          (SourceSynthesisCurrentContext.constructorCatalog lib query)))
        [] name state = .done (.node entry edges 0 [name]) final := by
  simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
    labeled_callback_node top (SourceSynthesisCurrentContext.constructorCatalog lib query)
      name state facts available

/-- The actual current callback supplies the body that retains its reserved Mu. -/
theorem current_types_callback_cleanup
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (entry : Interned NodeKey)
    (state : State Symbol Guard) (facts : Facts state)
    (available : Available state (.reference (.interned entry.identity)))
    (depth ordinary : Value Symbol Guard) :
    ∃ (body : Value Symbol Guard) (final : State Symbol Guard),
      InternedFreshOrdinaryFacts.callback
        (ordinarySymbols (allTypesBody top
          (SourceSynthesisCurrentContext.constructorCatalog lib query)))
        [] (.interned entry.identity) state = .done body final ∧
      finish true (.mu entry body depth ordinary) = .mu entry body depth ordinary ∧
      (Value.mu entry body depth ordinary).free = [] := by
  obtain ⟨bodyEntry, edges, final, called⟩ :=
    current_types_callback_node lib query (.interned entry.identity) state facts available
  refine ⟨.node bodyEntry edges 0 [.interned entry.identity], final, called, ?_, ?_⟩
  · simp [finish, cleanup, Value.free, Value.referenceOf]
  · simp [Value.free]


/-- The current catalog supplies the exact callback rows in the same returned heap. -/
theorem current_types_callback_rows
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (name : Reference)
    (state : State Symbol Guard) (facts : Facts state)
    (available : Available state (.reference name)) :
    ∃ (entry : Interned NodeKey) (marker : Value Symbol Guard)
      (arrow : EdgeValue Symbol Guard) (rows : List (EdgeValue Symbol Guard))
      (final : State Symbol Guard),
      callback (ordinarySymbols (allTypesBody top
        (SourceSynthesisCurrentContext.constructorCatalog lib query))) [] name state =
        .done (.node entry (canonicalEdges (arrow :: rows)) 0 [name]) final ∧
      (∃ (markerEntry : Interned NodeKey) (markerRow : EdgeValue Symbol Guard),
        marker = .node markerEntry [markerRow] 0 [] ∧ markerRow.children = [] ∧
        markerRow.entry.key = ⟨literal "(->)", [], top⟩) ∧
      arrow.children = [marker, .reference name, .reference name] ∧
      arrow.entry.key = ⟨literal "->", [marker.referenceOf, .ref name, .ref name], top⟩ ∧
      All₂ (fun (descriptor : String × Nat) (row : EdgeValue Symbol Guard) =>
        row.children = List.replicate descriptor.2 (.reference name) ∧
        row.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref name), top⟩)
        (descriptors (SourceSynthesisCurrentContext.constructorCatalog lib query)) rows ∧
      Facts final ∧ Available final (.node entry (canonicalEdges (arrow :: rows)) 0 [name]) ∧
      (∀ row ∈ arrow :: rows, EdgeResident final row) ∧
      marker.free = [] ∧ Available final marker ∧
      (∀ row ∈ canonicalEdges (arrow :: rows), row.entry.key.constraint = top ∧
        ∀ child ∈ row.children, child = marker ∨ child = .reference name) ∧
      arrow ∈ canonicalEdges (arrow :: rows) := by
  obtain ⟨entry, marker, arrow, rows, final, called, markerShape, children, key,
    aligned, finalFacts, nodeAvailable, resident, markerClosed, markerAvailable, fields, retained⟩ :=
    labeled_callback_rows top (SourceSynthesisCurrentContext.constructorCatalog lib query)
      name state facts available
  obtain ⟨markerEntry, markerRow, markerEq, markerChildren, markerKey⟩ := markerShape
  refine ⟨entry, marker, arrow, rows, final, ?_, ?_, children, key, aligned,
    finalFacts, nodeAvailable, resident, markerClosed, markerAvailable, fields, retained⟩
  · simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using called
  · refine ⟨markerEntry, markerRow, ?_, markerChildren, markerKey⟩
    simpa [maximumDepth, childFree, canonicalFree] using markerEq



end MicroCFTA.SourceSynthesisCurrentUniverseBody
