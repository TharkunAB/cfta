import MicroCFTA.SourceSynthesisUniverseNativeInput
import MicroCFTA.InternedOrdinaryUnionReadback
import MicroCFTA.InternedShallowValues
import MicroCFTA.InternedOrdinaryAbsenceReplay
import MicroCFTA.InternedBinderFreeDepthBound

/-!
# Actual ordinary callback of the default type universe

The proof executes the original source syntax. Each declared alternative
builds one ordinary row. The source union keeps the arrow row, four rigid
leaves, and catalog rows after canonical edge normalization. Catalog rows
can repeat. They can overlap the distinguished rows.
-/
namespace MicroCFTA.SourceSynthesisUniverseBody
open Cache Language SourceSynthesisTypeSyntax
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency InternedFreshProbeKeys InternedRecordCoherence
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference)
open InternedOrdinaryUnionReadback

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

/-- The four rigid alternatives precede every original catalog entry. -/
def descriptors (catalog : List (String × Nat)) : List (String × Nat) :=
  [("var1", 0), ("var2", 0), ("var3", 0), ("var4", 0)] ++ catalog

/-- One literal source alternative has its declared arity of local variables. -/
def rowSyntax (top : Guard) (descriptor : String × Nat) : Expr Guard :=
  .node [.mk descriptor.1 top (List.replicate descriptor.2 (.var 0))]

/-- Complete canonical row readback includes the requested children and guard. -/
def RowReadback (label : String) (top : Guard) (children : List (Value String Guard))
    (value : Value String Guard) : Prop :=
  ∃ entry edge, value = .node entry [edge] (maximumDepth children) (childFree children) ∧
    edge.children = children ∧ edge.entry.key = ⟨label, children.map Value.referenceOf, top⟩

omit [DecidableEq (EdgeKey String Guard)] in
/-- The original body is the arrow followed by the same literal row alternatives. -/
theorem body_syntax (top : Guard) (catalog : List (String × Nat)) :
    allTypesBody top catalog = .union
      (arrowType top (.var 0) (.var 0) :: (descriptors catalog).map (rowSyntax top)) := by
  simp [allTypesBody, descriptors, rowSyntax]

omit [DecidableEq (EdgeKey String Guard)] in
private theorem canonical_singleton (edge : EdgeValue String Guard) : canonicalEdges [edge] = [edge] := by
  simp [canonicalEdges, EnumerationBuilderCaches.canonicalIds, List.eraseDups_cons]

private theorem variables_build (count : Nat) (name : Reference) (state : State String Guard) :
    buildMany (List.replicate count (.var 0)) [.reference name] state =
      .done (List.replicate count (.reference name)) state := by
  induction count with
  | zero => simp [List.replicate, buildMany]
  | succ count ih => simp [List.replicate_succ, buildMany, build, Outcome.bind, ih]

private theorem one_row (top : Guard) (label : String) (children : List (Expr Guard))
    (environment : List (Value String Guard)) (state middle : State String Guard)
    (facts : Facts state) (inputs : InternedNestedProvenance.Values state environment)
    (values : List (Value String Guard))
    (built : buildMany children environment state = .done values middle)
    (live : values.any (fun child => child.referenceOf == .empty) = false) :
    ∃ value final, build (.node [.mk label top children]) environment state = .done value final ∧
      RowReadback label top values value := by
  have checked := buildMany_verified children environment state facts inputs
  have middleFacts : Facts middle := by simpa only [built, Outcome.state] using checked.facts
  have available := checked.result values middle built
  let made := run (makeEdge label top values) middle
  have edgeChecked := edge_verified label top values middle middleFacts available
  have edgeFacts : Facts made.2 := edgeChecked.facts
  have resident : EdgeResident made.2 made.1 := edgeChecked.result _ _ rfl
  have childrenEq : made.1.children = values :=
    InternedShallowValues.makeEdge_children label top values middle
      middleFacts.coherent middleFacts.cached available
  have keyEq : made.1.entry.key = ⟨label, values.map Value.referenceOf, top⟩ :=
    InternedOrdinaryAbsenceReplay.makeEdge_key label top values middle middleFacts.coherent
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

omit [DecidableEq (EdgeKey String Guard)] in
private theorem input_reference (state : State String Guard) (name : Reference)
    (available : Available state (.reference name)) :
    InternedNestedProvenance.Values state [.reference name] := by
  intro value member
  have same := List.mem_singleton.mp member
  subst value
  exact available

private theorem row_build (top : Guard) (descriptor : String × Nat) (name : Reference)
    (state : State String Guard) (facts : Facts state) (available : Available state (.reference name)) :
    ∃ value final, build (rowSyntax top descriptor) [.reference name] state = .done value final ∧
      RowReadback descriptor.1 top (List.replicate descriptor.2 (.reference name)) value := by
  apply one_row top descriptor.1 _ _ state state facts (input_reference state name available)
    _ (variables_build descriptor.2 name state)
  apply List.any_eq_false.mpr
  intro child member
  have same := List.eq_of_mem_replicate member
  subst child
  simp [Value.referenceOf]

private theorem rows_build (top : Guard) (rows : List (String × Nat)) (name : Reference)
    (state : State String Guard) (facts : Facts state) (available : Available state (.reference name)) :
    ∃ values final, buildMany (rows.map (rowSyntax top)) [.reference name] state = .done values final ∧
      All₂ (fun descriptor value =>
        RowReadback descriptor.1 top (List.replicate descriptor.2 (.reference name)) value) rows values := by
  induction rows generalizing state with
  | nil => exact ⟨[], state, by simp [buildMany], .nil⟩
  | cons descriptor rest ih =>
      obtain ⟨value, middle, head, shape⟩ := row_build top descriptor name state facts available
      have checked := build_verified (rowSyntax top descriptor) [.reference name] state facts
        (input_reference state name available)
      have middleFacts : Facts middle := by simpa only [head, Outcome.state] using checked.facts
      have later : Available middle (.reference name) := by
        simpa only [head, Outcome.state] using checked.available _ available
      obtain ⟨values, final, tail, shapes⟩ := ih middle middleFacts later
      exact ⟨value :: values, final, by simp only [List.map_cons, buildMany, head, Outcome.bind, tail],
        .cons shape shapes⟩

private theorem arrow_build (top : Guard) (name : Reference) (state : State String Guard)
    (facts : Facts state) (available : Available state (.reference name)) :
    ∃ marker value final,
      build (arrowType top (.var 0) (.var 0)) [.reference name] state = .done value final ∧
      RowReadback "(->)" top [] marker ∧ RowReadback "->" top [marker, .reference name, .reference name] value := by
  obtain ⟨marker, middle, markerDone, markerShape⟩ := row_build top ("(->)", 0) name state facts available
  have markerBuilt : build (arrowMarker top) [.reference name] state = .done marker middle := by
    simpa only [rowSyntax, List.replicate_zero, arrowMarker] using markerDone
  have childrenDone : buildMany [arrowMarker top, .var 0, .var 0] [.reference name] state =
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
  exact ⟨marker, value, final, done, markerReadback, shape⟩

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

private theorem first_two {A B : Type} {R : A → B → Prop} {first second : A} {rest : List A}
    {outputs : List B} (aligned : All₂ R (first :: second :: rest) outputs) :
    ∃ a b later, outputs = a :: b :: later ∧ R first a ∧ R second b := by
  cases aligned with
  | cons head tail =>
      cases tail with
      | cons next rest => exact ⟨_, _, _, rfl, head, next⟩

omit [DecidableEq (EdgeKey String Guard)] in
private theorem row_different (top : Guard) (first second : String) (different : first ≠ second)
    (leftChildren rightChildren : List (Value String Guard)) (left right : Value String Guard)
    (state : State String Guard) (coherent : Coherent state)
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
  exact different (congrArg EdgeKey.symbol keys)

/-- Readback of catalog rows retains source order before final edge normalization. -/
def RowKeys (top : Guard) (name : Reference) (descriptor : String × Nat) (edge : EdgeValue String Guard) : Prop :=
  edge.children = List.replicate descriptor.2 (.reference name) ∧
    edge.entry.key = ⟨descriptor.1, List.replicate descriptor.2 (.ref name), top⟩

omit [DecidableEq (EdgeKey String Guard)] in
private theorem row_keys (top : Guard) (name : Reference) (rows : List (String × Nat))
    (values : List (Value String Guard))
    (aligned : All₂ (fun descriptor value =>
      RowReadback descriptor.1 top (List.replicate descriptor.2 (.reference name)) value) rows values) :
    All₂ (RowKeys top name) rows (values.flatMap nodeEdges) := by
  induction aligned with
  | nil => exact .nil
  | @cons descriptor value rest values own tail ih =>
      obtain ⟨entry, edge, same, children, key⟩ := own
      simp only [List.flatMap_cons, same, nodeEdges, List.singleton_append]
      exact .cons ⟨children, by simpa [List.map_replicate, Value.referenceOf] using key⟩ ih

/-- The actual body has its distinguished arrow and literal catalog before canonical ordering. -/
def Shape (top : Guard) (catalog : List (String × Nat)) (name : Reference) (value : Value String Guard) : Prop :=
  ∃ entry marker arrow rest,
    value = .node entry (canonicalEdges (surviving (arrow :: rest))) 0 [name] ∧
    RowReadback "(->)" top [] marker ∧
    arrow.children = [marker, .reference name, .reference name] ∧
    arrow.entry.key = ⟨"->", [marker.referenceOf, .ref name, .ref name], top⟩ ∧
    All₂ (RowKeys top name) (descriptors catalog) rest

private def Good (name : Reference) (value : Value String Guard) : Prop :=
  value.depth = 0 ∧ ∀ other ∈ value.free, other = name

omit [DecidableEq (EdgeKey String Guard)] in
private theorem good_reference (name : Reference) : Good (Guard := Guard) name (.reference name) := by
  simp [Good, Value.depth, Value.free]

omit [DecidableEq (EdgeKey String Guard)] in
private theorem row_children (name : Reference) (label : String) (top : Guard)
    (children : List (Value String Guard)) (value : Value String Guard)
    (shape : RowReadback label top children value) (good : ∀ child ∈ children, Good name child) :
    ∀ edge ∈ nodeEdges value, ∀ child ∈ edge.children, Good name child := by
  obtain ⟨entry, source, rfl, childrenEq, _⟩ := shape
  intro edge included child member
  have same := List.mem_singleton.mp included
  subst edge
  rw [childrenEq] at member
  exact good child member

private theorem body_inputs (top : Guard) (catalog : List (String × Nat)) (name : Reference)
    (state : State String Guard) (facts : Facts state) (available : Available state (.reference name)) :
    ∃ marker arrow values middle,
      buildMany (arrowType top (.var 0) (.var 0) :: (descriptors catalog).map (rowSyntax top))
        [.reference name] state = .done (arrow :: values) middle ∧
      RowReadback "(->)" top [] marker ∧ RowReadback "->" top [marker, .reference name, .reference name] arrow ∧
      All₂ (fun descriptor value =>
        RowReadback descriptor.1 top (List.replicate descriptor.2 (.reference name)) value)
        (descriptors catalog) values := by
  obtain ⟨marker, arrow, afterArrow, arrowDone, markerShape, arrowShape⟩ :=
    arrow_build top name state facts available
  have checked := build_verified (arrowType top (.var 0) (.var 0)) [.reference name] state facts
    (input_reference state name available)
  have arrowFacts : Facts afterArrow := by simpa only [arrowDone, Outcome.state] using checked.facts
  have later : Available afterArrow (.reference name) := by
    simpa only [arrowDone, Outcome.state] using checked.available _ available
  obtain ⟨values, middle, rowsDone, shapes⟩ := rows_build top (descriptors catalog) name afterArrow arrowFacts later
  exact ⟨marker, arrow, values, middle, by simp only [buildMany, arrowDone, Outcome.bind, rowsDone],
    markerShape, arrowShape, shapes⟩

/-- The actual normalized callback derives its complete ordinary rows without a completion premise. -/
theorem callback_readback (top : Guard) (catalog : List (String × Nat)) (name : Reference)
    (state : State String Guard) (facts : Facts state) (available : Available state (.reference name)) :
    ∃ value final, callback (allTypesBody top catalog) [] name state = .done value final ∧
      Shape top catalog name value ∧ Facts final ∧ Available final value := by
  obtain ⟨marker, arrow, values, middle, partsDone, markerShape, arrowShape, aligned⟩ :=
    body_inputs top catalog name state facts available
  have checked := buildMany_verified
    (arrowType top (.var 0) (.var 0) :: (descriptors catalog).map (rowSyntax top))
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
  have bodyDone : build (allTypesBody top catalog) [.reference name] state = .done result.1 result.2 := by
    simp only [body_syntax, build, partsDone, Outcome.bind, work]
    rfl
  have done : callback (allTypesBody top catalog) [] name state = .done result.1 result.2 := by
    simp only [callback, bodyDone, Outcome.bind, work, resultEq, withoutSelfReference, run]
  have finalChecked := callback_verified (allTypesBody top catalog) [] name state facts
    (input_reference state name available)
  refine ⟨result.1, result.2, done, ?_, ?_, finalChecked.result _ _ done⟩
  · refine ⟨entry, marker, arrowEdge, values.flatMap nodeEdges, ?_, markerReadback, arrowChildren, ?_, ?_⟩
    · simpa only [List.flatMap_cons, arrowEq, nodeEdges, List.singleton_append] using resultEq
    · simpa only [List.map_cons, List.map_nil, Value.referenceOf] using arrowKey
    · exact row_keys top name (descriptors catalog) values aligned
  · simpa only [done, Outcome.state] using finalChecked.facts

/-- The same callback has an ordinary constructor tag, zero depth, and exactly its local free name. -/
theorem callback_node (top : Guard) (catalog : List (String × Nat)) (name : Reference)
    (state : State String Guard) (facts : Facts state) (available : Available state (.reference name)) :
    ∃ entry edges final,
      callback (allTypesBody top catalog) [] name state = .done (.node entry edges 0 [name]) final := by
  obtain ⟨value, final, done, shape, _, _⟩ := callback_readback top catalog name state facts available
  obtain ⟨entry, marker, arrow, rest, same, _, _, _, _⟩ := shape
  exact ⟨entry, _, final, same ▸ done⟩

end MicroCFTA.SourceSynthesisUniverseBody
