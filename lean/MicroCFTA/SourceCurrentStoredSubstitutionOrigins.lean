import MicroCFTA.SourceCurrentStoredSubstitutionCalls
import MicroCFTA.MergedFreshOrdinaryUnionOrigins
import MicroCFTA.InternedFreshOrdinaryUnfoldCompletion
import MicroCFTA.SourceCurrentNativeMuPublication
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

/-!
# Source row occurrences through actual stored substitution

Ordinary reconstruction retains exact source fields and ordered stored
child calls. Union reconstruction retains each member call and its complete
epsilon row origins. Children may contain arbitrary nested Mu records.
The results do not identify changed child records with their source values.
-/
namespace MicroCFTA.SourceCurrentStoredSubstitutionOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome work)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment Replacements leaves manyLeaves edgeLeaves input encode encodeMany encodeEdges)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredMuOrigins (Normal)
open SourceCurrentSubstitutionRowExecution (ChildTrace)
open SourceCurrentStoredSubstitutionCalls (Calls)
open MergedFreshOrdinaryGraph (Origin)
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

private theorem closed [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (noFree : value.free = []) :
    execute value environment before = .done value before := by
  unfold execute
  have captured : leaves value = [value] := by
    rw [leaves.eq_def]
    simp only [noFree, List.isEmpty_nil, ite_true]
  rw [captured]
  have encoded : encode [value] [] value = .var 0 := by
    rw [encode.eq_def]
    simp [noFree, InternedStoredSubstitution.slot]
  rw [encoded]
  simpa only [List.map_cons, List.map_nil, build, List.getElem?_cons_zero, Option.getD_some] using
    congrArg (fun result => (Outcome.done result before : Outcome Symbol Guard (Value Symbol Guard)))
      (InternedStoredSubstitutionScope.input_closed value environment noFree)

private theorem row_leaves (rows : List (EdgeValue Symbol Guard)) (row : EdgeValue Symbol Guard)
    (member : row ∈ rows) (leaf : Value Symbol Guard) (present : leaf ∈ manyLeaves row.children) :
    leaf ∈ edgeLeaves rows := by
  induction rows with
  | nil => cases member
  | cons first rest ih =>
      cases first with
      | mk entry children =>
          rcases List.mem_cons.mp member with rfl | member
          · simpa only [edgeLeaves, EdgeValue.children] using List.mem_append_left (edgeLeaves rest) present
          · simpa only [edgeLeaves] using List.mem_append_right (manyLeaves children) (ih member)

/-- Each normalized ordinary row retains its source index, exact fields, and actual child call interval. -/
def NodeRows [DecidableEq (EdgeKey Symbol Guard)] (context : List (Value Symbol Guard))
    (environment : Environment Symbol Guard) (originals : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  ∀ (index : Nat) (output : EdgeValue Symbol Guard), (nodeEdges result)[index]? = some output →
    ∃ (sourceIndex : Nat), ∃ original rows middle current childAfter next,
      originals[sourceIndex]? = some original ∧ rows[sourceIndex]? = some output ∧
      buildEdges (encodeEdges context [] originals) (context.map (input environment)) before = .done rows middle ∧
      run (makeNode rows) middle = (result, after) ∧
      buildEdges (encodeEdges context [] (originals.take sourceIndex)) (context.map (input environment)) before =
        .done (rows.take sourceIndex) current ∧
      Calls environment original.children current output.children childAfter ∧
      run (makeEdge original.entry.key.symbol original.entry.key.constraint output.children) childAfter = (output, next) ∧
      buildEdges (encodeEdges context [] (originals.drop (sourceIndex + 1))) (context.map (input environment)) next =
        .done (rows.drop (sourceIndex + 1)) middle ∧
      output.entry.key.symbol = original.entry.key.symbol ∧
      output.entry.key.constraint = original.entry.key.constraint ∧
      output.children.length = original.children.length

/-- Union rows retain the ordered literal member substitutions and exact member origin occurrences. -/
def UnionRows [DecidableEq (EdgeKey Symbol Guard)] (environment : Environment Symbol Guard)
    (originals : List (Value Symbol Guard)) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  ∃ values middle, Calls environment originals before values middle ∧
    run (makeUnion values) middle = (result, after) ∧
    ∀ view row, Origin view [result] row ↔
      ∃ (index : Nat), ∃ original output, originals[index]? = some original ∧ values[index]? = some output ∧
        Origin view [output] row

/-- Actual open ordinary substitution retains indexed source rows and each child's own stored execution. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (originals : List (EdgeValue Symbol Guard)) (level : Nat) (free : List Reference)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (normal : Normal before)
    (available : Available before (.node entry originals level free)) (replacements : Replacements before environment)
    (opened : free.isEmpty = false) (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute (.node entry originals level free) environment before = .done result after) :
    NodeRows (leaves (.node entry originals level free)) environment originals before result after := by
  let context := leaves (.node entry originals level free)
  have inputs := InternedStoredSubstitution.inputs_available _ environment before available replacements
  have compiled : encode context [] (.node entry originals level free) = .node (encodeEdges context [] originals) := by
    rw [encode.eq_def]
    simp only [Value.free, opened, Bool.false_eq_true, ite_false]
  change build (encode context [] (.node entry originals level free)) (context.map (input environment)) before =
    .done result after at actual
  rw [compiled] at actual
  intro index output selected
  obtain ⟨sourceIndex, original, rows, middle, current, childAfter, next, values,
    found, rebuilt, rowsDone, madeNode, earlier, trace, madeEdge, later, symbol, guard, children, arity⟩ :=
    SourceCurrentSubstitutionRowExecution.node_indexed context [] (context.map (input environment)) originals
      before result after normal.facts inputs actual index output selected
  have childAvailable : Values before original.children := by
    intro child member
    exact available.children child (List.mem_flatMap.mpr ⟨original, List.mem_of_getElem? found, member⟩)
  have covered : ∀ leaf ∈ manyLeaves original.children, leaf ∈ context := by
    intro leaf member
    have included := row_leaves originals original (List.mem_of_getElem? found) leaf member
    simpa only [context, leaves.eq_def, Value.free, opened, Bool.false_eq_true, ite_false] using included
  have calls := SourceCurrentStoredSubstitutionCalls.from_encoded context environment before normal.facts.coherent
    (InternedStoredSubstitution.leaves_available _ before available) trace childAvailable covered
  rw [← children] at calls madeEdge
  exact ⟨sourceIndex, original, rows, middle, current, childAfter, next, found, rebuilt,
    rowsDone, madeNode, earlier, calls, madeEdge, later, symbol, guard, arity⟩

/-- Actual open union substitution retains complete row origins of its indexed original member calls. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (originals : List (Value Symbol Guard)) (level : Nat) (free : List Reference)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (normal : Normal before)
    (available : Available before (.union entry originals level free)) (replacements : Replacements before environment)
    (opened : free.isEmpty = false) (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute (.union entry originals level free) environment before = .done result after) :
    UnionRows environment originals before result after := by
  let context := leaves (.union entry originals level free)
  let inputs := context.map (input environment)
  have inputsAvailable : Values before inputs :=
    InternedStoredSubstitution.inputs_available _ environment before available replacements
  have compiled : encode context [] (.union entry originals level free) = .union (encodeMany context [] originals) := by
    rw [encode.eq_def]
    simp only [Value.free, opened, Bool.false_eq_true, ite_false]
  change build (encode context [] (.union entry originals level free)) inputs before = .done result after at actual
  rw [compiled, build] at actual
  cases membersDone : buildMany (encodeMany context [] originals) inputs before with
  | pending key stopped => simp only [membersDone, Outcome.bind] at actual; cases actual
  | done values middle =>
      simp only [membersDone, Outcome.bind, work, Outcome.done.injEq] at actual
      have made : run (makeUnion values) middle = (result, after) := Prod.ext actual.1 actual.2
      have middleNormal : Normal middle := by
        simpa only [membersDone, Outcome.state] using InternedFreshOrdinaryNormal.buildMany_normal
          (encodeMany context [] originals) inputs before normal inputsAvailable
      have outputsAvailable := (InternedFreshOrdinaryFacts.buildMany_verified
        (encodeMany context [] originals) inputs before normal.facts inputsAvailable).result values middle membersDone
      have trace := ChildTrace.children context [] inputs originals before values middle membersDone
      have calls := SourceCurrentStoredSubstitutionCalls.from_encoded context environment before normal.facts.coherent
        (InternedStoredSubstitution.leaves_available _ before available) trace
        (fun value member => available.children value member) (by
          intro leaf member
          simpa only [context, leaves.eq_def, Value.free, opened, Bool.false_eq_true, ite_false] using member)
      refine ⟨values, middle, calls, made, ?_⟩
      intro view row
      have origins := MergedFreshOrdinaryUnionOrigins.union_origins middle view middleNormal.facts middleNormal.live
        values outputsAvailable row
      rw [made] at origins
      rw [origins]
      constructor
      · rintro ⟨output, member, origin⟩
        obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
        obtain ⟨original, _, _, found, _, _, _⟩ := calls.indexed index output selected
        exact ⟨index, original, output, found, selected, origin⟩
      · rintro ⟨index, original, output, _, selected, origin⟩
        exact ⟨output, List.mem_of_getElem? selected, origin⟩

private theorem history [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (semantic : SemanticHeap before)
    (available : Available before value) (replacements : Replacements before environment)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute value environment before = .done result after) :
    Nonempty (SourceCurrentNativeMuPublication.History before after) := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before semantic
    ((leaves value).map (input environment))
    (InternedStoredSubstitution.inputs_available value environment before available replacements)
  have emitted := SourceCurrentNativeMuPublication.build_history
    (encode (leaves value) [] value) ((leaves value).map (input environment)) before ⟨context, semantic.2⟩
  change Nonempty (SourceCurrentNativeMuPublication.History before (execute value environment before).state) at emitted
  simpa only [actual, Outcome.state] using emitted

/-- Initial complete semantic inputs construct the ordinary return, its source rows, and its causal history. -/
theorem node_complete [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (originals : List (EdgeValue Symbol Guard)) (level : Nat) (free : List Reference)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (semantic : SemanticHeap before)
    (covered : Covered [] before) (available : Available before (.node entry originals level free))
    (replacements : Replacements before environment) :
    ∃ result after, execute (.node entry originals level free) environment before = .done result after ∧
      SemanticHeap after ∧ Covered [] after ∧ Available after result ∧
      Nonempty (SourceCurrentNativeMuPublication.History before after) ∧
      ((free = [] ∧ result = .node entry originals level free ∧ after = before) ∨
        (free.isEmpty = false ∧ NodeRows (leaves (.node entry originals level free)) environment originals before result after)) := by
  obtain ⟨result, after, actual, context, depth, retained, output, _, _⟩ :=
    InternedFreshOrdinaryStoredSubstitution.execute_complete_decoded _ environment before semantic.1
      available replacements semantic.2 covered
  refine ⟨result, after, actual, ⟨context, depth⟩, retained, output,
    history _ environment before semantic available replacements result after actual, ?_⟩
  by_cases noFree : free = []
  · left
    rw [closed (.node entry originals level free) environment before noFree] at actual
    exact ⟨noFree, (Outcome.done.inj actual).1.symm, (Outcome.done.inj actual).2.symm⟩
  · have opened : free.isEmpty = false := by simpa only [List.isEmpty_eq_false_iff] using noFree
    exact Or.inr ⟨opened, node entry originals level free environment before semantic.1.normal available
      replacements opened result after actual⟩

/-- Initial complete semantic inputs construct the union return and indexed member origins without future completion. -/
theorem union_complete [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (originals : List (Value Symbol Guard)) (level : Nat) (free : List Reference)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (semantic : SemanticHeap before)
    (covered : Covered [] before) (available : Available before (.union entry originals level free))
    (replacements : Replacements before environment) :
    ∃ result after, execute (.union entry originals level free) environment before = .done result after ∧
      SemanticHeap after ∧ Covered [] after ∧ Available after result ∧
      Nonempty (SourceCurrentNativeMuPublication.History before after) ∧
      ((free = [] ∧ result = .union entry originals level free ∧ after = before) ∨
        (free.isEmpty = false ∧ UnionRows environment originals before result after)) := by
  obtain ⟨result, after, actual, context, depth, retained, output, _, _⟩ :=
    InternedFreshOrdinaryStoredSubstitution.execute_complete_decoded _ environment before semantic.1
      available replacements semantic.2 covered
  refine ⟨result, after, actual, ⟨context, depth⟩, retained, output,
    history _ environment before semantic available replacements result after actual, ?_⟩
  by_cases noFree : free = []
  · left
    rw [closed (.union entry originals level free) environment before noFree] at actual
    exact ⟨noFree, (Outcome.done.inj actual).1.symm, (Outcome.done.inj actual).2.symm⟩
  · have opened : free.isEmpty = false := by simpa only [List.isEmpty_eq_false_iff] using noFree
    exact Or.inr ⟨opened, union entry originals level free environment before semantic.1.normal available
      replacements opened result after actual⟩

end MicroCFTA.SourceCurrentStoredSubstitutionOrigins
