import MicroCFTA.SourceCurrentStoredSubstitutionOrigins
import MicroCFTA.SourceCurrentRowPlanReplay
import MicroCFTA.SourceCurrentOpenObservationConstructors
import MicroCFTA.InternedNormalizationFree

/-!
# Complete row expansion of warm stored ordinary nodes

Every original row retains its ordered stored child calls and full guard.
Closed nodes retain their literal rows. Their parent key need not be the
canonical key of a new node request. Open nodes expose all rebuilt rows
before dead-row filtering. No child completion is a separate premise.
-/
namespace MicroCFTA.SourceCurrentStoredNodeExpansion
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome work)
open InternedNestedProvenance (Values Edges)
open InternedNestedFacts (Facts)
open InternedStoredSubstitution (Environment Replacements leaves manyLeaves edgeLeaves input encode encodeMany encodeEdges)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredMuOrigins (Normal)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentSubstitutionRowExecution (ChildTrace)
open SourceCurrentRowPlanReplay (rowRun)
open SourceEqualityRequiredCache (Ordinary)
open MergedFreshOrdinaryGraph (Origin)
open InternedBinderProtocol (NodeKey Reference)
open Language

/-- A row retains its exact warm child calls, edge request, and complete source fields. -/
def RowCalls [DecidableEq (EdgeKey Symbol Guard)] (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (original output : EdgeValue Symbol Guard) : Prop :=
  Calls environment original.children common output.children common ∧
    run (makeEdge original.entry.key.symbol original.entry.key.constraint output.children) common = (output, common) ∧
    output.entry.key.symbol = original.entry.key.symbol ∧
    output.entry.key.constraint = original.entry.key.constraint ∧
    output.children.length = original.children.length

/-- Every original row has a warm execution, and exactly its surviving outputs are exposed. -/
def Expansion [DecidableEq (EdgeKey Symbol Guard)] (environment : Environment Symbol Guard)
    (originals : List (EdgeValue Symbol Guard)) (common : State Symbol Guard)
    (result : Value Symbol Guard) : Prop :=
  ∃ outputs, All₂ (RowCalls environment common) originals outputs ∧ Ordinary result ∧
    ∀ view row, Origin view [result] row ↔ row ∈ surviving outputs

private theorem closed (value : Value Symbol Guard) (environment : Environment Symbol Guard)
    (state : State Symbol Guard) (noFree : value.free = []) [DecidableEq (EdgeKey Symbol Guard)] :
    execute value environment state = .done value state := by
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
    congrArg (fun result => (Outcome.done result state : Outcome Symbol Guard (Value Symbol Guard)))
      (InternedStoredSubstitutionScope.input_closed value environment noFree)

private theorem closed_calls [DecidableEq (EdgeKey Symbol Guard)]
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (values : List (Value Symbol Guard))
    (noFree : ∀ value ∈ values, value.free = []) : Calls environment values state values state := by
  induction values with
  | nil => exact .nil state
  | cons value values ih =>
      exact .cons value values state state state value values
        (closed value environment state (noFree value List.mem_cons_self))
        (ih (fun value member => noFree value (List.mem_cons_of_mem _ member)))

private theorem edge_warm [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (coherent : Coherent state) (edge : EdgeValue Symbol Guard) (resident : EdgeResident state edge) :
    run (makeEdge edge.entry.key.symbol edge.entry.key.constraint edge.children) state = (edge, state) := by
  have fields := coherent.edges edge.entry.key edge resident
  have key : EdgeKey.mk edge.entry.key.symbol (edge.children.map Value.referenceOf) edge.entry.key.constraint =
      edge.entry.key := by
    cases same : edge.entry.key
    simpa only [same] using congrArg (fun children => EdgeKey.mk _ children _) fields.2.2
  change state.edgeRecords edge.entry.key = some edge at resident
  simp only [makeEdge, run, key, edgeStep, Cache.intern, fields.1, keepFirst, resident, Option.getD_some]

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

private theorem warm_row [DecidableEq (EdgeKey Symbol Guard)]
    (context : List (Value Symbol Guard)) (environment : Environment Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (contextAvailable : Values state context)
    (replacements : Replacements state environment)
    (original output : EdgeValue Symbol Guard) (available : Values state original.children)
    (covered : ∀ leaf ∈ manyLeaves original.children, leaf ∈ context)
    (actual : rowRun (.mk original.entry.key.symbol original.entry.key.constraint
      (encodeMany context [] original.children)) (context.map (input environment)) state = .done output state) :
    RowCalls environment state original output := by
  let plans := encodeMany context [] original.children
  let inputs := context.map (input environment)
  have inputsAvailable : Values state inputs := by
    intro value member
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp member
    have source := contextAvailable original member
    cases original with
    | empty | node | union | mu => exact source
    | reference name =>
        cases found : environment name with
        | none => simpa only [input, found, Option.getD_none] using source
        | some replacement =>
            simpa only [input, found, Option.getD_some] using replacements name replacement found
  change (buildMany plans inputs state).bind
    (fun values middle => work (makeEdge original.entry.key.symbol original.entry.key.constraint values) middle) =
      .done output state at actual
  cases childrenDone : buildMany plans inputs state with
  | pending key middle => simp only [childrenDone, Outcome.bind] at actual; cases actual
  | done values middle =>
      simp only [childrenDone, Outcome.bind, work, Outcome.done.injEq] at actual
      have made : run (makeEdge original.entry.key.symbol original.entry.key.constraint values) middle = (output, state) :=
        Prod.ext actual.1 actual.2
      have checked := InternedFreshOrdinaryFacts.buildMany_verified plans inputs state facts inputsAvailable
      have middleFacts : Facts middle := by simpa only [childrenDone, Outcome.state] using checked.facts
      have middleAvailable := checked.result values middle childrenDone
      have growth : Grows middle state := by
        simpa only [made] using
          (run_correct (makeEdge original.entry.key.symbol original.entry.key.constraint values) middle
            middleFacts.coherent.valid).2
      have repeated := InternedFreshOrdinaryReplay.buildMany_replays plans inputs state state values middle
        facts.coherent.valid childrenDone growth
      have trace := ChildTrace.children context [] inputs original.children state values state repeated
      have calls := SourceCurrentStoredSubstitutionCalls.from_encoded context environment state facts.coherent
        contextAvailable trace available covered
      have fields := MergedPhysicalGroupEdges.makeEdge_fields middle middleFacts
        original.entry.key.symbol original.entry.key.constraint values middleAvailable
      rw [made] at fields
      have replayed := InternedConstructorTemplates.replay
        (makeEdge original.entry.key.symbol original.entry.key.constraint values) middle state
        middleFacts.coherent.valid (by rw [made]; exact grows_refl _)
      rw [made] at replayed
      rw [← fields.2.2] at calls replayed
      exact ⟨calls, replayed, fields.1, fields.2.1, calls.length⟩

private theorem makeNode_origins [DecidableEq (EdgeKey Symbol Guard)]
    (state view : State Symbol Guard) (facts : Facts state)
    (rows : List (EdgeValue Symbol Guard)) (resident : Edges state rows) (row : EdgeValue Symbol Guard) :
    Origin view [(run (makeNode rows) state).1] row ↔ row ∈ surviving rows := by
  have ordinary := SourceEqualityRequiredCache.node_ordinary rows state facts resident
  have terminal : MergedFreshOrdinaryGraph.successors view (run (makeNode rows) state).1 = [] := by
    generalize selected : (run (makeNode rows) state).1 = value at ordinary ⊢
    cases value <;> simp_all [SourceEqualityRequiredCache.Ordinary, MergedFreshOrdinaryGraph.successors]
  have exactRows : Origin view [(run (makeNode rows) state).1] row ↔ row ∈ nodeEdges (run (makeNode rows) state).1 :=
    ⟨MergedFreshOrdinaryExposureCoverage.origin_terminal view _ terminal row,
      fun member => ⟨_, .seed List.mem_cons_self, member⟩⟩
  rw [exactRows, EqualityLeafProjectionPhysical.makeNode_edges rows state facts.coherent facts.linked resident]
  exact ⟨canonicalEdges_member _ row,
    InternedEdgeResidency.canonicalEdges_retains state facts.coherent _ row
      (fun edge member => resident edge (List.mem_filter.mp member).1)⟩

/-- Actual warm node execution exposes every original row, including closed opaque nodes. -/
theorem node_warm [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (originals : List (EdgeValue Symbol Guard)) (level : Nat) (free : List Reference)
    (environment : Environment Symbol Guard) (common : State Symbol Guard) (normal : Normal common)
    (available : Available common (.node entry originals level free))
    (replacements : Replacements common environment) (result : Value Symbol Guard)
    (actual : execute (.node entry originals level free) environment common = .done result common) :
    Expansion environment originals common result := by
  by_cases noFree : free = []
  · have same := (Outcome.done.inj
      ((closed (.node entry originals level free) environment common noFree).symm.trans actual)).1
    subst result
    have freeFields := InternedNormalizationFree.node_free common normal.facts.coherent
      entry originals level free available.resident
    have childrenClosed : ∀ row ∈ originals, ∀ child ∈ row.children, child.free = [] := by
      intro row member child included
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro name present
      have named := (childFree_member (originals.flatMap EdgeValue.children) name).mpr
        ⟨child, List.mem_flatMap.mpr ⟨row, member, included⟩, present⟩
      rw [← freeFields, noFree] at named
      cases named
    have resident := resident_edges common normal.facts.linked _ available.resident
    have live := InternedLiveEdges.resident_live common normal.live _ available.resident
    have surviving : surviving originals = originals := by
      apply List.filter_eq_self.mpr
      intro row member
      simp only [live row member, Bool.not_false]
    refine ⟨originals, ?_, trivial, ?_⟩
    · have buildRows : ∀ rows, (∀ row ∈ rows, row ∈ originals) →
          All₂ (RowCalls environment common) rows rows := by
        intro rows subset
        induction rows with
        | nil => exact .nil
        | cons row rows ih =>
            refine .cons ⟨closed_calls environment common row.children
                (childrenClosed row (subset row List.mem_cons_self)),
              edge_warm common normal.facts.coherent row (resident row (subset row List.mem_cons_self)),
              rfl, rfl, rfl⟩ ?_
            exact ih (fun row member => subset row (List.mem_cons_of_mem _ member))
      exact buildRows originals (fun _ member => member)
    · intro view row
      rw [surviving]
      exact MergedFreshOrdinaryGraph.origin_node view entry originals level free row
  · have opened : free.isEmpty = false := by simpa only [List.isEmpty_eq_false_iff] using noFree
    let context := leaves (.node entry originals level free)
    let inputs := context.map (input environment)
    have contextAvailable := InternedStoredSubstitution.leaves_available _ common available
    have inputsAvailable := InternedStoredSubstitution.inputs_available _ environment common available replacements
    have compiled : encode context [] (.node entry originals level free) = .node (encodeEdges context [] originals) := by
      rw [encode.eq_def]
      simp only [Value.free, opened, Bool.false_eq_true, ite_false]
    change build (encode context [] (.node entry originals level free)) inputs common = .done result common at actual
    rw [compiled, build] at actual
    cases rowsDone : buildEdges (encodeEdges context [] originals) inputs common with
    | pending key stopped => simp only [rowsDone, Outcome.bind] at actual; cases actual
    | done rows middle =>
        simp only [rowsDone, Outcome.bind, work, Outcome.done.injEq] at actual
        have made : run (makeNode rows) middle = (result, common) := Prod.ext actual.1 actual.2
        have checked := InternedFreshOrdinaryFacts.buildEdges_verified
          (encodeEdges context [] originals) inputs common normal.facts inputsAvailable
        have middleFacts : Facts middle := by simpa only [rowsDone, Outcome.state] using checked.facts
        have resident := checked.result rows middle rowsDone
        have growth : Grows middle common := by
          simpa only [made] using (run_correct (makeNode rows) middle middleFacts.coherent.valid).2
        have replayed := SourceCurrentRowPlanReplay.rows (encodeEdges context [] originals) inputs common rows middle common
          normal.facts.coherent.valid rowsDone growth
        have convert : ∀ source outputs, (∀ row ∈ source, row ∈ originals) →
            All₂ (fun plan output => rowRun plan inputs common = .done output common)
              (encodeEdges context [] source) outputs →
            All₂ (RowCalls environment common) source outputs := by
          intro source
          induction source with
          | nil =>
              intro outputs _ paired
              simp only [encodeEdges] at paired
              cases paired
              exact .nil
          | cons row source ih =>
              intro outputs subset paired
              cases row with
              | mk edge children =>
                  simp only [encodeEdges] at paired
                  cases paired with
                  | cons called rest =>
                      refine .cons (warm_row context environment common normal.facts contextAvailable replacements
                        (.mk edge children) _ ?_ ?_ called) (ih _ ?_ rest)
                      · intro child member
                        exact available.children child
                          (List.mem_flatMap.mpr ⟨.mk edge children, subset _ List.mem_cons_self, member⟩)
                      · intro leaf member
                        have included := row_leaves originals (.mk edge children) (subset _ List.mem_cons_self) leaf member
                        simpa only [context, leaves.eq_def, Value.free, opened, Bool.false_eq_true, ite_false] using included
                      · exact fun row member => subset row (List.mem_cons_of_mem _ member)
        refine ⟨rows, convert originals rows (fun _ member => member) replayed, ?_, ?_⟩
        · have ordinary := SourceEqualityRequiredCache.node_ordinary rows middle middleFacts resident
          simpa only [made] using ordinary
        · intro view row
          have origins := makeNode_origins middle view middleFacts rows resident row
          simpa only [made] using origins

end MicroCFTA.SourceCurrentStoredNodeExpansion
