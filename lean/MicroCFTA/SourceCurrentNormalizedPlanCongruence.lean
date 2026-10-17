import MicroCFTA.SourceCurrentNormalizedPlanRelation
import MicroCFTA.SourceCurrentWarmConstructionParts
import MicroCFTA.SourceCurrentNativeRequestWinner
import MicroCFTA.SourceCurrentNodePlanCongruence

/-!
# Exact results for recursively normalized plans

Completed plans replay at a common heap. Related nested node rows then
select the same canonical values. Binder probes select the same stored
winner. Initial readiness constructs both executions in sequence.
-/
namespace MicroCFTA.SourceCurrentNormalizedPlanCongruence
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedFacts InternedNestedProvenance InternedNestedSpecialization
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryGrowth InternedFreshOrdinaryFacts InternedFreshOrdinaryReplay
open SourceCurrentNormalizedPlanRelation
open SourceCurrentRowPlanReplay (rowRun)
open SourceEqualityRequiredCache (Ready Keeps)
open Language

private theorem left_member {A B : Type} {relation : A → B → Prop} {first : List A} {second : List B}
    (paired : All₂ relation first second) (value : A) (member : value ∈ first) :
    ∃ other ∈ second, relation value other := by
  induction paired with
  | nil => cases member
  | cons pair _ ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, pair⟩
      · obtain ⟨other, present, related⟩ := ih later
        exact ⟨other, List.mem_cons_of_mem _ present, related⟩

private theorem right_member {A B : Type} {relation : A → B → Prop} {first : List A} {second : List B}
    (paired : All₂ relation first second) (value : B) (member : value ∈ second) :
    ∃ other ∈ first, relation other value := by
  induction paired with
  | nil => cases member
  | cons pair _ ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, pair⟩
      · obtain ⟨other, present, related⟩ := ih later
        exact ⟨other, List.mem_cons_of_mem _ present, related⟩

private theorem inputs_cons (state : State Symbol Guard) (value : Value Symbol Guard)
    (inputs : List (Value Symbol Guard)) (available : Available state value) (values : Values state inputs) :
    Values state (value :: inputs) := by
  intro selected present
  rcases List.mem_cons.mp present with rfl | member
  · exact available
  · exact values selected member

mutual
/-- Related recursive plans have the same exact value when both actual calls are warm at one heap. -/
theorem warm [DecidableEq (EdgeKey Symbol Guard)] (first : Syntax Symbol Guard)
    (firstInputs : List (Value Symbol Guard)) (second : Syntax Symbol Guard) (secondInputs : List (Value Symbol Guard))
    (common : State Symbol Guard) (left right : Value Symbol Guard) (facts : Facts common)
    (leftInputs : Values common firstInputs) (rightInputs : Values common secondInputs)
    (related : Related first firstInputs second secondInputs)
    (leftDone : build first firstInputs common = .done left common)
    (rightDone : build second secondInputs common = .done right common) : left = right := by
  cases first <;> cases second <;> simp only [Related] at related <;> try contradiction
  case empty.empty =>
    simp only [build, Outcome.done.injEq, and_true] at leftDone rightDone
    exact leftDone.symm.trans rightDone
  case var.var firstIndex secondIndex =>
    simp only [build, Outcome.done.injEq, and_true] at leftDone rightDone
    exact leftDone.symm.trans (related.trans rightDone)
  case node.node firstRows secondRows =>
    obtain ⟨leftRows, leftRowsDone, leftMade⟩ :=
      SourceCurrentWarmConstructionParts.node firstRows firstInputs common left facts.coherent.valid leftDone
    obtain ⟨rightRows, rightRowsDone, rightMade⟩ :=
      SourceCurrentWarmConstructionParts.node secondRows secondInputs common right facts.coherent.valid rightDone
    have same := warm_rows firstRows firstInputs secondRows secondInputs common leftRows rightRows facts leftInputs rightInputs related
      (SourceCurrentWarmConstructionParts.rows firstRows firstInputs common leftRows facts.coherent.valid leftRowsDone)
      (SourceCurrentWarmConstructionParts.rows secondRows secondInputs common rightRows facts.coherent.valid rightRowsDone)
    have leftResident := (InternedFreshOrdinaryFacts.buildEdges_verified firstRows firstInputs common facts leftInputs).result
      leftRows common leftRowsDone
    have rightResident := (InternedFreshOrdinaryFacts.buildEdges_verified secondRows secondInputs common facts rightInputs).result
      rightRows common rightRowsDone
    have requests := InternedNodeSetCongruence.makeNode_same_members common facts.coherent leftRows rightRows
      leftResident rightResident (by intro edge; simp only [surviving, List.mem_filter, same edge])
    rw [requests] at leftMade
    exact congrArg Prod.fst (leftMade.symm.trans rightMade)
  case union.union firstMembers secondMembers =>
    obtain ⟨leftValues, leftValuesDone, leftMade⟩ :=
      SourceCurrentWarmConstructionParts.union firstMembers firstInputs common left facts.coherent.valid leftDone
    obtain ⟨rightValues, rightValuesDone, rightMade⟩ :=
      SourceCurrentWarmConstructionParts.union secondMembers secondInputs common right facts.coherent.valid rightDone
    have same := warm_many firstMembers firstInputs secondMembers secondInputs common leftValues rightValues facts leftInputs rightInputs related
      (SourceCurrentWarmConstructionParts.many firstMembers firstInputs common leftValues facts.coherent.valid leftValuesDone)
      (SourceCurrentWarmConstructionParts.many secondMembers secondInputs common rightValues facts.coherent.valid rightValuesDone)
    rw [same] at leftMade
    exact congrArg Prod.fst (leftMade.symm.trans rightMade)
  case binder.binder firstSmart firstBody secondSmart secondBody =>
    obtain ⟨rfl, bodies⟩ := related
    obtain ⟨firstDepth, firstOrdinary, firstRawDepth, firstRawOrdinary, _, _, firstDepthDone, firstDepthFilter,
      firstOrdinaryDone, firstOrdinaryFilter, firstRequest⟩ :=
      SourceCurrentWarmConstructionParts.binder firstSmart firstBody firstInputs common left facts.coherent.valid leftDone
    obtain ⟨secondDepth, secondOrdinary, secondRawDepth, secondRawOrdinary, _, _, secondDepthDone, secondDepthFilter,
      secondOrdinaryDone, secondOrdinaryFilter, secondRequest⟩ :=
      SourceCurrentWarmConstructionParts.binder firstSmart secondBody secondInputs common right facts.coherent.valid rightDone
    have rawDepthSame := warm firstBody (.reference .depth :: firstInputs) secondBody (.reference .depth :: secondInputs)
      common firstRawDepth secondRawDepth facts
      (inputs_cons common _ firstInputs (depth_available common) leftInputs)
      (inputs_cons common _ secondInputs (depth_available common) rightInputs) (bodies .depth) firstDepthDone secondDepthDone
    rw [rawDepthSame] at firstDepthFilter
    have depthSame := congrArg Prod.fst (firstDepthFilter.symm.trans secondDepthFilter)
    cases depthSame
    have rawOrdinarySame := warm firstBody (.reference (.uninterned (ordinaryLevel firstDepth)) :: firstInputs)
      secondBody (.reference (.uninterned (ordinaryLevel firstDepth)) :: secondInputs)
      common firstRawOrdinary secondRawOrdinary facts
      (inputs_cons common _ firstInputs (ordinary_available common _) leftInputs)
      (inputs_cons common _ secondInputs (ordinary_available common _) rightInputs)
      (bodies (.uninterned (ordinaryLevel firstDepth))) firstOrdinaryDone secondOrdinaryDone
    rw [rawOrdinarySame] at firstOrdinaryFilter
    have ordinarySame := congrArg Prod.fst (firstOrdinaryFilter.symm.trans secondOrdinaryFilter)
    cases ordinarySame
    obtain ⟨firstWinner, firstPresent, firstValue⟩ := SourceCurrentNativeRequestWinner.winner firstSmart firstDepth firstOrdinary
      (InternedFreshOrdinaryFacts.callback firstBody firstInputs) common left common firstRequest
    obtain ⟨secondWinner, secondPresent, secondValue⟩ := SourceCurrentNativeRequestWinner.winner firstSmart firstDepth firstOrdinary
      (InternedFreshOrdinaryFacts.callback secondBody secondInputs) common right common secondRequest
    have winnerSame := Option.some.inj (firstPresent.symm.trans secondPresent)
    exact firstValue.trans ((congrArg (InternedNestedConstruction.finish firstSmart) winnerSame).trans secondValue.symm)
termination_by sizeOf first

/-- Ordered related child calls give the same complete list of returned values. -/
theorem warm_many [DecidableEq (EdgeKey Symbol Guard)] (first : List (Syntax Symbol Guard))
    (firstInputs : List (Value Symbol Guard)) (second : List (Syntax Symbol Guard)) (secondInputs : List (Value Symbol Guard))
    (common : State Symbol Guard) (left right : List (Value Symbol Guard)) (facts : Facts common)
    (leftInputs : Values common firstInputs) (rightInputs : Values common secondInputs)
    (related : ManyRelated first firstInputs second secondInputs)
    (leftCalls : All₂ (fun expression output => build expression firstInputs common = .done output common) first left)
    (rightCalls : All₂ (fun expression output => build expression secondInputs common = .done output common) second right) :
    left = right := by
  cases first <;> cases second <;> simp only [ManyRelated] at related <;> try contradiction
  case nil.nil => cases leftCalls; cases rightCalls; rfl
  case cons.cons first rest second remaining =>
    cases leftCalls with
    | cons leftDone leftRest =>
      cases rightCalls with
      | cons rightDone rightRest =>
        have headSame := warm first firstInputs second secondInputs common _ _ facts leftInputs rightInputs related.1 leftDone rightDone
        have tailSame := warm_many rest firstInputs remaining secondInputs common _ _ facts leftInputs rightInputs related.2 leftRest rightRest
        exact congr (congrArg List.cons headSame) tailSame
termination_by sizeOf first

/-- Related row plans have identical complete edge values at a common warm heap. -/
theorem warm_row [DecidableEq (EdgeKey Symbol Guard)] (first : EdgeSyntax Symbol Guard)
    (firstInputs : List (Value Symbol Guard)) (second : EdgeSyntax Symbol Guard) (secondInputs : List (Value Symbol Guard))
    (common : State Symbol Guard) (left right : EdgeValue Symbol Guard) (facts : Facts common)
    (leftInputs : Values common firstInputs) (rightInputs : Values common secondInputs)
    (related : RowRelated first firstInputs second secondInputs)
    (leftDone : rowRun first firstInputs common = .done left common)
    (rightDone : rowRun second secondInputs common = .done right common) : left = right := by
  cases first with
  | mk symbol guard firstChildren =>
    cases second with
    | mk otherSymbol otherGuard secondChildren =>
      simp only [RowRelated] at related
      obtain ⟨rfl, rfl, children⟩ := related
      obtain ⟨leftValues, leftValuesDone, leftMade⟩ := SourceCurrentWarmConstructionParts.bind (buildMany firstChildren firstInputs)
        (fun values state => work (makeEdge symbol guard values) state) common left facts.coherent.valid
        (buildMany_correct firstChildren firstInputs) (fun values => InternedNestedConstruction.work_correct (makeEdge symbol guard values))
        (buildMany_replays firstChildren firstInputs) leftDone
      obtain ⟨rightValues, rightValuesDone, rightMade⟩ := SourceCurrentWarmConstructionParts.bind (buildMany secondChildren secondInputs)
        (fun values state => work (makeEdge symbol guard values) state) common right facts.coherent.valid
        (buildMany_correct secondChildren secondInputs) (fun values => InternedNestedConstruction.work_correct (makeEdge symbol guard values))
        (buildMany_replays secondChildren secondInputs) rightDone
      have same := warm_many firstChildren firstInputs secondChildren secondInputs common leftValues rightValues facts leftInputs rightInputs children
        (SourceCurrentWarmConstructionParts.many firstChildren firstInputs common leftValues facts.coherent.valid leftValuesDone)
        (SourceCurrentWarmConstructionParts.many secondChildren secondInputs common rightValues facts.coherent.valid rightValuesDone)
      rw [same] at leftMade
      exact (Outcome.done.inj (leftMade.symm.trans rightMade)).1
termination_by sizeOf first

/-- Bidirectional row occurrence matching gives identical complete physical row sets. -/
theorem warm_rows [DecidableEq (EdgeKey Symbol Guard)] (first : List (EdgeSyntax Symbol Guard))
    (firstInputs : List (Value Symbol Guard)) (second : List (EdgeSyntax Symbol Guard)) (secondInputs : List (Value Symbol Guard))
    (common : State Symbol Guard) (left right : List (EdgeValue Symbol Guard)) (facts : Facts common)
    (leftInputs : Values common firstInputs) (rightInputs : Values common secondInputs)
    (related : RowsRelated first firstInputs second secondInputs)
    (leftCalls : All₂ (fun expression output => rowRun expression firstInputs common = .done output common) first left)
    (rightCalls : All₂ (fun expression output => rowRun expression secondInputs common = .done output common) second right) :
    ∀ row, row ∈ left ↔ row ∈ right := by
  rw [RowsRelated] at related
  intro row
  constructor
  · intro member
    obtain ⟨original, present, called⟩ := right_member leftCalls row member
    obtain ⟨other, included, matching⟩ := related.1 original present
    obtain ⟨output, returned, actual⟩ := left_member rightCalls other included
    have same := warm_row original firstInputs other secondInputs common row output facts leftInputs rightInputs matching called actual
    simpa only [same] using returned
  · intro member
    obtain ⟨original, present, called⟩ := right_member rightCalls row member
    obtain ⟨other, included, matching⟩ := related.2 original present
    obtain ⟨output, returned, actual⟩ := left_member leftCalls other included
    have same := warm_row other firstInputs original secondInputs common output row facts leftInputs rightInputs matching actual called
    exact same ▸ returned
termination_by sizeOf first
decreasing_by all_goals exact List.sizeOf_lt_of_mem (by assumption)
end

/-- Related completed calls have identical values after both actual histories reach a common heap. -/
theorem completed [DecidableEq (EdgeKey Symbol Guard)]
    (first second : Syntax Symbol Guard) (firstInputs secondInputs : List (Value Symbol Guard))
    (before later after final common : State Symbol Guard) (left right : Value Symbol Guard)
    (leftValid : Valid before) (rightValid : Valid later) (facts : Facts common)
    (leftInputs : Values common firstInputs) (rightInputs : Values common secondInputs)
    (related : Related first firstInputs second secondInputs)
    (leftDone : build first firstInputs before = .done left after)
    (rightDone : build second secondInputs later = .done right final)
    (leftGrowth : Grows after common) (rightGrowth : Grows final common) : left = right :=
  warm first firstInputs second secondInputs common left right facts leftInputs rightInputs related
    (build_replay first firstInputs before common left after leftValid leftDone leftGrowth)
    (build_replay second secondInputs later common right final rightValid rightDone rightGrowth)

private theorem complete [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (ready : Ready before) (inputs : Values before environment) :
    ∃ value after, build expression environment before = .done value after ∧
      Keeps before after ∧ Available after value := by
  let context : InternedFreshOrdinaryContext.Context before environment :=
    ⟨ready.semantic.1.normal, inputs, ready.semantic.1.profiles, ready.semantic.1.freeNames⟩
  obtain ⟨value, after, actual⟩ := InternedRecordDepthCompletion.source_complete expression environment before
    context ready.semantic.2 ready.covered
  have checked := InternedFreshOrdinaryFacts.build_verified expression environment before context.normal.facts inputs
  have semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap after := by
    simpa only [actual, Outcome.state] using
      SourceRecursiveIntersectionSemanticHeap.source expression environment before ready.semantic inputs
  have openDepth : InternedOpenDepthReadback.Heap after := by
    simpa only [actual, Outcome.state] using
      (InternedOpenDepthExecution.build_depth expression environment before context ready.semantic.2 ready.depth).heap
  refine ⟨value, after, actual, ⟨⟨semantic, ?_, openDepth⟩, ?_, ?_⟩, checked.result value after actual⟩
  · exact InternedFreshOrdinaryCoverage.build_covered expression environment before
      context.normal.facts.coherent.valid ready.covered value after actual
  · simpa only [actual, Outcome.state] using checked.growth
  · simpa only [actual, Outcome.state] using checked.history

/-- Initial ready captures construct both recursively normalized plans with one identical result. -/
theorem initial [DecidableEq (EdgeKey Symbol Guard)]
    (first second : Syntax Symbol Guard) (firstInputs secondInputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (ready : Ready before)
    (leftInputs : Values before firstInputs) (rightInputs : Values before secondInputs)
    (related : Related first firstInputs second secondInputs) :
    ∃ value middle after,
      build first firstInputs before = .done value middle ∧
      build second secondInputs middle = .done value after ∧
      Keeps before middle ∧ Keeps middle after ∧ Available after value := by
  obtain ⟨left, middle, leftDone, firstKept, leftAvailable⟩ := complete first firstInputs before ready leftInputs
  have secondInputsAvailable : Values middle secondInputs :=
    fun value member => firstKept.available value (rightInputs value member)
  obtain ⟨right, after, rightDone, secondKept, rightAvailable⟩ :=
    complete second secondInputs middle firstKept.ready secondInputsAvailable
  have equal := completed first second firstInputs secondInputs before middle middle after after left right
    ready.semantic.1.normal.facts.coherent.valid firstKept.ready.semantic.1.normal.facts.coherent.valid
    secondKept.ready.semantic.1.normal.facts
    (fun value member => secondKept.available value (firstKept.available value (leftInputs value member)))
    (fun value member => secondKept.available value (secondInputsAvailable value member))
    related leftDone rightDone secondKept.growth (grows_refl after)
  cases equal
  exact ⟨left, middle, after, leftDone, rightDone, firstKept, secondKept, rightAvailable⟩

end MicroCFTA.SourceCurrentNormalizedPlanCongruence
