import MicroCFTA.SourceCurrentRowPlanReplay
import MicroCFTA.InternedNestedSpecialization

/-!
# Exact parts of warm repaired construction

A successful warm call returns to its initial heap. Each actual prefix
also returns to that heap. Replay identifies the prefix heap without
an antisymmetry premise for cache growth. The results include both raw
binder probes, their filters, and the final request.
-/
namespace MicroCFTA.SourceCurrentWarmConstructionParts
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request Growing Replays)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryGrowth InternedFreshOrdinaryReplay
open InternedBinderProtocol (Reference)
open Language

/-- Each stage of an actual warm bind returns to the same common heap. -/
theorem bind
    (first : State Symbol Guard → Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (common : State Symbol Guard) (output : Result) (valid : Valid common)
    (firstGrowing : Growing first) (nextGrowing : ∀ value, Growing (next value))
    (firstReplay : Replays first)
    (actual : (first common).bind next = .done output common) :
    ∃ input, first common = .done input common ∧ next input common = .done output common := by
  rcases InternedNestedSpecialization.bind_done _ _ _ _ actual with
    ⟨input, middle, firstDone, nextDone⟩
  have middleValid : Valid middle := by
    simpa only [firstDone, Outcome.state] using (firstGrowing common valid).1
  have suffix : Grows middle common := by
    simpa only [nextDone, Outcome.state] using (nextGrowing input middle middleValid).2
  have again := firstReplay common common input middle valid firstDone suffix
  have same := (Outcome.done.inj (firstDone.symm.trans again)).2
  subst middle
  exact ⟨input, firstDone, nextDone⟩

/-- A warm child list supplies each actual child call in its original order. -/
theorem many [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (common : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (valid : Valid common)
    (actual : buildMany expressions environment common = .done outputs common) :
    All₂ (fun expression output => build expression environment common = .done output common) expressions outputs := by
  induction expressions generalizing outputs with
  | nil =>
      simp only [buildMany, Outcome.done.injEq] at actual
      rcases actual with ⟨rfl, _⟩
      exact .nil
  | cons expression expressions ih =>
      have laterGrowing : ∀ value, Growing (fun state =>
          (buildMany expressions environment state).bind fun values after => .done (value :: values) after) := by
        intro value state retained
        exact InternedNestedConstruction.bind_correct _ _ state
          (buildMany_correct expressions environment state retained)
          (fun values after afterValid => ⟨afterValid, grows_refl _⟩)
      rcases bind (build expression environment) _ common outputs valid
        (build_correct expression environment) laterGrowing (build_replays expression environment) actual with
        ⟨value, firstDone, laterDone⟩
      rcases bind (buildMany expressions environment) _ common outputs valid
        (buildMany_correct expressions environment)
        (fun values state retained => ⟨retained, grows_refl _⟩)
        (buildMany_replays expressions environment) laterDone with ⟨values, restDone, finalDone⟩
      cases finalDone
      exact .cons firstDone (ih values restDone)

/-- A warm row list supplies each exact row plan in its original order. -/
theorem rows [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (common : State Symbol Guard)
    (outputs : List (EdgeValue Symbol Guard)) (valid : Valid common)
    (actual : buildEdges expressions environment common = .done outputs common) :
    All₂ (fun expression output => SourceCurrentRowPlanReplay.rowRun expression environment common =
      .done output common) expressions outputs :=
  SourceCurrentRowPlanReplay.rows expressions environment common outputs common common valid actual (grows_refl _)

private theorem work_done [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Result)
    (common : State Symbol Guard) (output : Result)
    (actual : work computation common = .done output common) : run computation common = (output, common) := by
  have same := Outcome.done.inj actual
  exact Prod.ext same.1 same.2

/-- A warm node call supplies its actual row list and its exact final node request. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (common : State Symbol Guard)
    (output : Value Symbol Guard) (valid : Valid common)
    (actual : build (.node expressions) environment common = .done output common) :
    ∃ values, buildEdges expressions environment common = .done values common ∧
      run (makeNode values) common = (output, common) := by
  rcases bind (buildEdges expressions environment) (fun values state => work (makeNode values) state)
    common output valid (buildEdges_correct expressions environment)
    (fun values => InternedNestedConstruction.work_correct (makeNode values))
    (buildEdges_replays expressions environment) actual with ⟨values, firstDone, finalDone⟩
  exact ⟨values, firstDone, work_done _ _ _ finalDone⟩

/-- A warm union call supplies its ordered member results and its exact union request. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (common : State Symbol Guard)
    (output : Value Symbol Guard) (valid : Valid common)
    (actual : build (.union expressions) environment common = .done output common) :
    ∃ values, buildMany expressions environment common = .done values common ∧
      run (makeUnion values) common = (output, common) := by
  rcases bind (buildMany expressions environment) (fun values state => work (makeUnion values) state)
    common output valid (buildMany_correct expressions environment)
    (fun values => InternedNestedConstruction.work_correct (makeUnion values))
    (buildMany_replays expressions environment) actual with ⟨values, firstDone, finalDone⟩
  exact ⟨values, firstDone, work_done _ _ _ finalDone⟩

private theorem callback_growing [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) :
    Growing (InternedFreshOrdinaryFacts.callback body environment name) := by
  intro state valid
  exact InternedNestedConstruction.bind_correct _ _ state (build_correct body _ state valid)
    (fun value after retained => InternedNestedConstruction.work_correct (withoutSelfReference name value) after retained)

/-- A warm normalized callback supplies the raw body call and its exact filter at the common heap. -/
theorem callback [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (common : State Symbol Guard)
    (output : Value Symbol Guard) (valid : Valid common)
    (actual : InternedFreshOrdinaryFacts.callback body environment name common = .done output common) :
    ∃ raw, build body (.reference name :: environment) common = .done raw common ∧
      run (withoutSelfReference name raw) common = (output, common) := by
  rcases bind (build body (.reference name :: environment))
    (fun value state => work (withoutSelfReference name value) state) common output valid
    (build_correct body _) (fun value => InternedNestedConstruction.work_correct (withoutSelfReference name value))
    (build_replays body _) actual with ⟨raw, rawDone, filterDone⟩
  exact ⟨raw, rawDone, work_done _ _ _ filterDone⟩

/-- An actual warm binder supplies both probes, both raw calls and filters, and its request at one heap. -/
theorem binder [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (common : State Symbol Guard)
    (output : Value Symbol Guard) (valid : Valid common)
    (actual : build (.binder smart body) environment common = .done output common) :
    ∃ depth ordinary rawDepth rawOrdinary,
      InternedFreshOrdinaryFacts.callback body environment .depth common = .done depth common ∧
      InternedFreshOrdinaryFacts.callback body environment (.uninterned (ordinaryLevel depth)) common = .done ordinary common ∧
      build body (.reference .depth :: environment) common = .done rawDepth common ∧
      run (withoutSelfReference .depth rawDepth) common = (depth, common) ∧
      build body (.reference (.uninterned (ordinaryLevel depth)) :: environment) common = .done rawOrdinary common ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) rawOrdinary) common = (ordinary, common) ∧
      request smart depth ordinary (InternedFreshOrdinaryFacts.callback body environment) common = .done output common := by
  have laterGrowing : ∀ depth, Growing (fun state =>
      (InternedFreshOrdinaryFacts.callback body environment (.uninterned (ordinaryLevel depth)) state).bind
        fun ordinary after => request smart depth ordinary (InternedFreshOrdinaryFacts.callback body environment) after) := by
    intro depth state retained
    exact InternedNestedConstruction.bind_correct _ _ state (callback_growing body environment _ state retained)
      (fun ordinary => InternedNestedConstruction.request_correct smart depth ordinary _ (callback_growing body environment))
  rcases bind (InternedFreshOrdinaryFacts.callback body environment .depth) _ common output valid
    (callback_growing body environment .depth) laterGrowing (callback_replays body environment .depth) actual with
    ⟨depth, depthDone, laterDone⟩
  rcases bind (InternedFreshOrdinaryFacts.callback body environment (.uninterned (ordinaryLevel depth))) _ common output valid
    (callback_growing body environment _) (fun ordinary =>
      InternedNestedConstruction.request_correct smart depth ordinary _ (callback_growing body environment))
    (callback_replays body environment _) laterDone with ⟨ordinary, ordinaryDone, requestDone⟩
  rcases callback body environment .depth common depth valid depthDone with ⟨rawDepth, rawDepthDone, depthFilter⟩
  rcases callback body environment _ common ordinary valid ordinaryDone with ⟨rawOrdinary, rawOrdinaryDone, ordinaryFilter⟩
  exact ⟨depth, ordinary, rawDepth, rawOrdinary, depthDone, ordinaryDone, rawDepthDone, depthFilter,
    rawOrdinaryDone, ordinaryFilter, requestDone⟩

end MicroCFTA.SourceCurrentWarmConstructionParts
