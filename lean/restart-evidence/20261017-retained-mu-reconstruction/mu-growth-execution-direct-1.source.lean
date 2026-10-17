import MicroCFTA.SourceCurrentNativeMuGrowthHistory

/-!
# Actual source execution with causal publication growth

Each actual stopping state has a path that retains publication order and
cache growth. Each ordinary Work step uses its actual returned state.
The result does not require successful source completion.
-/
namespace MicroCFTA.SourceCurrentNativeMuGrowthExecution
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedNestedFacts InternedNestedRequestFacts InternedFreshProbeKeys InternedShallowHeap
open InternedNestedProvenance (depth_available ordinary_available)
open InternedStoredMuOrigins (filter_noNewMu)
open InternedConstructionProvenance InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuGrowthHistory (Path)

private def bind_path [DecidableEq (EdgeKey Symbol Guard)] (before : State Symbol Guard)
    (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (first : Path before outcome.state)
    (later : ∀ value after, outcome = .done value after → Path after (next value after).state) :
    Path before (outcome.bind next).state := by
  cases outcome with
  | pending => exact first
  | done value after => exact .trans first (later value after rfl)

private def binder_path [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment)
    (checked : ∀ name current, Context current environment → Available current (.reference name) →
      Path current (callback expression environment name current).state) :
    Path state ((callback expression environment .depth state).bind fun depth afterDepth =>
      (callback expression environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary cut =>
        request smart depth ordinary (callback expression environment) cut).state := by
  have depthPath := checked .depth state context (depth_available state)
  cases depthDone : callback expression environment .depth state with
  | pending key after => simpa only [depthDone, Outcome.bind, Outcome.state] using depthPath
  | done depth afterDepth =>
      have depthPath' : Path state afterDepth := by simpa only [depthDone, Outcome.state] using depthPath
      have depthContext : Context afterDepth environment := by
        simpa only [depthDone, Outcome.state] using context.callback expression .depth (depth_available state)
      have ordinaryPath := checked (.uninterned (ordinaryLevel depth)) afterDepth depthContext
        (ordinary_available afterDepth (ordinaryLevel depth))
      simp only [Outcome.bind]
      cases ordinaryDone : callback expression environment (.uninterned (ordinaryLevel depth)) afterDepth with
      | pending key after =>
          exact .trans depthPath' (by simpa only [ordinaryDone, Outcome.state] using ordinaryPath)
      | done ordinary cut =>
          have ordinaryPath' : Path afterDepth cut := by simpa only [ordinaryDone, Outcome.state] using ordinaryPath
          have cutContext : Context cut environment := by
            simpa only [ordinaryDone, Outcome.state] using depthContext.callback expression
              (.uninterned (ordinaryLevel depth)) (ordinary_available afterDepth (ordinaryLevel depth))
          cases missing : cut.nodes.table (muKey depth ordinary) with
          | some entry =>
              cases found : cut.nodeRecords (muKey depth ordinary) <;>
                simpa only [request, missing, found, Outcome.state] using .trans depthPath' ordinaryPath'
          | none =>
              let entry := Cache.intern cut.nodes (muKey depth ordinary)
              let allocated := {cut with nodes := entry.2}
              have reservePath : Path cut allocated := .retain cut allocated (fun _ _ _ _ _ present => present)
                ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
              have reserved : Context allocated environment := cutContext.reserve (muKey depth ordinary)
              have argument : Available allocated (.reference (.interned entry.1.identity)) :=
                (reserve_available (muKey depth ordinary) cut cutContext.base.normal.facts.coherent
                  cutContext.base.normal.facts.cached).2
              have bodyPath := checked (.interned entry.1.identity) allocated reserved argument
              simp only [request, missing]
              change Path state ((callback expression environment (.interned entry.1.identity) allocated).bind
                (fun value after => complete smart entry.1 value depth ordinary after)).state
              cases bodyDone : callback expression environment (.interned entry.1.identity) allocated with
              | pending key after =>
                  exact .trans (.trans depthPath' ordinaryPath') (.trans reservePath
                    (by simpa only [bodyDone, Outcome.bind, Outcome.state] using bodyPath))
              | done body afterBody =>
                  let event : Publication (Symbol := Symbol) (Guard := Guard) :=
                    ⟨smart, expression, environment, state, afterDepth, cut, afterBody, depth, ordinary, body,
                      context, depthDone, ordinaryDone, missing, bodyDone⟩
                  exact Path.publication event depthPath' ordinaryPath'
                    (by
                      change Path allocated afterBody
                      simpa only [bodyDone, Outcome.state] using bodyPath)

mutual
/-- Full repaired source execution produces its actual publication history at every stopping state. -/
theorem build_path [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment) :
    Nonempty (Path state (build expression environment state).state) := by
  apply Nonempty.intro
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using Path.refl state
  | node edges =>
      rw [build]
      exact bind_path state _ _ (Classical.choice (buildEdges_path edges environment state context))
        (fun values after returned => by
          have afterContext : Context after environment := by
            simpa only [returned, Outcome.state] using context.edges edges
          exact .retain after _ (makeNode_noNewMu values after)
            (InternedConstructorTemplates.run_correct _ after afterContext.base.normal.facts.coherent.valid).2)
  | union members =>
      rw [build]
      exact bind_path state _ _ (Classical.choice (buildMany_path members environment state context))
        (fun values after returned => by
          have afterContext : Context after environment := by
            simpa only [returned, Outcome.state] using context.many members
          exact .retain after _ (makeUnion_noNewMu values after)
            (InternedConstructorTemplates.run_correct _ after afterContext.base.normal.facts.coherent.valid).2)
  | binder smart body =>
      rw [build]
      apply binder_path smart body environment state context
      intro name current currentContext argument
      exact bind_path current _ _ (Classical.choice (build_path body _ current (currentContext.local name argument)))
        (fun value after returned => by
          have afterContext : Context after (.reference name :: environment) := by
            simpa only [returned, Outcome.state] using (currentContext.local name argument).build body
          exact .retain after _ (filter_noNewMu name value after)
            (InternedConstructorTemplates.run_correct _ after afterContext.base.normal.facts.coherent.valid).2)
termination_by sizeOf expression

/-- Ordered child construction produces the histories of the children that actually execute. -/
theorem buildMany_path [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment) :
    Nonempty (Path state (buildMany expressions environment state).state) := by
  apply Nonempty.intro
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using Path.refl state
  | cons first rest =>
      rw [buildMany]
      apply bind_path state _ _ (Classical.choice (build_path first environment state context))
      intro value after returned
      have afterContext : Context after environment := by
        simpa only [returned, Outcome.state] using context.build first
      exact bind_path after _ _ (Classical.choice (buildMany_path rest environment after afterContext))
        (fun _ final _ => .refl final)
termination_by sizeOf expressions

/-- Ordered rows retain callback histories even when normalization discards a row. -/
theorem buildEdges_path [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment) :
    Nonempty (Path state (buildEdges expressions environment state).state) := by
  apply Nonempty.intro
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using Path.refl state
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          rw [buildEdges]
          apply bind_path state _ _ (Classical.choice (buildMany_path children environment state context))
          intro values after returned
          have afterContext : Context after environment := by
            simpa only [returned, Outcome.state] using context.many children
          have available := (buildMany_verified children environment state context.base.normal.facts
            context.base.inputs).result values after returned
          let result := run (makeEdge symbol guard values) after
          have edgeContext : Context result.2 environment := afterContext.edge symbol guard values available
          change Path after ((buildEdges rest environment result.2).bind _).state
          exact .trans (.retain after result.2 (fun _ _ _ _ _ present => present)
            (InternedConstructorTemplates.run_correct _ after afterContext.base.normal.facts.coherent.valid).2)
            (bind_path result.2 _ _ (Classical.choice (buildEdges_path rest environment result.2 edgeContext))
              (fun _ final _ => .refl final))
termination_by sizeOf expressions
end

/-- A closed source starts this history at the actual empty tables. -/
noncomputable def closed_path [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Path empty (build expression [] empty).state :=
  Classical.choice (build_path expression [] empty SourceCurrentConstrainedCapSourcePath.empty_context)

end MicroCFTA.SourceCurrentNativeMuGrowthExecution
