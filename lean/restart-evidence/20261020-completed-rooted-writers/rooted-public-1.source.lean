import MicroCFTA.SourceCurrentNativeMuIssuedWriters
import MicroCFTA.InternedFreshOrdinarySourceHistory

/-!
# Rooted writers from actual completed source construction

The actual source call derives an issued path with rooted publications.
Selection keeps the rooted receipt and all issued writer intervals in the
same publication witness. No source root is inferred from an arbitrary
issued path. Initial Mu records must be absent for this source-only result.
-/
namespace MicroCFTA.SourceCurrentCompletedBuildRootedWriters
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges ordinaryLevel)
open InternedFreshOrdinaryFacts (callback buildMany_verified)
open InternedNestedProvenance (depth_available ordinary_available)
open InternedBinderProtocol (NodeKey Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentNativeMuGrowthHistory (reserve_growth publication_growth)
open InternedFreshOrdinaryActiveOrigins (Crossing Entered)
open InternedFreshOrdinarySourceHistory (Reached reached_initial)

/-- One selected publication keeps its original source route and exact issued writer intervals. -/
def Written [DecidableEq (EdgeKey Symbol Guard)]
    (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    (before after : State Symbol Guard) (key : NodeKey) (value : Value Symbol Guard) : Prop :=
  ∃ event : Publication (Symbol := Symbol) (Guard := Guard),
    Reached root initial (.binder event.smart event.expression) event.environment event.before ∧
    key = event.key ∧ value = event.candidate ∧ event.afterBody.nodeRecords event.key = none ∧
    Nonempty (Path before event.before) ∧
    Nonempty (Path event.before event.afterDepth) ∧
    Nonempty (Path event.afterDepth event.cut) ∧
    Nonempty (Path event.allocated event.afterBody) ∧
    Grows event.after after ∧ Extends event.after.nodes.issued after.nodes.issued

private def Rooted [DecidableEq (EdgeKey Symbol Guard)]
    (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    {before after : State Symbol Guard} : Path before after → Prop
  | .refl _ | .retain _ _ _ _ _ => True
  | .trans first next => Rooted root initial first ∧ Rooted root initial next
  | .publication event depth ordinary body =>
      Reached root initial (.binder event.smart event.expression) event.environment event.before ∧
      Rooted root initial depth ∧ Rooted root initial ordinary ∧ Rooted root initial body

private def Supported [DecidableEq (EdgeKey Symbol Guard)]
    (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    (before after : State Symbol Guard) : Prop :=
  ∃ path : Path before after, Rooted root initial path

private theorem supported_growth [DecidableEq (EdgeKey Symbol Guard)]
    {root : Syntax Symbol Guard} {initial : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (actual : Supported root initial before after) :
    Grows before after := by
  obtain ⟨path,_⟩ := actual
  exact path.growth

private theorem supported_bind [DecidableEq (EdgeKey Symbol Guard)]
    (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    (before : State Symbol Guard) (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (first : Supported root initial before outcome.state)
    (later : ∀ value after, outcome = .done value after → Supported root initial after (next value after).state) :
    Supported root initial before (outcome.bind next).state := by
  cases outcome with
  | pending => exact first
  | done value after =>
      obtain ⟨left,leftRoot⟩ := first
      obtain ⟨right,rightRoot⟩ := later value after rfl
      exact ⟨.trans left right,leftRoot,rightRoot⟩

private theorem supported_binder [DecidableEq (EdgeKey Symbol Guard)]
    (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    (smart : Bool) (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (context : Context state environment)
    (reached : Reached root initial (.binder smart expression) environment state)
    (checked : ∀ name current, Entered smart expression environment state name current →
      Context current environment → Available current (.reference name) →
      Supported root initial current (callback expression environment name current).state) :
    Supported root initial state ((callback expression environment .depth state).bind fun depth afterDepth =>
      (callback expression environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary cut =>
        request smart depth ordinary (callback expression environment) cut).state := by
  have depthPath := checked .depth state .depth context (depth_available state)
  cases depthDone : callback expression environment .depth state with
  | pending key after => simpa only [depthDone,Outcome.bind,Outcome.state] using depthPath
  | done depth afterDepth =>
      have depthPath' : Supported root initial state afterDepth := by
        simpa only [depthDone,Outcome.state] using depthPath
      have depthContext : Context afterDepth environment := by
        simpa only [depthDone,Outcome.state] using context.callback expression .depth (depth_available state)
      have ordinaryPath := checked (.uninterned (ordinaryLevel depth)) afterDepth
        (.ordinary depth afterDepth depthDone) depthContext (ordinary_available afterDepth (ordinaryLevel depth))
      simp only [Outcome.bind]
      cases ordinaryDone : callback expression environment (.uninterned (ordinaryLevel depth)) afterDepth with
      | pending key after =>
          obtain ⟨first,firstRoot⟩ := depthPath'
          obtain ⟨second,secondRoot⟩ : Supported root initial afterDepth after := by
            simpa only [ordinaryDone,Outcome.state] using ordinaryPath
          exact ⟨.trans first second,firstRoot,secondRoot⟩
      | done ordinary cut =>
          obtain ⟨depthPath,depthRoot⟩ := depthPath'
          obtain ⟨ordinaryPath,ordinaryRoot⟩ : Supported root initial afterDepth cut := by
            simpa only [ordinaryDone,Outcome.state] using ordinaryPath
          have cutContext : Context cut environment := by
            simpa only [ordinaryDone,Outcome.state] using depthContext.callback expression
              (.uninterned (ordinaryLevel depth)) (ordinary_available afterDepth (ordinaryLevel depth))
          cases missing : cut.nodes.table (muKey depth ordinary) with
          | some entry =>
              cases found : cut.nodeRecords (muKey depth ordinary) <;>
                simpa only [request,missing,found,Outcome.state] using
                  (show Supported root initial state cut from ⟨.trans depthPath ordinaryPath,depthRoot,ordinaryRoot⟩)
          | none =>
              let entry := Cache.intern cut.nodes (muKey depth ordinary)
              let allocated := {cut with nodes := entry.2}
              let reservePath : Path cut allocated := .retain cut allocated (fun _ _ _ _ _ present => present)
                ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
                (InternedFreshProbeKeys.intern_issued_extends cut.nodes (muKey depth ordinary)
                  cutContext.base.normal.facts.coherent.valid.2)
              have reserved : Context allocated environment := cutContext.reserve (muKey depth ordinary)
              have argument : Available allocated (.reference (.interned entry.1.identity)) :=
                (InternedConstructionProvenance.reserve_available (muKey depth ordinary) cut
                  cutContext.base.normal.facts.coherent cutContext.base.normal.facts.cached).2
              have bodyPath := checked (.interned entry.1.identity) allocated
                (.fresh depth ordinary afterDepth cut depthDone ordinaryDone missing) reserved argument
              simp only [Outcome.bind,request,missing]
              change Supported root initial state ((callback expression environment (.interned entry.1.identity) allocated).bind
                (fun value after => InternedNestedRequestFacts.complete smart entry.1 value depth ordinary after)).state
              cases bodyDone : callback expression environment (.interned entry.1.identity) allocated with
              | pending key after =>
                  obtain ⟨last,lastRoot⟩ : Supported root initial allocated after := by
                    simpa only [bodyDone,Outcome.state] using bodyPath
                  exact ⟨.trans (.trans depthPath ordinaryPath) (.trans reservePath last),
                    ⟨depthRoot,ordinaryRoot⟩,True.intro,lastRoot⟩
              | done body afterBody =>
                  let event : Publication (Symbol := Symbol) (Guard := Guard) :=
                    ⟨smart,expression,environment,state,afterDepth,cut,afterBody,depth,ordinary,body,
                      context,depthDone,ordinaryDone,missing,bodyDone⟩
                  obtain ⟨last,lastRoot⟩ : Supported root initial allocated afterBody := by
                    simpa only [bodyDone,Outcome.state] using bodyPath
                  exact ⟨.publication event depthPath ordinaryPath last,reached,depthRoot,ordinaryRoot,lastRoot⟩

mutual
private theorem build_supported [DecidableEq (EdgeKey Symbol Guard)]
    (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (context : Context state environment)
    (reached : Reached root initial expression environment state) :
    Supported root initial state (build expression environment state).state := by
  cases expression with
  | empty | var =>
      simpa only [build,Outcome.state] using
        (show Supported root initial state state from ⟨.refl state,True.intro⟩)
  | node edges =>
      rw [build]
      apply supported_bind root initial state _ _
        (buildEdges_supported root initial edges environment state context
          (fun symbol guard children member child included => reached.node member included))
      intro values after returned
      have afterContext : Context after environment := by
        simpa only [returned,Outcome.state] using context.edges edges
      exact ⟨.retain after _ (InternedShallowHeap.makeNode_noNewMu values after)
        (run_correct _ after afterContext.base.normal.facts.coherent.valid).2
        (run_issued_extends _ after afterContext.base.normal.facts.coherent.valid),True.intro⟩
  | union members =>
      rw [build]
      apply supported_bind root initial state _ _
        (buildMany_supported root initial members environment state context (fun child member => reached.union member))
      intro values after returned
      have afterContext : Context after environment := by
        simpa only [returned,Outcome.state] using context.many members
      exact ⟨.retain after _ (InternedShallowHeap.makeUnion_noNewMu values after)
        (run_correct _ after afterContext.base.normal.facts.coherent.valid).2
        (run_issued_extends _ after afterContext.base.normal.facts.coherent.valid),True.intro⟩
  | binder smart body =>
      rw [build]
      apply supported_binder root initial smart body environment state context reached
      intro name current entered currentContext argument
      let crossing : Crossing Symbol Guard := ⟨smart,body,environment,state,name,current,context.base,entered⟩
      exact supported_bind root initial current _ _
        (build_supported root initial body _ current (currentContext.local name argument) (Reached.enter crossing reached))
        (fun value after returned => by
          have afterContext : Context after (.reference name :: environment) := by
            simpa only [returned,Outcome.state] using (currentContext.local name argument).build body
          exact ⟨.retain after _ (InternedStoredMuOrigins.filter_noNewMu name value after)
            (run_correct _ after afterContext.base.normal.facts.coherent.valid).2
            (run_issued_extends _ after afterContext.base.normal.facts.coherent.valid),True.intro⟩)
termination_by sizeOf expression

private theorem buildMany_supported [DecidableEq (EdgeKey Symbol Guard)]
    (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    (expressions : List (Syntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (context : Context state environment)
    (reached : ∀ expression ∈ expressions, Reached root initial expression environment state) :
    Supported root initial state (buildMany expressions environment state).state := by
  cases expressions with
  | nil =>
      simpa only [buildMany,Outcome.state] using
        (show Supported root initial state state from ⟨.refl state,True.intro⟩)
  | cons first rest =>
      rw [buildMany]
      have firstPath := build_supported root initial first environment state context (reached first List.mem_cons_self)
      apply supported_bind root initial state _ _ firstPath
      intro value after returned
      have afterContext : Context after environment := by
        simpa only [returned,Outcome.state] using context.build first
      have firstGrowth : Grows state after := supported_growth (by simpa only [returned,Outcome.state] using firstPath)
      apply supported_bind root initial after _ _
        (buildMany_supported root initial rest environment after afterContext
          (fun child member => (reached child (List.mem_cons_of_mem first member)).grows firstGrowth))
      intro _ final _
      exact ⟨.refl final,True.intro⟩
termination_by sizeOf expressions

private theorem buildEdges_supported [DecidableEq (EdgeKey Symbol Guard)]
    (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (context : Context state environment)
    (reached : ∀ symbol guard children, .mk symbol guard children ∈ expressions →
      ∀ expression ∈ children, Reached root initial expression environment state) :
    Supported root initial state (buildEdges expressions environment state).state := by
  cases expressions with
  | nil =>
      simpa only [buildEdges,Outcome.state] using
        (show Supported root initial state state from ⟨.refl state,True.intro⟩)
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          rw [buildEdges]
          have childPath := buildMany_supported root initial children environment state context
            (reached symbol guard children List.mem_cons_self)
          apply supported_bind root initial state _ _ childPath
          intro values after returned
          have afterContext : Context after environment := by
            simpa only [returned,Outcome.state] using context.many children
          have available := (buildMany_verified children environment state context.base.normal.facts
            context.base.inputs).result values after returned
          have childGrowth : Grows state after := supported_growth (by simpa only [returned,Outcome.state] using childPath)
          let result := run (makeEdge symbol guard values) after
          have edgeContext : Context result.2 environment := afterContext.edge symbol guard values available
          let edgePath : Path after result.2 := .retain after result.2 (fun _ _ _ _ _ present => present)
            (run_correct _ after afterContext.base.normal.facts.coherent.valid).2
            (run_issued_extends _ after afterContext.base.normal.facts.coherent.valid)
          change Supported root initial after ((buildEdges rest environment result.2).bind _).state
          have restSupported := buildEdges_supported root initial rest environment result.2 edgeContext
            (fun s g cs member child included =>
              (reached s g cs (List.mem_cons_of_mem (.mk symbol guard children) member) child included).grows
                (grows_trans childGrowth edgePath.growth))
          obtain ⟨restPath,restRoot⟩ := supported_bind root initial result.2
            (buildEdges rest environment result.2) (fun edges final => .done (result.1 :: edges) final)
            restSupported (fun _ final _ => ⟨.refl final,True.intro⟩)
          exact ⟨.trans edgePath restPath,True.intro,restRoot⟩
termination_by sizeOf expressions
end

private theorem prepend [DecidableEq (EdgeKey Symbol Guard)]
    {root : Syntax Symbol Guard} {initial : List (Value Symbol Guard)}
    {before middle after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (earlier : Path before middle) (written : Written root initial middle after key value) :
    Written root initial before after key value := by
  obtain ⟨event,site,keySame,valueSame,missing,⟨first⟩,depth,ordinary,body,growth,issued⟩ := written
  exact ⟨event,site,keySame,valueSame,missing,⟨.trans earlier first⟩,depth,ordinary,body,growth,issued⟩

private theorem later [DecidableEq (EdgeKey Symbol Guard)]
    {root : Syntax Symbol Guard} {initial : List (Value Symbol Guard)}
    {before middle after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (written : Written root initial before middle key value) (growth : Grows middle after)
    (issued : Extends middle.nodes.issued after.nodes.issued) : Written root initial before after key value := by
  obtain ⟨event,site,keySame,valueSame,missing,first,depth,ordinary,body,earlier,earlierIssued⟩ := written
  exact ⟨event,site,keySame,valueSame,missing,first,depth,ordinary,body,
    grows_trans earlier growth,extends_trans earlierIssued issued⟩

private theorem reserve_issued [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    Extends event.cut.nodes.issued event.allocated.nodes.issued := by
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  exact InternedFreshProbeKeys.intern_issued_extends event.cut.nodes event.key cutContext.base.normal.facts.coherent.valid.2

private theorem writers [DecidableEq (EdgeKey Symbol Guard)]
    {root : Syntax Symbol Guard} {initial : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (path : Path before after) (rooted : Rooted root initial path)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : after.nodeRecords key = some (.mu entry body depth ordinary)) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
      Written root initial before after key (.mu entry body depth ordinary) := by
  revert rooted present
  induction path with
  | refl => intro _ present; exact .inl present
  | retain before after old _growth _issued => intro _ present; exact .inl (old key entry body depth ordinary present)
  | trans first next firstIH nextIH =>
      intro rooted present
      rcases nextIH rooted.2 present with old | written
      · rcases firstIH rooted.1 old with initial | written
        · exact .inl initial
        · exact .inr (later written next.growth next.issued)
      · exact .inr (prepend first written)
  | publication event depthPath ordinaryPath bodyPath depthIH ordinaryIH bodyIH =>
      intro rooted present
      obtain ⟨site,depthRoot,ordinaryRoot,bodyRoot⟩ := rooted
      have reserve : Path event.cut event.allocated :=
        .retain event.cut event.allocated (fun _ _ _ _ _ found => found) (reserve_growth event) (reserve_issued event)
      have cutGrowth : Grows event.cut event.after :=
        grows_trans (reserve_growth event) (grows_trans bodyPath.growth (publication_growth event))
      have depthGrowth : Grows event.afterDepth event.after := grows_trans ordinaryPath.growth cutGrowth
      have cutIssued : Extends event.cut.nodes.issued event.after.nodes.issued :=
        extends_trans (reserve_issued event) bodyPath.issued
      have depthIssued : Extends event.afterDepth.nodes.issued event.after.nodes.issued :=
        extends_trans ordinaryPath.issued cutIssued
      have prior (old : event.afterBody.nodeRecords key = some (.mu entry body depth ordinary)) :
          event.before.nodeRecords key = some (.mu entry body depth ordinary) ∨
            Written root initial event.before event.after key (.mu entry body depth ordinary) := by
        rcases bodyIH bodyRoot old with allocated | written
        · rcases ordinaryIH ordinaryRoot allocated with afterDepth | written
          · rcases depthIH depthRoot afterDepth with initial | written
            · exact .inl initial
            · exact .inr (later written depthGrowth depthIssued)
          · exact .inr (later (prepend depthPath written) cutGrowth cutIssued)
        · exact .inr (later (prepend (.trans (.trans depthPath ordinaryPath) reserve) written)
            (publication_growth event) (extends_refl _))
      rcases record_cases event.afterBody.nodeRecords event.key key event.candidate
        (.mu entry body depth ordinary) present with old | ⟨sameKey,sameValue⟩
      · exact prior old
      · cases firstWrite : event.afterBody.nodeRecords event.key with
        | none => exact .inr ⟨event,site,sameKey,sameValue,firstWrite,⟨.refl event.before⟩,
            ⟨depthPath⟩,⟨ordinaryPath⟩,⟨bodyPath⟩,grows_refl event.after,extends_refl _⟩
        | some previous =>
            apply prior
            change keepFirst event.afterBody.nodeRecords event.key event.candidate key =
              some (.mu entry body depth ordinary) at present
            simpa only [keepFirst,firstWrite] using present

/-- A completed source call derives its selected writer and original rooted source route. -/
theorem build_writer [DecidableEq (EdgeKey Symbol Guard)]
    (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    (before : State Symbol Guard) (context : Context before initial)
    (initialMuFree : ∀ key entry body depth ordinary,
      before.nodeRecords key ≠ some (.mu entry body depth ordinary))
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : build root initial before = .done result after)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (selected : after.nodeRecords key = some (.mu entry body depth ordinary)) :
    Written root initial before after key (.mu entry body depth ordinary) := by
  have supported := build_supported root initial root initial before context (reached_initial root initial before)
  rw [actual] at supported
  obtain ⟨path,rooted⟩ := supported
  rcases writers path rooted key entry body depth ordinary selected with old | written
  · exact False.elim (initialMuFree key entry body depth ordinary old)
  · exact written

end MicroCFTA.SourceCurrentCompletedBuildRootedWriters

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentCompletedBuildRootedWriters.Written
#print MicroCFTA.SourceCurrentCompletedBuildRootedWriters.Written
#print axioms MicroCFTA.SourceCurrentCompletedBuildRootedWriters.Written
#check @MicroCFTA.SourceCurrentCompletedBuildRootedWriters.build_writer
#print MicroCFTA.SourceCurrentCompletedBuildRootedWriters.build_writer
#print axioms MicroCFTA.SourceCurrentCompletedBuildRootedWriters.build_writer
