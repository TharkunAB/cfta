import MicroCFTA.SourceCurrentCompletedBuildRootedWriters

/-!
# Original source writers in one actual publication trace

One completed source build supplies one rooted issued path.
Its postorder events retain indexed final and earlier callback writers.
-/
namespace MicroCFTA.SourceCurrentNativeOriginalPublicationTrace
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

/-- This list follows the actual callback and publication completion order. -/
def events {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    {before after : State Symbol Guard} : Path before after → List (Publication (Symbol := Symbol) (Guard := Guard))
  | .refl _ | .retain _ _ _ _ _ => []
  | .trans first next => events first ++ events next
  | .publication event depth ordinary body => events depth ++ events ordinary ++ events body ++ [event]

section
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

private def WrittenIn (all : List (@Publication Symbol Guard _))
    (before after : State Symbol Guard) (key : NodeKey) (value : Value Symbol Guard) : Prop :=
  ∃ i : Nat, ∃ event : @Publication Symbol Guard _, all[i]? = some event ∧ key = event.key ∧ value = event.candidate ∧
    event.afterBody.nodeRecords event.key = none ∧
    Nonempty (Path before event.before) ∧
    Nonempty (Path event.before event.afterDepth) ∧
    Nonempty (Path event.afterDepth event.cut) ∧
    Nonempty (Path event.allocated event.afterBody) ∧
    Grows event.after after ∧ Extends event.after.nodes.issued after.nodes.issued

private theorem written_append {all : List (@Publication Symbol Guard _)}
    {before middle after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (written : WrittenIn all before middle key value) (tail : List (@Publication Symbol Guard _))
    (growth : Grows middle after) (issued : Extends middle.nodes.issued after.nodes.issued) :
    WrittenIn (all ++ tail) before after key value := by
  obtain ⟨i,event,found,keySame,valueSame,missing,earlier,depth,ordinary,body,oldGrowth,oldIssued⟩ := written
  have bounded := (List.getElem?_eq_some_iff.mp found).1
  exact ⟨i,event,(List.getElem?_append_left bounded).trans found,keySame,valueSame,missing,
    earlier,depth,ordinary,body,grows_trans oldGrowth growth,extends_trans oldIssued issued⟩

private theorem written_prepend {all : List (@Publication Symbol Guard _)}
    {before middle after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (earlierPath : Path before middle) (written : WrittenIn all middle after key value) :
    WrittenIn (events earlierPath ++ all) before after key value := by
  obtain ⟨i,event,found,keySame,valueSame,missing,⟨earlier⟩,depth,ordinary,body,growth,issued⟩ := written
  refine ⟨(events earlierPath).length + i,event,?_,keySame,valueSame,missing,
    ⟨.trans earlierPath earlier⟩,depth,ordinary,body,growth,issued⟩
  simpa only [List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left] using found

private theorem reserve_issued (event : @Publication Symbol Guard _) :
    Extends event.cut.nodes.issued event.allocated.nodes.issued := by
  have context := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  exact InternedFreshProbeKeys.intern_issued_extends event.cut.nodes event.key context.base.normal.facts.coherent.valid.2

private def reserve_path (event : @Publication Symbol Guard _) : Path event.cut event.allocated :=
  .retain _ _ (fun _ _ _ _ _ present => present) (reserve_growth event) (reserve_issued event)

private theorem writers_in {before after : State Symbol Guard}
    (path : Path before after) (key : NodeKey) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : after.nodeRecords key = some (.mu entry body depth ordinary)) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
      WrittenIn (events path) before after key (.mu entry body depth ordinary) := by
  induction path with
  | refl => exact .inl present
  | retain before after old _growth _issued => exact .inl (old key entry body depth ordinary present)
  | trans first next firstIH nextIH =>
      rcases nextIH present with old | written
      · rcases firstIH old with initial | written
        · exact .inl initial
        · exact .inr (written_append written (events next) next.growth next.issued)
      · exact .inr (written_prepend first written)
  | publication event depthPath ordinaryPath bodyPath depthIH ordinaryIH bodyIH =>
      have cutGrowth : Grows event.cut event.after :=
        grows_trans (reserve_growth event) (grows_trans bodyPath.growth (publication_growth event))
      have depthGrowth : Grows event.afterDepth event.after := grows_trans ordinaryPath.growth cutGrowth
      have cutIssued : Extends event.cut.nodes.issued event.after.nodes.issued :=
        extends_trans (reserve_issued event) bodyPath.issued
      have depthIssued : Extends event.afterDepth.nodes.issued event.after.nodes.issued :=
        extends_trans ordinaryPath.issued cutIssued
      have prior (old : event.afterBody.nodeRecords key = some (.mu entry body depth ordinary)) :
          event.before.nodeRecords key = some (.mu entry body depth ordinary) ∨
            WrittenIn (events (.publication event depthPath ordinaryPath bodyPath))
              event.before event.after key (.mu entry body depth ordinary) := by
        rcases bodyIH old with allocated | written
        · rcases ordinaryIH allocated with afterDepth | written
          · rcases depthIH afterDepth with initial | written
            · exact .inl initial
            · exact .inr (by simpa only [events,List.append_assoc] using
                written_append written (events ordinaryPath ++ events bodyPath ++ [event]) depthGrowth depthIssued)
          · have later := written_append written (events bodyPath ++ [event]) cutGrowth cutIssued
            exact .inr (by simpa only [events,List.append_assoc] using written_prepend depthPath later)
        · have later := written_append written [event] (publication_growth event) (extends_refl _)
          have joined := written_prepend (.trans depthPath (.trans ordinaryPath (reserve_path event))) later
          exact .inr (by simpa only [reserve_path,events,List.nil_append,List.append_assoc] using joined)
      rcases record_cases event.afterBody.nodeRecords event.key key event.candidate
        (.mu entry body depth ordinary) present with old | ⟨sameKey,sameValue⟩
      · exact prior old
      · cases firstWrite : event.afterBody.nodeRecords event.key with
        | none =>
            refine .inr ⟨(events depthPath).length + (events ordinaryPath).length + (events bodyPath).length,
              event,?_,sameKey,sameValue,firstWrite,⟨.refl _⟩,⟨depthPath⟩,⟨ordinaryPath⟩,⟨bodyPath⟩,
              grows_refl _,extends_refl _⟩
            simpa only [events,List.length_append] using
              (List.getElem?_concat_length (l := events depthPath ++ events ordinaryPath ++ events bodyPath) (a := event))
        | some previous =>
            apply prior
            change keepFirst event.afterBody.nodeRecords event.key event.candidate key =
              some (.mu entry body depth ordinary) at present
            simpa only [keepFirst,firstWrite] using present

private theorem indexed_writers {before after : State Symbol Guard}
    (path : Path before after) (key : NodeKey) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : after.nodeRecords key = some (.mu entry body depth ordinary)) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
      ∃ i : Nat, ∃ event : @Publication Symbol Guard _, (events path)[i]? = some event ∧ key = event.key ∧
        Value.mu entry body depth ordinary = event.candidate ∧ event.afterBody.nodeRecords event.key = none ∧
        Nonempty (Path before event.before) ∧ Nonempty (Path event.before event.afterDepth) ∧
        Nonempty (Path event.afterDepth event.cut) ∧ Nonempty (Path event.allocated event.afterBody) ∧
        Grows event.after after ∧ Extends event.after.nodes.issued after.nodes.issued :=
  writers_in path key entry body depth ordinary present

private theorem before_publication {before after : State Symbol Guard} (path : Path before after)
    (j : Nat) (outer : @Publication Symbol Guard _) (found : (events path)[j]? = some outer) :
    ∃ earlierPath : Path before outer.afterBody, ∃ tail : List (@Publication Symbol Guard _),
      events path = events earlierPath ++ tail ∧ (events earlierPath).length = j := by
  induction path generalizing j outer with
  | refl | retain => simp only [events,List.getElem?_nil] at found; cases found
  | trans first next firstIH nextIH =>
      by_cases left : j < (events first).length
      · have chosen : (events first)[j]? = some outer := by
          simpa only [events,List.getElem?_append_left left] using found
        obtain ⟨earlierPath,tail,same,length⟩ := firstIH j outer chosen
        exact ⟨earlierPath,tail ++ events next,by simp only [events,same,List.append_assoc],length⟩
      · have chosen : (events next)[j - (events first).length]? = some outer := by
          simpa only [events,List.getElem?_append_right (l₁ := events first) (l₂ := events next) (i := j) (by omega)] using found
        obtain ⟨earlierPath,tail,same,length⟩ := nextIH _ outer chosen
        refine ⟨.trans first earlierPath,tail,?_,?_⟩
        · simp only [events,same,List.append_assoc]
        · simp only [events,List.length_append]
          omega
  | publication event depthPath ordinaryPath bodyPath depthIH ordinaryIH bodyIH =>
      by_cases inDepth : j < (events depthPath).length
      · have chosen : (events depthPath)[j]? = some outer := by
          simpa only [events,List.append_assoc,List.getElem?_append_left inDepth] using found
        obtain ⟨earlierPath,tail,same,length⟩ := depthIH j outer chosen
        exact ⟨earlierPath,tail ++ events ordinaryPath ++ events bodyPath ++ [event],
          by simp only [events,same,List.append_assoc],length⟩
      · have afterDepth : (events ordinaryPath ++ events bodyPath ++ [event])[j - (events depthPath).length]? = some outer := by
          simpa only [events,List.append_assoc,List.getElem?_append_right (l₁ := events depthPath) (l₂ := events ordinaryPath ++ (events bodyPath ++ [event])) (i := j) (by omega)] using found
        by_cases inOrdinary : j - (events depthPath).length < (events ordinaryPath).length
        · have chosen : (events ordinaryPath)[j - (events depthPath).length]? = some outer := by
            simpa only [List.append_assoc,List.getElem?_append_left inOrdinary] using afterDepth
          obtain ⟨earlierPath,tail,same,length⟩ := ordinaryIH _ outer chosen
          refine ⟨.trans depthPath earlierPath,tail ++ events bodyPath ++ [event],?_,?_⟩
          · simp only [events,same,List.append_assoc]
          · simp only [events,List.length_append]
            omega
        · have afterOrdinary : (events bodyPath ++ [event])[j - (events depthPath).length - (events ordinaryPath).length]? = some outer := by
            simpa only [List.append_assoc,List.getElem?_append_right (l₁ := events ordinaryPath) (l₂ := events bodyPath ++ [event]) (i := j - (events depthPath).length) (by omega)] using afterDepth
          by_cases inBody : j - (events depthPath).length - (events ordinaryPath).length < (events bodyPath).length
          · have chosen : (events bodyPath)[j - (events depthPath).length - (events ordinaryPath).length]? = some outer := by
              simpa only [List.append_assoc,List.getElem?_append_left inBody] using afterOrdinary
            obtain ⟨earlierPath,tail,same,length⟩ := bodyIH _ outer chosen
            refine ⟨.trans depthPath (.trans ordinaryPath (.trans (reserve_path event) earlierPath)),tail ++ [event],?_,?_⟩
            · simp only [events,reserve_path,same,List.nil_append,List.append_assoc]
            · simp only [events,reserve_path,List.length_append,List.length_nil]
              omega
          · have last : ([event] : List (@Publication Symbol Guard _))[j - (events depthPath).length -
                (events ordinaryPath).length - (events bodyPath).length]? = some outer := by
                simpa only [List.getElem?_append_right (l₁ := events bodyPath) (l₂ := [event]) (i := j - (events depthPath).length - (events ordinaryPath).length) (by omega)] using afterOrdinary
            have bounded := (List.getElem?_eq_some_iff.mp last).1
            have zero : j - (events depthPath).length - (events ordinaryPath).length - (events bodyPath).length = 0 := by
              simp only [List.length_singleton] at bounded
              omega
            have sameEvent : event = outer := by simpa only [zero,List.getElem?_cons_zero,Option.some.injEq] using last
            subst outer
            refine ⟨.trans depthPath (.trans ordinaryPath (.trans (reserve_path event) bodyPath)),[event],?_,?_⟩
            · simp only [events,reserve_path,List.nil_append,List.append_assoc]
            · simp only [events,reserve_path,List.length_append,List.length_nil]
              omega

private theorem precompletion_writers {before after : State Symbol Guard}
    (path : Path before after) (j : Nat) (outer : @Publication Symbol Guard _)
    (found : (events path)[j]? = some outer)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : outer.afterBody.nodeRecords key = some (.mu entry body depth ordinary)) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
      ∃ i : Nat, ∃ earlier : @Publication Symbol Guard _, i < j ∧ (events path)[i]? = some earlier ∧ key = earlier.key ∧
        Value.mu entry body depth ordinary = earlier.candidate ∧ earlier.afterBody.nodeRecords earlier.key = none ∧
        Nonempty (Path before earlier.before) ∧ Nonempty (Path earlier.before earlier.afterDepth) ∧
        Nonempty (Path earlier.afterDepth earlier.cut) ∧ Nonempty (Path earlier.allocated earlier.afterBody) ∧
        Grows earlier.after outer.afterBody ∧ Extends earlier.after.nodes.issued outer.afterBody.nodes.issued := by
  obtain ⟨earlierPath,tail,same,length⟩ := before_publication path j outer found
  rcases indexed_writers earlierPath key entry body depth ordinary present with initial | written
  · exact .inl initial
  · obtain ⟨i,earlier,chosen,rest⟩ := written
    have bounded := (List.getElem?_eq_some_iff.mp chosen).1
    refine .inr ⟨i,earlier,by omega,?_,rest⟩
    rw [same,List.getElem?_append_left bounded]
    exact chosen

end

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

private theorem rooted_event [DecidableEq (EdgeKey Symbol Guard)]
    {root : Syntax Symbol Guard} {initial : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (path : Path before after)
    (rooted : Rooted root initial path) (event : Publication (Symbol := Symbol) (Guard := Guard))
    (member : event ∈ events path) :
    Reached root initial (.binder event.smart event.expression) event.environment event.before := by
  induction path with
  | refl => simp only [events,List.not_mem_nil] at member
  | retain => simp only [events,List.not_mem_nil] at member
  | trans first next left right =>
    obtain ⟨firstRoot,nextRoot⟩ := rooted
    rcases List.mem_append.mp member with firstMember | nextMember
    · exact left firstRoot firstMember
    · exact right nextRoot nextMember
  | publication selected depth ordinary body first second last =>
    obtain ⟨site,depthRoot,ordinaryRoot,bodyRoot⟩ := rooted
    simp only [events,List.mem_append,List.mem_singleton] at member
    rcases member with ((depthMember | ordinaryMember) | bodyMember) | same
    · exact first depthRoot depthMember
    · exact second ordinaryRoot ordinaryMember
    · exact last bodyRoot bodyMember
    · subst event
      exact site


/-- One actual rooted path orders every final writer and every writer present before another completion. -/
theorem build_trace_writers [DecidableEq (EdgeKey Symbol Guard)]
    (original : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    (before : State Symbol Guard) (context : Context before initial)
    (initialMuFree : ∀ key entry body depth ordinary,
      before.nodeRecords key ≠ some (.mu entry body depth ordinary))
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : build original initial before = .done result after) :
    ∃ path : Path before after,
      (∀ (index : Nat) event, (events path)[index]? = some event →
        Reached original initial (.binder event.smart event.expression) event.environment event.before) ∧
      (∀ key entry body depth ordinary,
        after.nodeRecords key = some (.mu entry body depth ordinary) →
        ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
          Reached original initial (.binder event.smart event.expression) event.environment event.before ∧
          key = event.key ∧ Value.mu entry body depth ordinary = event.candidate ∧
          event.afterBody.nodeRecords event.key = none ∧
          Nonempty (Path before event.before) ∧
          Nonempty (Path event.before event.afterDepth) ∧
          Nonempty (Path event.afterDepth event.cut) ∧
          Nonempty (Path event.allocated event.afterBody) ∧
          Grows event.after after ∧ Extends event.after.nodes.issued after.nodes.issued) ∧
      ∀ (index : Nat) outer, (events path)[index]? = some outer →
        ∀ key entry body depth ordinary,
          outer.afterBody.nodeRecords key = some (.mu entry body depth ordinary) →
          ∃ earlierIndex : Nat, ∃ earlier, earlierIndex < index ∧ (events path)[earlierIndex]? = some earlier ∧
            Reached original initial (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
            key = earlier.key ∧ Value.mu entry body depth ordinary = earlier.candidate ∧
            earlier.afterBody.nodeRecords earlier.key = none ∧
            Nonempty (Path before earlier.before) ∧
            Nonempty (Path earlier.before earlier.afterDepth) ∧
            Nonempty (Path earlier.afterDepth earlier.cut) ∧
            Nonempty (Path earlier.allocated earlier.afterBody) ∧
            Grows earlier.after outer.afterBody ∧
            Extends earlier.after.nodes.issued outer.afterBody.nodes.issued := by
  have supported := build_supported original initial original initial before context
    (reached_initial original initial before)
  rw [actual] at supported
  obtain ⟨path,rooted⟩ := supported
  refine ⟨path,?_,?_,?_⟩
  · intro index event selected
    exact rooted_event path rooted event (List.mem_of_getElem? selected)
  · intro key entry body depth ordinary present
    rcases indexed_writers path key entry body depth ordinary present with old | written
    · exact (initialMuFree key entry body depth ordinary old).elim
    · obtain ⟨index,event,selected,keySame,valueSame,missing,prefixPath,depthPath,ordinaryPath,bodyPath,growth,issued⟩ := written
      exact ⟨index,event,selected,rooted_event path rooted event (List.mem_of_getElem? selected),
        keySame,valueSame,missing,prefixPath,depthPath,ordinaryPath,bodyPath,growth,issued⟩
  · intro index outer selected key entry body depth ordinary present
    rcases precompletion_writers path index outer selected key entry body depth ordinary present with old | written
    · exact (initialMuFree key entry body depth ordinary old).elim
    · obtain ⟨earlierIndex,earlier,less,chosen,keySame,valueSame,missing,prefixPath,
        depthPath,ordinaryPath,bodyPath,growth,issued⟩ := written
      exact ⟨earlierIndex,earlier,less,chosen,rooted_event path rooted earlier (List.mem_of_getElem? chosen),
        keySame,valueSame,missing,prefixPath,depthPath,ordinaryPath,bodyPath,growth,issued⟩

end MicroCFTA.SourceCurrentNativeOriginalPublicationTrace

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000

#check @MicroCFTA.SourceCurrentNativeOriginalPublicationTrace.events
#print MicroCFTA.SourceCurrentNativeOriginalPublicationTrace.events
#print axioms MicroCFTA.SourceCurrentNativeOriginalPublicationTrace.events

#check @MicroCFTA.SourceCurrentNativeOriginalPublicationTrace.build_trace_writers
#print MicroCFTA.SourceCurrentNativeOriginalPublicationTrace.build_trace_writers
#print axioms MicroCFTA.SourceCurrentNativeOriginalPublicationTrace.build_trace_writers
