import MicroCFTA.InternedNestedCoherence
import MicroCFTA.InternedNestedSpecialization

/-!
# Erased outer dependencies around arbitrary nested live source children

The live children can contain arbitrary nested binders. Their source input
slots exclude the changed outer variable. Their actual earlier successful
trace supplies replay. The discarded edge still performs its exact cache
effects before the original completed parent record is read back.
-/
namespace MicroCFTA.InternedNestedErasureReplay
open Cache InternedConstructorTemplates InternedRecordCoherence InternedNestedConstruction
open InternedNestedDependencies InternedNestedSpecialization InternedNestedCoherence InternedErasedEdgeReplay
open InternedBinderProtocol (Reference)

/-- Source sequencing has the ordinary associative law at both possible outcomes. -/
theorem bind_assoc (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Second)
    (last : Second → State Symbol Guard → Outcome Symbol Guard Result) :
    (outcome.bind next).bind last = outcome.bind (fun value state => (next value state).bind last) := by
  cases outcome <;> rfl

/-- Appended source edges execute after all actual effects of the earlier edge list. -/
theorem buildEdges_append [DecidableEq (EdgeKey Symbol Guard)] (left right : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    buildEdges (left ++ right) environment state = (buildEdges left environment state).bind fun earlier middle =>
      (buildEdges right environment middle).bind fun later final => .done (earlier ++ later) final := by
  induction left generalizing state with
  | nil =>
      simp only [List.nil_append, buildEdges, Outcome.bind]
      cases buildEdges right environment state <;> rfl
  | cons first rest ih =>
      cases first with
      | mk symbol constraint children =>
          simp only [List.cons_append, buildEdges, bind_assoc]
          congr 1
          funext values after
          congr 1
          funext edge afterEdge
          rw [ih]
          simp only [bind_assoc]
          congr 1

/-- The body retains arbitrary live source edges and appends the exact outer-dependent dead edge. -/
def body (live : List (EdgeSyntax Symbol Guard)) (symbol : Symbol) (constraint : Guard) : Syntax Symbol Guard :=
  .node (live ++ [.mk symbol constraint [.var 1, .empty]])

/-- The normalized body callback uses the actual source self-reference filter. -/
def callback [DecidableEq (EdgeKey Symbol Guard)] (live : List (EdgeSyntax Symbol Guard))
    (symbol : Symbol) (constraint : Guard) (outer : Value Symbol Guard) (captures : List (Value Symbol Guard))
    (name : Reference) (state : State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) :=
  (build (body live symbol constraint) (.reference name :: outer :: captures) state).bind fun value after =>
    work (withoutSelfReference name value) after

/-- The source callback evaluates live children before the discarded edge and the parent node. -/
theorem callback_effects [DecidableEq (EdgeKey Symbol Guard)] (live : List (EdgeSyntax Symbol Guard))
    (symbol : Symbol) (constraint : Guard) (outer : Value Symbol Guard) (captures : List (Value Symbol Guard))
    (name : Reference) (state : State Symbol Guard) :
    callback live symbol constraint outer captures name state =
      (buildEdges live (.reference name :: outer :: captures) state).bind fun edges middle =>
        (work (makeEdge symbol constraint [outer, .empty]) middle).bind fun dead afterDead =>
          (work (makeNode (edges ++ [dead])) afterDead).bind fun value afterNode =>
            work (withoutSelfReference name value) afterNode := by
  simp only [callback, body, build, buildEdges_append, buildEdges, buildMany, Outcome.bind,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  cases buildEdges live (.reference name :: outer :: captures) state <;> rfl

/-- Changing the discarded edge leaves an actual completed callback as ordinary edge work followed by exact record reuse. -/
theorem callback_residual [DecidableEq (EdgeKey Symbol Guard)] (live : List (EdgeSyntax Symbol Guard))
    (unused : 1 ∉ edgeInputs live) (symbol : Symbol) (constraint : Guard)
    (oldOuter newOuter : Value Symbol Guard) (captures : List (Value Symbol Guard)) (name : Reference)
    (before after : State Symbol Guard) (value : Value Symbol Guard) (final : State Symbol Guard)
    (coherentBefore : Coherent before) (coherentAfter : Coherent after)
    (completed : callback live symbol constraint oldOuter captures name before = .done value final)
    (growth : Grows final after) :
    callback live symbol constraint newOuter captures name after =
      work ((makeEdge symbol constraint [newOuter, .empty]).bind fun _ => .pure value) after := by
  rw [callback_effects] at completed
  obtain ⟨edges, middle, edgesDone, restDone⟩ := bind_done _ _ _ _ completed
  have edgesFacts := buildEdges_correct live (.reference name :: oldOuter :: captures) before coherentBefore.valid
  rw [edgesDone] at edgesFacts
  have middleCoherent : Coherent middle := by
    simpa only [edgesDone, Outcome.state] using buildEdges_coherent live (.reference name :: oldOuter :: captures) before coherentBefore
  let oldDead := run (makeEdge symbol constraint [oldOuter, .empty]) middle
  let newDead := run (makeEdge symbol constraint [newOuter, .empty]) after
  have oldDeadCorrect := InternedConstructorTemplates.run_correct (makeEdge symbol constraint [oldOuter, .empty]) middle middleCoherent.valid
  have newDeadCorrect := InternedConstructorTemplates.run_correct (makeEdge symbol constraint [newOuter, .empty]) after coherentAfter.valid
  have oldErased : makeNode (edges ++ [oldDead.1]) = makeNode edges := by
    apply makeNode_erases
    rw [makeEdge_references symbol constraint [oldOuter, .empty] middle middleCoherent]
    simp [Value.referenceOf]
  have newErased : makeNode (edges ++ [newDead.1]) = makeNode edges := by
    apply makeNode_erases
    rw [makeEdge_references symbol constraint [newOuter, .empty] after coherentAfter]
    simp [Value.referenceOf]
  let parent := (makeNode edges).bind (withoutSelfReference name)
  have parentDone : work parent oldDead.2 = .done value final := by
    simp only [work, Outcome.bind] at restDone
    rw [oldErased] at restDone
    simpa only [work, parent, run_bind] using restDone
  have parentCorrect := work_correct parent oldDead.2 oldDeadCorrect.1
  rw [parentDone] at parentCorrect
  have edgesReplay := buildEdges_replays live (.reference name :: oldOuter :: captures) before after edges middle
    coherentBefore.valid edgesDone (grows_trans oldDeadCorrect.2 (grows_trans parentCorrect.2 growth))
  have agree : Agree (edgeInputs live) (.reference name :: oldOuter :: captures) (.reference name :: newOuter :: captures) := by
    intro index member
    cases index with
    | zero => rfl
    | succ index => cases index with
      | zero => exact False.elim (unused member)
      | succ index => rfl
  rw [buildEdges_congr live _ _ after agree] at edgesReplay
  have parentReplay := work_replays parent oldDead.2 newDead.2 value final oldDeadCorrect.1 parentDone
    (grows_trans growth newDeadCorrect.2)
  rw [callback_effects, edgesReplay]
  simp only [work, Outcome.bind, run_bind]
  rw [newErased]
  simpa only [work, parent, run_bind, run] using parentReplay


/-- Completed source requests keep their record available even if the later callback is different. -/
theorem request_after_done [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (depth ordinary : Value Symbol Guard)
    (oldCallback newCallback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (before after : State Symbol Guard) (value : Value Symbol Guard) (final : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before)
    (growing : ∀ name, Growing (oldCallback name))
    (completed : request smart depth ordinary oldCallback before = .done value final)
    (growth : Grows final after) : request smart depth ordinary newCallback after = .done value after := by
  cases installed : before.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases stored : before.nodeRecords (muKey depth ordinary) with
      | none => simp [request, installed, stored] at completed
      | some record =>
          simp only [request, installed, stored, Outcome.done.injEq] at completed
          obtain ⟨rfl, rfl⟩ := completed
          simp only [request, growth.nodes _ _ installed, growth.nodeRecords _ _ stored]
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern before.nodes key
      let allocated := {before with nodes := entry.2}
      simp only [request, installed] at completed
      change (oldCallback (.interned entry.1.identity) allocated).bind _ = .done value final at completed
      obtain ⟨body, afterBody, bodyDone, completed⟩ := bind_done _ _ _ _ completed
      have allocatedValid : InternedConstructorTemplates.Valid allocated :=
        ⟨valid.1, (Cache.intern_correct before.nodes key valid.2).1⟩
      have bodyGrowth := (growing (.interned entry.1.identity) allocated allocatedValid).2
      rw [bodyDone] at bodyGrowth
      have present := bodyGrowth.nodes key entry.1 (Cache.intern_correct before.nodes key valid.2).2.1
      let candidate := Value.mu entry.1 body depth ordinary
      obtain ⟨record, stored⟩ := keepFirst_present afterBody.nodeRecords key candidate
      change Outcome.done (finish smart ((keepFirst afterBody.nodeRecords key candidate key).getD candidate))
        {afterBody with nodeRecords := keepFirst afterBody.nodeRecords key candidate} = Outcome.done value final at completed
      rw [stored] at completed
      simp only [Option.getD_some, Outcome.done.injEq] at completed
      obtain ⟨rfl, rfl⟩ := completed
      have laterEntry := growth.nodes key entry.1 present
      have laterRecord := growth.nodeRecords key record stored
      change after.nodes.table (muKey depth ordinary) = some entry.1 at laterEntry
      change after.nodeRecords (muKey depth ordinary) = some record at laterRecord
      simp only [request, laterEntry, laterRecord]

/-- Later erased-dependent calls execute both actual discarded-edge requests before returning the earlier record. -/
def replayWork (symbol : Symbol) (constraint : Guard) (outer value : Value Symbol Guard) : Work Symbol Guard (Value Symbol Guard) :=
  (makeEdge symbol constraint [outer, .empty]).bind fun _ =>
    (makeEdge symbol constraint [outer, .empty]).bind fun _ => .pure value

/-- The changed discarded edge performs only safe ordinary constructor effects. -/
theorem replayWork_safe (symbol : Symbol) (constraint : Guard) (outer value : Value Symbol Guard) :
    Safe (replayWork symbol constraint outer value) ∧ Ordinary (replayWork symbol constraint outer value) := by
  constructor
  · exact safe_bind _ _ (makeEdge_safe _ _ _) (fun _ => safe_bind _ _ (makeEdge_safe _ _ _) (fun _ => trivial))
  · exact ordinary_bind _ _ (by simp [makeEdge, Ordinary])
      (fun _ => ordinary_bind _ _ (by simp [makeEdge, Ordinary]) (fun _ => trivial))

/-- Arbitrarily nested live children reuse an actual earlier complete binder when only its discarded outer edge changes. -/
theorem binder_residual [DecidableEq (EdgeKey Symbol Guard)] (live : List (EdgeSyntax Symbol Guard))
    (unused : 1 ∉ edgeInputs live) (symbol : Symbol) (constraint : Guard) (smart : Bool)
    (oldOuter newOuter : Value Symbol Guard) (captures : List (Value Symbol Guard))
    (before after : State Symbol Guard) (value : Value Symbol Guard) (final : State Symbol Guard)
    (coherentBefore : Coherent before) (coherentAfter : Coherent after)
    (completed : build (.binder smart (body live symbol constraint)) (oldOuter :: captures) before = .done value final)
    (growth : Grows final after) :
    build (.binder smart (body live symbol constraint)) (newOuter :: captures) after =
      work (replayWork symbol constraint newOuter value) after := by
  have growing : ∀ outer name, Growing (callback live symbol constraint outer captures name) := by
    intro outer name state valid
    exact bind_correct _ _ state (build_correct (body live symbol constraint) _ state valid)
      (fun value after afterValid => work_correct (withoutSelfReference name value) after afterValid)
  rw [build] at completed
  change (callback live symbol constraint oldOuter captures .depth before).bind
    (fun depth afterDepth => (callback live symbol constraint oldOuter captures (.uninterned depth.depth) afterDepth).bind
      fun ordinary afterOrdinary => request smart depth ordinary (callback live symbol constraint oldOuter captures) afterOrdinary) =
        .done value final at completed
  obtain ⟨depth, afterDepth, depthDone, remaining⟩ := bind_done _ _ _ _ completed
  have depthCorrect := growing oldOuter .depth before coherentBefore.valid
  rw [depthDone] at depthCorrect
  have depthCoherent : Coherent afterDepth := by
    have coherent := bind_coherent (build (body live symbol constraint) (.reference .depth :: oldOuter :: captures) before)
      (fun value after => work (withoutSelfReference .depth value) after)
      (build_coherent (body live symbol constraint) _ before coherentBefore)
      (fun value after _ current => run_coherent (withoutSelfReference .depth value) after (withoutSelfReference_safe _ _) current)
    change Coherent (callback live symbol constraint oldOuter captures .depth before).state at coherent
    simpa only [depthDone, Outcome.state] using coherent
  obtain ⟨ordinary, afterOrdinary, ordinaryDone, requestDone⟩ := bind_done _ _ _ _ remaining
  have ordinaryCorrect := growing oldOuter (.uninterned depth.depth) afterDepth depthCorrect.1
  rw [ordinaryDone] at ordinaryCorrect
  have requestCorrect := request_correct smart depth ordinary (callback live symbol constraint oldOuter captures)
    (growing oldOuter) afterOrdinary ordinaryCorrect.1
  rw [requestDone] at requestCorrect
  have depthReplay := callback_residual live unused symbol constraint oldOuter newOuter captures .depth before after depth afterDepth
    coherentBefore coherentAfter depthDone (grows_trans ordinaryCorrect.2 (grows_trans requestCorrect.2 growth))
  let first := run (makeEdge symbol constraint [newOuter, .empty]) after
  have firstCoherent := run_coherent (makeEdge symbol constraint [newOuter, .empty]) after (makeEdge_safe _ _ _) coherentAfter
  have firstGrowth := (InternedConstructorTemplates.run_correct (makeEdge symbol constraint [newOuter, .empty]) after coherentAfter.valid).2
  have ordinaryReplay := callback_residual live unused symbol constraint oldOuter newOuter captures (.uninterned depth.depth)
    afterDepth first.2 ordinary afterOrdinary depthCoherent firstCoherent ordinaryDone
      (grows_trans requestCorrect.2 (grows_trans growth firstGrowth))
  let second := run (makeEdge symbol constraint [newOuter, .empty]) first.2
  have secondGrowth := (InternedConstructorTemplates.run_correct (makeEdge symbol constraint [newOuter, .empty]) first.2 firstCoherent.valid).2
  have readback := request_after_done smart depth ordinary (callback live symbol constraint oldOuter captures)
    (callback live symbol constraint newOuter captures) afterOrdinary second.2 value final ordinaryCorrect.1
    (growing oldOuter) requestDone (grows_trans growth (grows_trans firstGrowth secondGrowth))
  have firstDone : callback live symbol constraint newOuter captures .depth after = .done depth first.2 := by
    simpa only [work, run_bind, run] using depthReplay
  have secondDone : callback live symbol constraint newOuter captures (.uninterned depth.depth) first.2 = .done ordinary second.2 := by
    simpa only [work, run_bind, run] using ordinaryReplay
  rw [build]
  change (callback live symbol constraint newOuter captures .depth after).bind
    (fun depth afterDepth => (callback live symbol constraint newOuter captures (.uninterned depth.depth) afterDepth).bind
      fun ordinary afterOrdinary => request smart depth ordinary (callback live symbol constraint newOuter captures) afterOrdinary) = _
  rw [firstDone]
  simp only [Outcome.bind]
  rw [secondDone]
  dsimp only
  rw [readback]
  simp only [work, replayWork, run_bind, run]
  rfl

end MicroCFTA.InternedNestedErasureReplay
