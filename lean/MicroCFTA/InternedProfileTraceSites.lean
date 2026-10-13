import MicroCFTA.InternedNestedCoherentSites
import MicroCFTA.InternedNestedProfiles

/-!
# Completed source sites retain their verified profile prefix

Every syntactic descendant runs during a completed enclosing trace.
The witness retains actual input availability, source normalization facts,
and the decoded profile table at its original starting point. It follows
the unconditional depth-body call at every crossed binder.
-/
namespace MicroCFTA.InternedProfileTraceSites
open InternedConstructorTemplates InternedNestedConstruction InternedNestedSpecialization InternedNestedTraceSites
open InternedStoredMuOrigins InternedNestedProvenance InternedProbeProvenance InternedNestedMuOrigins InternedNestedProfiles

/-- A source trace prefix retains the inputs and both independent constructor invariants. -/
structure Context (state : State Symbol Guard) (environment : List (Value Symbol Guard)) : Prop where
  normal : Normal state
  inputs : Values state environment
  heap : InternedProfileHeap.Heap state

/-- Full source evaluation retains each original lexical input and both cache invariants. -/
theorem Context.build [DecidableEq (EdgeKey Symbol Guard)] (context : Context state environment) (expression : Syntax Symbol Guard) :
    Context (build expression environment state).state environment :=
  ⟨build_normal expression environment state context.normal context.inputs,
    fun value member => (build_verified expression environment state context.normal.facts context.inputs).available value (context.inputs value member),
    (build_profile expression environment state context.normal context.inputs context.heap).heap⟩

/-- Ordered source children retain their original input context. -/
theorem Context.many [DecidableEq (EdgeKey Symbol Guard)] (context : Context state environment) (expressions : List (Syntax Symbol Guard)) :
    Context (buildMany expressions environment state).state environment :=
  ⟨buildMany_normal expressions environment state context.normal context.inputs,
    fun value member => (buildMany_verified expressions environment state context.normal.facts context.inputs).available value (context.inputs value member),
    (buildMany_profile expressions environment state context.normal context.inputs context.heap).heap⟩

/-- Edge allocation changes no recursive profile payload. -/
theorem Context.edge [DecidableEq (EdgeKey Symbol Guard)] (context : Context state environment)
    (symbol : Symbol) (constraint : Guard) (values : List (Value Symbol Guard)) (inputs : Values state values) :
    Context (run (makeEdge symbol constraint values) state).2 environment :=
  ⟨edge_normal symbol constraint values state context.normal inputs,
    fun value member => available_after_run (makeEdge symbol constraint values) state context.normal.facts.coherent.valid (context.inputs value member),
    context.heap⟩

/-- The unconditional depth body introduces one available source sentinel. -/
theorem Context.depth (context : Context state environment) : Context state (.reference .depth :: environment) := by
  refine ⟨context.normal, ?_, context.heap⟩
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact depth_available state
  · exact context.inputs value member

/-- Each member of a completed child list has an actual earlier complete execution with preserved cache order. -/
theorem buildMany_member_checked [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (values : List (Value Symbol Guard)) (final : State Symbol Guard)
    (context : Context before environment)
    (completed : buildMany expressions environment before = .done values final)
    (selected : Syntax Symbol Guard) (member : selected ∈ expressions) :
    ∃ start value finish, build selected environment start = .done value finish ∧
      Context start environment ∧ Grows before start ∧ Grows finish final := by
  cases expressions with
  | nil => cases member
  | cons first rest =>
      simp only [buildMany] at completed
      obtain ⟨head, middle, firstDone, later⟩ := bind_done _ _ _ _ completed
      obtain ⟨tail, last, tailDone, assembled⟩ := bind_done _ _ _ _ later
      simp only [Outcome.done.injEq] at assembled
      obtain ⟨rfl, rfl⟩ := assembled
      have headFacts := build_correct first environment before context.normal.facts.coherent.valid
      rw [firstDone] at headFacts
      have headContext : Context middle environment := by
        simpa only [firstDone, Outcome.state] using context.build first
      have tailFacts := buildMany_correct rest environment middle headFacts.1
      rw [tailDone] at tailFacts
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨before, head, middle, firstDone, context, grows_refl _, tailFacts.2⟩
      · obtain ⟨start, value, finish, selectedDone, startValid, initialGrowth, suffix⟩ :=
          buildMany_member_checked rest environment middle tail last headContext tailDone selected inRest
        exact ⟨start, value, finish, selectedDone, startValid, grows_trans headFacts.2 initialGrowth, suffix⟩
termination_by expressions.length

/-- Every source edge child completes before edge interning and later edge computations. -/
theorem buildEdges_member_checked [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (values : List (EdgeValue Symbol Guard)) (final : State Symbol Guard)
    (context : Context before environment)
    (completed : buildEdges expressions environment before = .done values final)
    (symbol : Symbol) (constraint : Guard) (children : List (Syntax Symbol Guard))
    (edge : .mk symbol constraint children ∈ expressions) (selected : Syntax Symbol Guard) (member : selected ∈ children) :
    ∃ start value finish, build selected environment start = .done value finish ∧
      Context start environment ∧ Grows before start ∧ Grows finish final := by
  cases expressions with
  | nil => cases edge
  | cons first rest =>
      cases first with
      | mk own guard ownChildren =>
          simp only [buildEdges] at completed
          obtain ⟨childValues, middle, childrenDone, later⟩ := bind_done _ _ _ _ completed
          obtain ⟨builtEdge, afterEdge, edgeDone, afterEdgeDone⟩ := bind_done _ _ _ _ later
          obtain ⟨tail, last, tailDone, assembled⟩ := bind_done _ _ _ _ afterEdgeDone
          simp only [Outcome.done.injEq] at assembled
          obtain ⟨rfl, rfl⟩ := assembled
          have childrenFacts := buildMany_correct ownChildren environment before context.normal.facts.coherent.valid
          rw [childrenDone] at childrenFacts
          have childrenContext : Context middle environment := by
            simpa only [childrenDone, Outcome.state] using context.many ownChildren
          have childAvailable : Values middle childValues := (buildMany_verified ownChildren environment before context.normal.facts context.inputs).result childValues middle childrenDone
          have edgeContext : Context afterEdge environment := by
            have current := childrenContext.edge own guard childValues childAvailable
            change Context (work (makeEdge own guard childValues) middle).state environment at current
            simpa only [edgeDone, Outcome.state] using current
          have edgeFacts := work_correct (makeEdge own guard childValues) middle childrenFacts.1
          rw [edgeDone] at edgeFacts
          have tailFacts := buildEdges_correct rest environment afterEdge edgeFacts.1
          rw [tailDone] at tailFacts
          rcases List.mem_cons.mp edge with same | inRest
          · cases same
            obtain ⟨start, value, finish, selectedDone, startValid, initialGrowth, suffix⟩ :=
              buildMany_member_checked children environment before childValues middle context childrenDone selected member
            exact ⟨start, value, finish, selectedDone, startValid, initialGrowth,
              grows_trans suffix (grows_trans edgeFacts.2 tailFacts.2)⟩
          · obtain ⟨start, value, finish, selectedDone, startValid, initialGrowth, suffix⟩ :=
              buildEdges_member_checked rest environment afterEdge tail last edgeContext tailDone symbol constraint children inRest selected member
            exact ⟨start, value, finish, selectedDone, startValid,
              grows_trans childrenFacts.2 (grows_trans edgeFacts.2 initialGrowth), suffix⟩
termination_by expressions.length

/-- A declared source site has an actual completed depth-probe representative inside the enclosing trace. -/
theorem completed_site_checked [DecidableEq (EdgeKey Symbol Guard)]
    {expression target : Syntax Symbol Guard} {crossed : Nat} (site : Site expression target crossed)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (context : Context before environment)
    (completed : build expression environment before = .done value final) :
    ∃ start result finish,
      build target (List.replicate crossed (.reference .depth) ++ environment) start = .done result finish ∧
      Context start (List.replicate crossed (.reference .depth) ++ environment) ∧ Grows before start ∧ Grows finish final := by
  induction site generalizing environment before value final with
  | here expression =>
      exact ⟨before, value, final, by simpa using completed, by simpa using context, grows_refl _, grows_refl _⟩
  | @node sourceEdges symbol constraint children child target crossed edge member nested ih =>
      simp only [build] at completed
      obtain ⟨edges, middle, edgesDone, later⟩ := bind_done _ _ _ _ completed
      have edgesFacts := buildEdges_correct sourceEdges environment before context.normal.facts.coherent.valid
      rw [edgesDone] at edgesFacts
      have laterFacts := work_correct (makeNode edges) middle edgesFacts.1
      rw [later] at laterFacts
      obtain ⟨childStart, childValue, childFinal, childDone, childValid, initialGrowth, suffix⟩ :=
        buildEdges_member_checked sourceEdges environment before edges middle context edgesDone symbol constraint children edge child member
      obtain ⟨start, result, finish, targetDone, startValid, targetPrefix, targetSuffix⟩ :=
        ih environment childStart childValue childFinal childValid childDone
      exact ⟨start, result, finish, targetDone, startValid, grows_trans initialGrowth targetPrefix,
        grows_trans targetSuffix (grows_trans suffix laterFacts.2)⟩
  | @union expressions child target crossed member nested ih =>
      simp only [build] at completed
      obtain ⟨members, middle, membersDone, later⟩ := bind_done _ _ _ _ completed
      have membersFacts := buildMany_correct expressions environment before context.normal.facts.coherent.valid
      rw [membersDone] at membersFacts
      have laterFacts := work_correct (makeUnion members) middle membersFacts.1
      rw [later] at laterFacts
      obtain ⟨childStart, childValue, childFinal, childDone, childValid, initialGrowth, suffix⟩ :=
        buildMany_member_checked expressions environment before members middle context membersDone child member
      obtain ⟨start, result, finish, targetDone, startValid, targetPrefix, targetSuffix⟩ :=
        ih environment childStart childValue childFinal childValid childDone
      exact ⟨start, result, finish, targetDone, startValid, grows_trans initialGrowth targetPrefix,
        grows_trans targetSuffix (grows_trans suffix laterFacts.2)⟩
  | @binder smart body target crossed nested ih =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value next => work (withoutSelfReference name value) next
      have growing : ∀ name current, InternedConstructorTemplates.Valid current →
          InternedConstructorTemplates.Valid (callback name current).state ∧ Grows current (callback name current).state := by
        intro name current currentValid
        exact bind_correct _ _ current (build_correct body _ current currentValid)
          (fun value state valid => work_correct (withoutSelfReference name value) state valid)
      simp only [build] at completed
      change (callback .depth before).bind _ = .done value final at completed
      obtain ⟨depth, afterDepth, depthDone, laterDone⟩ := bind_done _ _ _ _ completed
      have depthFacts := growing .depth before context.normal.facts.coherent.valid
      rw [depthDone] at depthFacts
      have remaining := bind_correct
        (callback (.uninterned depth.depth) afterDepth)
        (fun ordinary state => request smart depth ordinary callback state) afterDepth
        (growing _ afterDepth depthFacts.1) (fun ordinary => request_correct smart depth ordinary callback growing)
      rw [laterDone] at remaining
      change (build body (.reference .depth :: environment) before).bind _ = .done depth afterDepth at depthDone
      obtain ⟨bodyValue, afterBody, bodyDone, filtered⟩ := bind_done _ _ _ _ depthDone
      have bodyFacts := build_correct body (.reference .depth :: environment) before context.normal.facts.coherent.valid
      rw [bodyDone] at bodyFacts
      have filterFacts := work_correct (withoutSelfReference .depth bodyValue) afterBody bodyFacts.1
      rw [filtered] at filterFacts
      obtain ⟨start, result, finish, targetDone, startValid, initialGrowth, suffix⟩ :=
        ih (.reference .depth :: environment) before bodyValue afterBody context.depth bodyDone
      refine ⟨start, result, finish, ?_, ?_, initialGrowth, grows_trans suffix (grows_trans filterFacts.2 remaining.2)⟩
      · simpa only [List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append] using targetDone
      · simpa only [List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append] using startValid


end MicroCFTA.InternedProfileTraceSites
