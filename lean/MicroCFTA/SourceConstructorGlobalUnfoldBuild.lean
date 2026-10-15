import MicroCFTA.SourceConstructorGlobalUnfold
import MicroCFTA.SourceRecursiveIntersectionMaybeMu

/-!
# Fresh constructor bodies with exact request events

Both probes run before lookup. A miss reserves the identity before the
winning callback runs. A pending callback stops the remaining schedule.
These statements apply to complete stored inputs. They do not model GHC
demand on delayed producer computations or substitution-plan memo tables.
-/
namespace MicroCFTA.SourceConstructorGlobalUnfold
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open SourceGlobalUnfold (Event NoGlobal)

mutual
/-- Execute the fresh constructor schedule and record each actual primitive request. -/
def build [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    Outcome Symbol Guard (Value Symbol Guard) × List (Event Symbol Guard) :=
  match expression with
  | .empty => (.done .empty state, [])
  | .var index => (.done (environment[index]?.getD .empty) state, [])
  | .node edges => bind (buildEdges edges environment state) fun values after => job (makeNode values) after
  | .union members => bind (buildMany members environment state) fun values after => job (makeUnion values) after
  | .binder smart body =>
      let callback := fun name current => bind (build body (.reference name :: environment) current)
        fun value after => job (withoutSelfReference name value) after
      bind (callback .depth state) fun depth afterDepth =>
      bind (callback (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth)
        fun ordinary afterOrdinary => request smart depth ordinary callback afterOrdinary
termination_by sizeOf expression

/-- Retain child order and the events of every completed earlier child. -/
def buildMany [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    Outcome Symbol Guard (List (Value Symbol Guard)) × List (Event Symbol Guard) :=
  match expressions with
  | [] => (.done [] state, [])
  | first :: rest => bind (build first environment state) fun value after =>
      bind (buildMany rest environment after) fun values final => (.done (value :: values) final, [])
termination_by sizeOf expressions

/-- Construct each edge after its children and before the next source edge. -/
def buildEdges [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    Outcome Symbol Guard (List (EdgeValue Symbol Guard)) × List (Event Symbol Guard) :=
  match expressions with
  | [] => (.done [] state, [])
  | .mk symbol guard children :: rest => bind (buildMany children environment state) fun values after =>
      bind (job (makeEdge symbol guard values) after) fun edge afterEdge =>
      bind (buildEdges rest environment afterEdge) fun edges final => (.done (edge :: edges) final, [])
termination_by sizeOf expressions
end

mutual
/-- Erasure retains every fresh probe, stopped callback, and exact constructor cache. -/
theorem build_erase [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    (build expression environment state).1 = InternedFreshOrdinaryConstruction.build expression environment state := by
  cases expression with
  | empty | var => simp only [build, InternedFreshOrdinaryConstruction.build]
  | node edges =>
      simp only [build, bind_erase, buildEdges_erase edges environment state,
        job_erase, InternedFreshOrdinaryConstruction.build]
  | union members =>
      simp only [build, bind_erase, buildMany_erase members environment state,
        job_erase, InternedFreshOrdinaryConstruction.build]
  | binder smart body =>
      simp only [build, bind_erase, build_erase body, job_erase, request_erase, InternedFreshOrdinaryConstruction.build]
termination_by sizeOf expression

/-- Erasure retains the actual ordered child sequence, including pending prefixes. -/
theorem buildMany_erase [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    (buildMany expressions environment state).1 = InternedFreshOrdinaryConstruction.buildMany expressions environment state := by
  cases expressions with
  | nil => simp only [buildMany, InternedFreshOrdinaryConstruction.buildMany]
  | cons first rest =>
      simp only [buildMany, bind_erase, build_erase first environment state,
        buildMany_erase rest environment, InternedFreshOrdinaryConstruction.buildMany]
termination_by sizeOf expressions

/-- Erasure retains the actual child, edge, and tail constructor effects. -/
theorem buildEdges_erase [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    (buildEdges expressions environment state).1 = InternedFreshOrdinaryConstruction.buildEdges expressions environment state := by
  cases expressions with
  | nil => simp only [buildEdges, InternedFreshOrdinaryConstruction.buildEdges]
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          simp only [buildEdges, bind_erase, buildMany_erase children environment state,
            job_erase, buildEdges_erase rest environment, InternedFreshOrdinaryConstruction.buildEdges]
termination_by sizeOf expressions
end

mutual
/-- Fresh body construction has no global unfolding-call event. -/
theorem build_silent [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    NoGlobal (build expression environment state).2 := by
  cases expression with
  | empty | var => simp only [build]; exact SourceGlobalUnfold.NoGlobal.nil
  | node edges =>
      simp only [build]
      exact bind_silent _ _ (buildEdges_silent edges environment state) (fun values after => job_silent (makeNode values) after)
  | union members =>
      simp only [build]
      exact bind_silent _ _ (buildMany_silent members environment state) (fun values after => job_silent (makeUnion values) after)
  | binder smart body =>
      simp only [build]
      have callbackSilent (name : Reference) (current : State Symbol Guard) :
          NoGlobal (bind (build body (.reference name :: environment) current)
            (fun value after => job (withoutSelfReference name value) after)).2 :=
        bind_silent _ _ (build_silent body (.reference name :: environment) current)
          (fun value after => job_silent (withoutSelfReference name value) after)
      exact bind_silent _ _ (callbackSilent .depth state) fun depth afterDepth =>
        bind_silent _ _ (callbackSilent _ afterDepth) fun ordinary afterOrdinary =>
          request_silent smart depth ordinary _ afterOrdinary callbackSilent
termination_by sizeOf expression

/-- Ordered child construction has no global unfolding-call event. -/
theorem buildMany_silent [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    NoGlobal (buildMany expressions environment state).2 := by
  cases expressions with
  | nil => simp only [buildMany]; exact SourceGlobalUnfold.NoGlobal.nil
  | cons first rest =>
      simp only [buildMany]
      exact bind_silent _ _ (build_silent first environment state) fun value after =>
        bind_silent _ _ (buildMany_silent rest environment after) (fun _ _ => SourceGlobalUnfold.NoGlobal.nil)
termination_by sizeOf expressions

/-- Ordered edge construction has no global unfolding-call event. -/
theorem buildEdges_silent [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    NoGlobal (buildEdges expressions environment state).2 := by
  cases expressions with
  | nil => simp only [buildEdges]; exact SourceGlobalUnfold.NoGlobal.nil
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          simp only [buildEdges]
          exact bind_silent _ _ (buildMany_silent children environment state) fun values after =>
            bind_silent _ _ (job_silent (makeEdge symbol guard values) after) fun edge afterEdge =>
              bind_silent _ _ (buildEdges_silent rest environment afterEdge) (fun _ _ => SourceGlobalUnfold.NoGlobal.nil)
termination_by sizeOf expressions
end

/-- Execute the fixed source substitution callback without an abstract callback premise. -/
def callback [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (name : Reference) (state : State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) × List (Event Symbol Guard) :=
  bind (build (InternedStoredSubstitution.encode (InternedStoredSubstitution.leaves body) [] body)
    ((InternedStoredSubstitution.leaves body).map
      (InternedStoredSubstitution.input (InternedStoredSubstitutionRebind.replacement old (.reference name)))) state)
    fun value after => job (withoutSelfReference name value) after

/-- The fixed callback erases for every complete stored body and current cache. -/
theorem callback_erase [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (name : Reference) (state : State Symbol Guard) :
    (callback old body name state).1 = SourceRecursiveIntersectionMaybeMu.callback old body name state := by
  simp only [callback, bind_erase, build_erase, job_erase, SourceRecursiveIntersectionMaybeMu.callback,
    InternedFreshOrdinaryStoredSubstitution.execute]

/-- The fixed callback's constructor events contain no global unfolding call. -/
theorem callback_silent [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (name : Reference) (state : State Symbol Guard) : NoGlobal (callback old body name state).2 :=
  bind_silent _ _ (build_silent _ _ _) (fun value after => job_silent (withoutSelfReference name value) after)

/-- Execute both fixed probes before the actual hit, pending, or reserved-body branch. -/
def construct [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (state : State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) × List (Event Symbol Guard) :=
  bind (callback old body .depth state) fun depth afterDepth =>
  bind (callback old body (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth)
    fun ordinary afterOrdinary => request true depth ordinary (callback old body) afterOrdinary

/-- The actual fixed-body constructor retains the full old outcome and cache. -/
theorem construct_erase [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (state : State Symbol Guard) :
    (construct old body state).1 = SourceRecursiveIntersectionMaybeMu.construct old body state := by
  simp only [construct, bind_erase, callback_erase, request_erase, SourceRecursiveIntersectionMaybeMu.construct]

/-- Both probes and every demanded winning callback have no global unfolding call. -/
theorem construct_silent [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (state : State Symbol Guard) : NoGlobal (construct old body state).2 :=
  bind_silent _ _ (callback_silent old body .depth state) fun depth afterDepth =>
    bind_silent _ _ (callback_silent old body _ afterDepth) fun ordinary afterOrdinary =>
      request_silent true depth ordinary (callback old body) afterOrdinary (callback_silent old body)

/-- Preserve the literal repeated-pair test before the optional constructor schedule. -/
def maybeMu [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) × List (Event Symbol Guard) :=
  if Reference.intersection key.1 key.2 ∈ body.free then construct (.intersection key.1 key.2) body state
  else (.done body state, [])

/-- Optional-binder event erasure preserves done and pending outcomes unconditionally. -/
theorem maybeMu_erase [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) :
    (maybeMu key body state).1 = SourceRecursiveIntersectionMaybeMu.maybeMu key body state := by
  unfold maybeMu SourceRecursiveIntersectionMaybeMu.maybeMu
  split
  · exact construct_erase _ _ _
  · rfl

/-- The actual optional binder emits no global unfolding-call event. -/
theorem maybeMu_silent [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) : NoGlobal (maybeMu key body state).2 := by
  unfold maybeMu
  split
  · exact construct_silent _ _ _
  · intro event member; cases member

/-- Every old optional-binder outcome has an exact instrumented execution with no global call. -/
theorem maybeMu_complete [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) :
    ∃ events, maybeMu key body state = (SourceRecursiveIntersectionMaybeMu.maybeMu key body state, events) ∧ NoGlobal events := by
  exact ⟨(maybeMu key body state).2, by rw [← maybeMu_erase], maybeMu_silent key body state⟩

mutual
/-- Fresh construction executes every recorded primitive in the actual returned heap. -/
theorem build_runs [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (memo : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard) :
    SourceGlobalUnfold.Runs ⟨state, memo⟩ ⟨(build expression environment state).1.state, memo⟩
      (build expression environment state).2 := by
  cases expression with
  | empty | var => simp only [build, Outcome.state]; exact .nil _
  | node edges =>
      simp only [build]
      exact bind_runs _ _ state memo (buildEdges_runs edges environment state memo)
        (fun values after => job_runs (makeNode values) after memo)
  | union members =>
      simp only [build]
      exact bind_runs _ _ state memo (buildMany_runs members environment state memo)
        (fun values after => job_runs (makeUnion values) after memo)
  | binder smart body =>
      simp only [build]
      have callbackRuns (name : Reference) (current : State Symbol Guard) :
          SourceGlobalUnfold.Runs ⟨current, memo⟩
            ⟨(bind (build body (.reference name :: environment) current)
              (fun value after => job (withoutSelfReference name value) after)).1.state, memo⟩
            (bind (build body (.reference name :: environment) current)
              (fun value after => job (withoutSelfReference name value) after)).2 :=
        bind_runs _ _ current memo (build_runs body (.reference name :: environment) current memo)
          (fun value after => job_runs (withoutSelfReference name value) after memo)
      exact bind_runs _ _ state memo (callbackRuns .depth state) fun depth afterDepth =>
        bind_runs _ _ afterDepth memo (callbackRuns _ afterDepth) fun ordinary afterOrdinary =>
          request_runs smart depth ordinary _ afterOrdinary memo callbackRuns
termination_by sizeOf expression

/-- Child traces preserve the actual order of physical primitive executions. -/
theorem buildMany_runs [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (memo : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard) :
    SourceGlobalUnfold.Runs ⟨state, memo⟩ ⟨(buildMany expressions environment state).1.state, memo⟩
      (buildMany expressions environment state).2 := by
  cases expressions with
  | nil => simp only [buildMany, Outcome.state]; exact .nil _
  | cons first rest =>
      simp only [buildMany]
      exact bind_runs _ _ state memo (build_runs first environment state memo) fun value after =>
        bind_runs _ _ after memo (buildMany_runs rest environment after memo) (fun _ _ => .nil _)
termination_by sizeOf expressions

/-- Edge traces retain child construction, physical interning, and later source rows. -/
theorem buildEdges_runs [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (memo : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard) :
    SourceGlobalUnfold.Runs ⟨state, memo⟩ ⟨(buildEdges expressions environment state).1.state, memo⟩
      (buildEdges expressions environment state).2 := by
  cases expressions with
  | nil => simp only [buildEdges, Outcome.state]; exact .nil _
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          simp only [buildEdges]
          exact bind_runs _ _ state memo (buildMany_runs children environment state memo) fun values after =>
            bind_runs _ _ after memo (job_runs (makeEdge symbol guard values) after memo) fun edge afterEdge =>
              bind_runs _ _ afterEdge memo (buildEdges_runs rest environment afterEdge memo) (fun _ _ => .nil _)
termination_by sizeOf expressions
end

/-- The fixed substitution callback executes its recorded physical events. -/
theorem callback_runs [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (name : Reference) (state : State Symbol Guard) (memo : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard) :
    SourceGlobalUnfold.Runs ⟨state, memo⟩ ⟨(callback old body name state).1.state, memo⟩
      (callback old body name state).2 :=
  bind_runs _ _ state memo (build_runs _ _ _ memo) (fun value after => job_runs (withoutSelfReference name value) after memo)

/-- The fixed two-probe constructor executes lookup, reservation, and publication as recorded. -/
theorem construct_runs [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (state : State Symbol Guard) (memo : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard) :
    SourceGlobalUnfold.Runs ⟨state, memo⟩ ⟨(construct old body state).1.state, memo⟩ (construct old body state).2 :=
  bind_runs _ _ state memo (callback_runs old body .depth state memo) fun depth afterDepth =>
    bind_runs _ _ afterDepth memo (callback_runs old body _ afterDepth memo) fun ordinary afterOrdinary =>
      request_runs true depth ordinary (callback old body) afterOrdinary memo (fun name current => callback_runs old body name current memo)

/-- The actual optional binder has a complete physical primitive trace at every outcome. -/
theorem maybeMu_runs [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (memo : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard) :
    SourceGlobalUnfold.Runs ⟨state, memo⟩ ⟨(maybeMu key body state).1.state, memo⟩ (maybeMu key body state).2 := by
  unfold maybeMu
  split
  · exact construct_runs _ _ _ _
  · exact .nil _

end MicroCFTA.SourceConstructorGlobalUnfold
