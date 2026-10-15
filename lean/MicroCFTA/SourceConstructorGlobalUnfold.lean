import MicroCFTA.SourceGlobalUnfold
import MicroCFTA.InternedFreshOrdinaryConstruction

/-!
# Constructor requests with explicit global-call events

The executor follows each actual constructor request and continuation.
Its inputs are complete stored values and pure identification functions.
The result does not describe demand on Haskell producer thunks.
-/
namespace MicroCFTA.SourceConstructorGlobalUnfold
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedNestedConstruction (Outcome)
open SourceGlobalUnfold (Event NoGlobal)

/-- Sequence actual outcomes and retain events from a stopped prefix. -/
def bind (first : Outcome Symbol Guard A × List (Event Symbol Guard))
    (next : A → State Symbol Guard → Outcome Symbol Guard B × List (Event Symbol Guard)) :
    Outcome Symbol Guard B × List (Event Symbol Guard) :=
  match first.1 with
  | .pending key state => (.pending key state, first.2)
  | .done value state =>
      let later := next value state
      (later.1, first.2 ++ later.2)

/-- Erasure preserves the actual pending branch and returned state. -/
theorem bind_erase (first : Outcome Symbol Guard A × List (Event Symbol Guard))
    (next : A → State Symbol Guard → Outcome Symbol Guard B × List (Event Symbol Guard)) :
    (bind first next).1 = first.1.bind (fun value state => (next value state).1) := by
  cases actual : first.1 <;> simp only [bind, actual, Outcome.bind]

/-- Concatenation preserves absence of global unfolding calls. -/
theorem silent_append {first second : List (Event Symbol Guard)}
    (left : NoGlobal first) (right : NoGlobal second) : NoGlobal (first ++ second) := by
  intro event member
  rcases List.mem_append.mp member with earlier | later
  · exact left event earlier
  · exact right event later

/-- Outcome sequencing does not introduce a global unfolding call. -/
theorem bind_silent (first : Outcome Symbol Guard A × List (Event Symbol Guard))
    (next : A → State Symbol Guard → Outcome Symbol Guard B × List (Event Symbol Guard))
    (earlier : NoGlobal first.2) (later : ∀ value state, NoGlobal (next value state).2) :
    NoGlobal (bind first next).2 := by
  cases actual : first.1 with
  | pending key state => simpa only [bind, actual] using earlier
  | done value state => simpa only [bind, actual] using silent_append earlier (later value state)

/-- Execute every edge and node request before its actual result continuation. -/
def work [DecidableEq (EdgeKey Symbol Guard)] (job : InternedConstructorTemplates.Work Symbol Guard A)
    (state : State Symbol Guard) : (A × State Symbol Guard) × List (Event Symbol Guard) :=
  match job with
  | .pure value => ((value, state), [])
  | .edge key identify next =>
      let actual := edgeStep key identify state
      let later := work (next actual.1) actual.2
      (later.1, .edgeRequest key :: later.2)
  | .node key identify next =>
      let actual := nodeStep key identify state
      let later := work (next actual.1) actual.2
      (later.1, .nodeRequest key :: later.2)

/-- Event erasure gives the original complete result and both constructor caches. -/
theorem work_erase [DecidableEq (EdgeKey Symbol Guard)]
    (job : InternedConstructorTemplates.Work Symbol Guard A) (state : State Symbol Guard) :
    (work job state).1 = InternedConstructorTemplates.run job state := by
  induction job generalizing state with
  | pure value => rfl
  | edge key identify next ih | node key identify next ih =>
      simpa only [work, InternedConstructorTemplates.run] using ih _ _

/-- Actual constructor requests emit no global unfolding call. -/
theorem work_silent [DecidableEq (EdgeKey Symbol Guard)]
    (job : InternedConstructorTemplates.Work Symbol Guard A) (state : State Symbol Guard) :
    NoGlobal (work job state).2 := by
  induction job generalizing state with
  | pure value => intro event member; cases member
  | edge key identify next ih | node key identify next ih =>
      intro event member
      rcases List.mem_cons.mp member with own | later
      · subst event; rfl
      · exact ih _ _ event later

/-- Lift actual constructor work into the pending-aware constructor schedule. -/
def job [DecidableEq (EdgeKey Symbol Guard)] (computation : InternedConstructorTemplates.Work Symbol Guard A)
    (state : State Symbol Guard) : Outcome Symbol Guard A × List (Event Symbol Guard) :=
  let actual := work computation state
  (.done actual.1.1 actual.1.2, actual.2)

/-- Pending-aware work erases to the original constructor adapter. -/
theorem job_erase [DecidableEq (EdgeKey Symbol Guard)]
    (computation : InternedConstructorTemplates.Work Symbol Guard A) (state : State Symbol Guard) :
    (job computation state).1 = InternedNestedConstruction.work computation state := by
  simp only [job, work_erase, InternedNestedConstruction.work]

/-- The pending-aware adapter retains the actual request events. -/
theorem job_silent [DecidableEq (EdgeKey Symbol Guard)]
    (computation : InternedConstructorTemplates.Work Symbol Guard A) (state : State Symbol Guard) :
    NoGlobal (job computation state).2 := work_silent computation state

/-- Probe lookup skips the body on a hit and reserves before a missing body call. -/
def request [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard) × List (Event Symbol Guard))
    (state : State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) × List (Event Symbol Guard) :=
  let key := muKey depth ordinary
  match state.nodes.table key with
  | some _ =>
      match state.nodeRecords key with
      | some value => (.done (InternedNestedConstruction.finish smart value) state, [.muLookup key])
      | none => (.pending key state, [.muLookup key])
  | none =>
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      let actual := callback (.interned entry.1.identity) allocated
      match actual.1 with
      | .pending pending after =>
          (.pending pending after, .muLookup key :: .muReserve key entry.1.identity :: actual.2)
      | .done body after =>
          let candidate := Value.mu entry.1 body depth ordinary
          let records := keepFirst after.nodeRecords key candidate
          (.done (InternedNestedConstruction.finish smart ((records key).getD candidate))
            {after with nodeRecords := records},
            .muLookup key :: .muReserve key entry.1.identity :: (actual.2 ++ [.muPublish key]))

/-- Request erasure retains the actual winner, pending prefix, and first stored record. -/
theorem request_erase [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard) × List (Event Symbol Guard))
    (state : State Symbol Guard) :
    (request smart depth ordinary callback state).1 =
      InternedNestedConstruction.request smart depth ordinary (fun name current => (callback name current).1) state := by
  cases found : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases stored : state.nodeRecords (muKey depth ordinary) <;>
        simp only [request, InternedNestedConstruction.request, found, stored]
  | none =>
      cases actual : (callback (.interned (Cache.intern state.nodes (muKey depth ordinary)).1.identity)
        {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2}).1 <;>
        simp only [request, InternedNestedConstruction.request, found, actual, Outcome.bind]

/-- A request contains only its actual callback's global unfolding calls. -/
theorem request_silent [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard) × List (Event Symbol Guard))
    (state : State Symbol Guard) (silent : ∀ name current, NoGlobal (callback name current).2) :
    NoGlobal (request smart depth ordinary callback state).2 := by
  cases found : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases stored : state.nodeRecords (muKey depth ordinary) <;>
        simp only [request, found, stored, SourceGlobalUnfold.noGlobal_cons,
          SourceGlobalUnfold.Event.isGlobal, SourceGlobalUnfold.noGlobal_nil, and_self]
  | none =>
      cases actual : (callback (.interned (Cache.intern state.nodes (muKey depth ordinary)).1.identity)
        {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2}).1 <;>
        simp only [request, found, actual, SourceGlobalUnfold.noGlobal_cons, SourceGlobalUnfold.noGlobal_append,
          SourceGlobalUnfold.Event.isGlobal, SourceGlobalUnfold.noGlobal_nil, and_true, true_and] <;>
        exact silent _ _

/-- Work events execute the actual physical primitives with the same complete heap. -/
theorem work_runs [DecidableEq (EdgeKey Symbol Guard)]
    (computation : InternedConstructorTemplates.Work Symbol Guard A) (state : State Symbol Guard)
    (memo : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard) :
    SourceGlobalUnfold.Runs ⟨state, memo⟩ ⟨(work computation state).1.2, memo⟩ (work computation state).2 := by
  induction computation generalizing state with
  | pure value => exact .nil _
  | edge key identify next ih =>
      exact .cons (SourceGlobalUnfold.Step.edge key identify ⟨state, memo⟩) (ih _ _)
  | node key identify next ih =>
      exact .cons (SourceGlobalUnfold.Step.node key identify ⟨state, memo⟩) (ih _ _)

/-- The pending-aware work adapter has the same actual primitive execution. -/
theorem job_runs [DecidableEq (EdgeKey Symbol Guard)]
    (computation : InternedConstructorTemplates.Work Symbol Guard A) (state : State Symbol Guard)
    (memo : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard) :
    SourceGlobalUnfold.Runs ⟨state, memo⟩ ⟨(job computation state).1.state, memo⟩ (job computation state).2 :=
  work_runs computation state memo

/-- Sequencing composes actual primitive runs and stops at a pending earlier outcome. -/
theorem bind_runs [DecidableEq (EdgeKey Symbol Guard)]
    (first : Outcome Symbol Guard A × List (Event Symbol Guard))
    (next : A → State Symbol Guard → Outcome Symbol Guard B × List (Event Symbol Guard))
    (state : State Symbol Guard) (memo : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard)
    (earlier : SourceGlobalUnfold.Runs ⟨state, memo⟩ ⟨first.1.state, memo⟩ first.2)
    (later : ∀ value current, SourceGlobalUnfold.Runs ⟨current, memo⟩
      ⟨(next value current).1.state, memo⟩ (next value current).2) :
    SourceGlobalUnfold.Runs ⟨state, memo⟩ ⟨(bind first next).1.state, memo⟩ (bind first next).2 := by
  cases actual : first.1 with
  | pending key current => simpa only [bind, actual, Outcome.state] using earlier
  | done value current =>
      have earlierRun : SourceGlobalUnfold.Runs ⟨state, memo⟩ ⟨current, memo⟩ first.2 := by
        simpa only [actual, Outcome.state] using earlier
      simpa only [bind, actual] using earlierRun.append (later value current)

/-- Lookup, reservation, the winning callback, and publication execute in their recorded order. -/
theorem request_runs [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard) × List (Event Symbol Guard))
    (state : State Symbol Guard) (memo : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard)
    (calls : ∀ name current, SourceGlobalUnfold.Runs ⟨current, memo⟩
      ⟨(callback name current).1.state, memo⟩ (callback name current).2) :
    SourceGlobalUnfold.Runs ⟨state, memo⟩ ⟨(request smart depth ordinary callback state).1.state, memo⟩
      (request smart depth ordinary callback state).2 := by
  let key := muKey depth ordinary
  cases found : state.nodes.table key with
  | some entry =>
      dsimp only [key] at found
      cases stored : state.nodeRecords (muKey depth ordinary) <;>
        simpa only [request, key, found, stored, Outcome.state] using
          SourceGlobalUnfold.Runs.single (SourceGlobalUnfold.Step.muLookup key ⟨state, memo⟩)
  | none =>
      dsimp only [key] at found
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      have lookupStep := SourceGlobalUnfold.Step.muLookup key ⟨state, memo⟩
      have reserve := SourceGlobalUnfold.Step.muReserve key ⟨state, memo⟩
      have called := calls (.interned entry.1.identity) allocated
      cases actual : (callback (.interned entry.1.identity) allocated).1 with
      | pending pending after =>
          dsimp only [allocated, entry, key] at actual
          have body : SourceGlobalUnfold.Runs ⟨allocated, memo⟩ ⟨after, memo⟩
              (callback (.interned entry.1.identity) allocated).2 := by
            simpa only [allocated, entry, key, actual, Outcome.state] using called
          simpa only [request, key, entry, allocated, found, actual, Outcome.state] using
            SourceGlobalUnfold.Runs.cons lookupStep (SourceGlobalUnfold.Runs.cons reserve body)
      | done value after =>
          dsimp only [allocated, entry, key] at actual
          have body : SourceGlobalUnfold.Runs ⟨allocated, memo⟩ ⟨after, memo⟩
              (callback (.interned entry.1.identity) allocated).2 := by
            simpa only [allocated, entry, key, actual, Outcome.state] using called
          have publish := SourceGlobalUnfold.Runs.single
            (SourceGlobalUnfold.Step.muPublish entry.1 value depth ordinary ⟨after, memo⟩)
          simpa only [request, key, entry, allocated, found, actual, Outcome.state] using
            SourceGlobalUnfold.Runs.cons lookupStep (SourceGlobalUnfold.Runs.cons reserve (body.append publish))

end MicroCFTA.SourceConstructorGlobalUnfold
