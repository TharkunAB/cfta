import MicroCFTA.AcceptanceDispatch
import MicroCFTA.Guards

/-!
# The global Unknown effect of refinement acceptance

The source records whether any executed guard callback returned Unknown.
Cache hits execute no callback. The flag persists through failed children,
failed alternatives, cache updates, and fresh shared tables. A trace records
the callbacks in their actual execution order for the flag invariant.
-/

namespace MicroCFTA.AcceptanceEffects
open Language NumberedTerms AcceptanceReference AcceptanceCache AcceptanceWorker AcceptanceDispatch

/-- One actual guard callback, after its children succeed. -/
abbrev Event (State Symbol : Type) := State × Edge State Symbol × Term Symbol

/-- The source cache and global Unknown flag, with an execution trace used only by the proof. -/
structure Context (State Symbol : Type) where
  cache : Cache State
  unknown : Bool
  events : List (Event State Symbol)

/-- A stable callback's Unknown projection. Its Yes projection is the automaton edge guard. -/
abbrev IsUnknown (State Symbol : Type) := State → Edge State Symbol → Term Symbol → Bool

/-- The recorded flag is exactly the disjunction of Unknown among executed callbacks. -/
def Tracks (unknown : IsUnknown State Symbol) (context : Context State Symbol) : Prop :=
  context.unknown = context.events.any (fun (key, edge, term) => unknown key edge term)

/-- Execute one callback and retain its Unknown result even if this alternative fails. -/
def check (unknown : IsUnknown State Symbol) (key : State) (edge : Edge State Symbol) (term : Term Symbol)
    (context : Context State Symbol) : Bool × Context State Symbol :=
  (edge.guard term, ⟨context.cache, context.unknown || unknown key edge term,
    context.events ++ [(key, edge, term)]⟩)

/-- Callback execution adds precisely its own Unknown effect to the global record. -/
theorem check_tracks (unknown : IsUnknown State Symbol) (key : State) (edge : Edge State Symbol) (term : Term Symbol)
    (context : Context State Symbol) (tracks : Tracks unknown context) : Tracks unknown (check unknown key edge term context).2 := by
  unfold Tracks at tracks ⊢
  simp [check, List.any_append, tracks]

/-- Forget only the global effect and its trace, retaining the exact answer and cache fields. -/
def erase (result : Bool × Context State Symbol) : Bool × Cache State := (result.1, result.2.cache)

/-- Ordered conjunction commutes with projection when each visited action does. -/
theorem allM_project (left : α → σ → Bool × σ) (right : α → τ → Bool × τ) (project : σ → τ)
    (items : List α) (state : σ)
    (correspondence : ∀ item ∈ items, ∀ state, ((left item state).1, project (left item state).2) = right item (project state)) :
    ((allM left items state).1, project (allM left items state).2) = allM right items (project state) := by
  induction items generalizing state with
  | nil => rfl
  | cons first rest ih =>
      have head := correspondence first (by simp) state
      have answer := congrArg Prod.fst head
      have next := congrArg Prod.snd head
      have tail := ih (left first state).2 (fun item member => correspondence item (by simp [member]))
      cases accepted : (left first state).1 with
      | false => simp [allM, ← answer, accepted, ← next]
      | true => simpa [allM, ← answer, accepted, ← next] using tail

/-- Ordered disjunction commutes with projection without changing short-circuit behavior. -/
theorem anyM_project (left : α → σ → Bool × σ) (right : α → τ → Bool × τ) (project : σ → τ)
    (items : List α) (state : σ)
    (correspondence : ∀ item ∈ items, ∀ state, ((left item state).1, project (left item state).2) = right item (project state)) :
    ((anyM left items state).1, project (anyM left items state).2) = anyM right items (project state) := by
  induction items generalizing state with
  | nil => rfl
  | cons first rest ih =>
      have head := correspondence first (by simp) state
      have answer := congrArg Prod.fst head
      have next := congrArg Prod.snd head
      have tail := ih (left first state).2 (fun item member => correspondence item (by simp [member]))
      cases accepted : (left first state).1 with
      | false => simpa [anyM, ← answer, accepted, ← next] using tail
      | true => simp [anyM, ← answer, accepted, ← next]

/-- A tracked visit preserves the global flag on a hit and records a computed answer on a miss. -/
def visit [DecidableEq State] (compute : State → Positioned Symbol → Context State Symbol → Bool × Context State Symbol)
    (key : State) (node : Positioned Symbol) (context : Context State Symbol) : Bool × Context State Symbol :=
  match context.cache (position node, key) with
  | some answer => (answer, context)
  | none =>
      let result := compute key node context
      (result.1, {result.2 with cache := insert result.2.cache (position node) key result.1})

/-- Cache lookup and insertion commute with projection, including both cache-hit and cache-miss branches. -/
theorem visit_project [DecidableEq State]
    (tracked : State → Positioned Symbol → Context State Symbol → Bool × Context State Symbol)
    (plain : State → Positioned Symbol → Cache State → Bool × Cache State)
    (key : State) (node : Positioned Symbol) (context : Context State Symbol)
    (correspondence : erase (tracked key node context) = plain key node context.cache) :
    erase (visit tracked key node context) = AcceptanceCache.visit plain key node context.cache := by
  cases found : context.cache (position node, key) with
  | some answer => simp [visit, AcceptanceCache.visit, found, erase]
  | none =>
      have answer := congrArg Prod.fst correspondence
      have cache := congrArg Prod.snd correspondence
      simp [visit, AcceptanceCache.visit, found, erase] at answer cache ⊢
      simp [answer, cache]

/-- Cache actions preserve the trace/flag invariant because they do not remove effects. -/
theorem visit_tracks [DecidableEq State] (unknown : IsUnknown State Symbol)
    (compute : State → Positioned Symbol → Context State Symbol → Bool × Context State Symbol)
    (key : State) (node : Positioned Symbol) (context : Context State Symbol) (tracks : Tracks unknown context)
    (computed : Tracks unknown (compute key node context).2) : Tracks unknown (visit compute key node context).2 := by
  cases found : context.cache (position node, key) <;> simp_all [visit, Tracks]

/-- The shared worker retains the source's global Unknown flag alongside its local cache. -/
def shared [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol) (unknown : IsUnknown State Symbol) :
    Nat → State → Positioned Symbol → Context State Symbol → Bool × Context State Symbol
  | 0, _, _, context => (false, context)
  | fuel + 1, key, .node _ term children, context =>
      anyM (fun edge context =>
        let children := allM (fun pair context => visit (shared automaton unknown fuel) pair.1 pair.2 context)
          (edge.children.zip children) context
        if children.1 then check unknown key edge term children.2 else (false, children.2))
        ((automaton key).filter (fun edge => matchesRoot edge term)) context

/-- Forgetting the effect gives exactly the already verified shared worker, including its cache. -/
theorem shared_project [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (unknown : IsUnknown State Symbol) (fuel : Nat) (key : State) (node : Positioned Symbol) (context : Context State Symbol) :
    erase (shared automaton unknown fuel key node context) = AcceptanceWorker.shared automaton fuel key node context.cache := by
  induction fuel generalizing key node context with
  | zero => rfl
  | succ fuel ih =>
      cases node with
      | node index term children =>
          apply anyM_project _ _ Context.cache
          intro edge _ current
          have checked := allM_project (α := State × Positioned Symbol)
            (fun pair context => visit (shared automaton unknown fuel) pair.1 pair.2 context)
            (fun pair cache => AcceptanceCache.visit (AcceptanceWorker.shared automaton fuel) pair.1 pair.2 cache)
            Context.cache (edge.children.zip children) current
            (fun pair _ context => visit_project _ _ pair.1 pair.2 context (ih pair.1 pair.2 context))
          have answer := congrArg Prod.fst checked
          have cache := congrArg Prod.snd checked
          dsimp only at answer cache ⊢
          cases accepted : (allM (fun pair context => visit (shared automaton unknown fuel) pair.1 pair.2 context)
              (edge.children.zip children) current).1 <;>
            simp [← answer, accepted, check, ← cache]

/-- Every source callback effect survives every child and alternative short-circuit and cache update. -/
theorem shared_tracks [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (unknown : IsUnknown State Symbol) (fuel : Nat) (key : State) (node : Positioned Symbol) (context : Context State Symbol)
    (tracks : Tracks unknown context) : Tracks unknown (shared automaton unknown fuel key node context).2 := by
  induction fuel generalizing key node context with
  | zero => exact tracks
  | succ fuel ih =>
      cases node with
      | node index term children =>
          apply anyM_preserves _ (Tracks unknown) _ context tracks
          intro edge _ current invariant
          have checked := allM_preserves
            (fun pair context => visit (shared automaton unknown fuel) pair.1 pair.2 context) (Tracks unknown)
            (edge.children.zip children) current invariant
            (fun pair _ context valid => visit_tracks unknown _ pair.1 pair.2 context valid (ih pair.1 pair.2 context valid))
          dsimp only
          split
          · exact check_tracks unknown key edge term _ checked
          · exact checked

/-- The adaptive worker creates each shared cache locally while retaining the global Unknown state. -/
def unshared [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol) (unknown : IsUnknown State Symbol) :
    Nat → State → Term Symbol → Context State Symbol → Bool × Context State Symbol
  | 0, _, _, context => (false, context)
  | fuel + 1, key, term@(.node _ children), context =>
      match fromMatch term (automaton key) with
      | [] => (false, context)
      | edge :: rest => match fromMatch term rest with
        | [] =>
            let checked := allM (fun pair context => unshared automaton unknown fuel pair.1 pair.2 context)
              (edge.children.zip children) context
            if checked.1 then check unknown key edge term checked.2 else (false, checked.2)
        | _ :: _ =>
            let checked := shared automaton unknown (fuel + 1) key (number term 0).2 {context with cache := fun _ => none}
            (checked.1, {checked.2 with cache := context.cache})

/-- The global effect changes no Boolean search decision, including adaptive table creation. -/
theorem unshared_project [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (unknown : IsUnknown State Symbol) (fuel : Nat) (key : State) (term : Term Symbol) (context : Context State Symbol) :
    (unshared automaton unknown fuel key term context).1 = AcceptanceDispatch.unshared automaton fuel key term := by
  induction fuel generalizing key term context with
  | zero => rfl
  | succ fuel ih =>
      cases term with
      | node symbol children =>
          cases first : fromMatch (.node symbol children) (automaton key) with
          | nil => simp [unshared, AcceptanceDispatch.unshared, first]
          | cons edge rest =>
              cases second : fromMatch (.node symbol children) rest with
              | nil =>
                  have checked := allM_correct (α := State × Term Symbol)
                    (fun pair context => unshared automaton unknown fuel pair.1 pair.2 context)
                    (fun pair => AcceptanceDispatch.unshared automaton fuel pair.1 pair.2) (fun _ => True)
                    (edge.children.zip children) context trivial (fun pair _ context _ => ⟨ih pair.1 pair.2 context, trivial⟩)
                  rw [← zipAll_eq_all] at checked
                  simp only [unshared, AcceptanceDispatch.unshared, first, second]
                  cases returned : (allM (fun pair context => unshared automaton unknown fuel pair.1 pair.2 context)
                      (edge.children.zip children) context).1 <;> simp [check, ← checked.1, returned]
              | cons other later =>
                  have projected := congrArg Prod.fst (shared_project automaton unknown (fuel + 1) key
                    (number (.node symbol children) 0).2 {context with cache := fun _ => none})
                  simpa [unshared, AcceptanceDispatch.unshared, first, second, erase] using projected

/-- Failed direct branches and completed shared regions retain all Unknown effects in the global flag. -/
theorem unshared_tracks [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (unknown : IsUnknown State Symbol) (fuel : Nat) (key : State) (term : Term Symbol) (context : Context State Symbol)
    (tracks : Tracks unknown context) : Tracks unknown (unshared automaton unknown fuel key term context).2 := by
  induction fuel generalizing key term context with
  | zero => exact tracks
  | succ fuel ih =>
      cases term with
      | node symbol children =>
          cases first : fromMatch (.node symbol children) (automaton key) with
          | nil => simpa [unshared, first] using tracks
          | cons edge rest =>
              cases second : fromMatch (.node symbol children) rest with
              | nil =>
                  have checked := allM_preserves (fun pair context => unshared automaton unknown fuel pair.1 pair.2 context)
                    (Tracks unknown) (edge.children.zip children) context tracks (fun pair _ context valid => ih pair.1 pair.2 context valid)
                  simp only [unshared, first, second]
                  split
                  · exact check_tracks unknown key edge (.node symbol children) _ checked
                  · exact checked
              | cons other later =>
                  have checked := shared_tracks automaton unknown (fuel + 1) key (number (.node symbol children) 0).2
                    {context with cache := fun _ => none} tracks
                  simpa only [unshared, first, second, Tracks] using checked

/-- Each action retains every earlier callback in its original execution order. -/
def Retains (before after : Context State Symbol) : Prop := before.events.IsPrefix after.events

/-- Executing a guard appends one event without losing any earlier event. -/
theorem check_retains (unknown : IsUnknown State Symbol) (key : State) (edge : Edge State Symbol) (term : Term Symbol)
    (context : Context State Symbol) : Retains context (check unknown key edge term context).2 :=
  List.prefix_append _ _

/-- Cache hits retain the trace; cache misses retain the computed extension. -/
theorem visit_retains [DecidableEq State]
    (compute : State → Positioned Symbol → Context State Symbol → Bool × Context State Symbol)
    (key : State) (node : Positioned Symbol) (context : Context State Symbol)
    (computed : Retains context (compute key node context).2) : Retains context (visit compute key node context).2 := by
  cases found : context.cache (position node, key) <;> simp_all [visit, Retains]

/-- Shared search never loses an event across a failed child, failed alternative, or successful cache hit. -/
theorem shared_retains [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (unknown : IsUnknown State Symbol) (fuel : Nat) (key : State) (node : Positioned Symbol) (context : Context State Symbol) :
    Retains context (shared automaton unknown fuel key node context).2 := by
  induction fuel generalizing key node context with
  | zero => exact ⟨[], by simp [shared]⟩
  | succ fuel ih =>
      cases node with
      | node index term children =>
          apply anyM_preserves _ (Retains context) _ context (by exact ⟨[], by simp⟩)
          intro edge _ current retained
          have checked := allM_preserves (α := State × Positioned Symbol)
            (fun pair context => visit (shared automaton unknown fuel) pair.1 pair.2 context) (Retains context)
            (edge.children.zip children) current retained
            (fun pair _ state previous => List.IsPrefix.trans previous
              (visit_retains _ pair.1 pair.2 state (ih pair.1 pair.2 state)))
          dsimp only
          split
          · exact List.IsPrefix.trans checked (check_retains unknown key edge term _)
          · exact checked

/-- Adaptive search preserves the global trace when it creates and discards each local shared cache. -/
theorem unshared_retains [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (unknown : IsUnknown State Symbol) (fuel : Nat) (key : State) (term : Term Symbol) (context : Context State Symbol) :
    Retains context (unshared automaton unknown fuel key term context).2 := by
  induction fuel generalizing key term context with
  | zero => exact ⟨[], by simp [unshared]⟩
  | succ fuel ih =>
      cases term with
      | node symbol children =>
          cases first : fromMatch (.node symbol children) (automaton key) with
          | nil => simp [unshared, first, Retains]
          | cons edge rest =>
              cases second : fromMatch (.node symbol children) rest with
              | nil =>
                  have checked := allM_preserves (α := State × Term Symbol) (fun pair state => unshared automaton unknown fuel pair.1 pair.2 state)
                    (Retains context) (edge.children.zip children) context (by exact ⟨[], by simp⟩)
                    (fun pair _ state previous => List.IsPrefix.trans previous (ih pair.1 pair.2 state))
                  simp only [unshared, first, second]
                  split
                  · exact List.IsPrefix.trans checked (check_retains unknown key edge (.node symbol children) _)
                  · exact checked
              | cons other later =>
                  have retained := shared_retains automaton unknown (fuel + 1) key (number (.node symbol children) 0).2
                    {context with cache := fun _ => none}
                  simpa only [unshared, first, second, Retains] using retained

/-- A true global Unknown flag remains true when a tracked action retains the preceding callbacks. -/
theorem unknown_monotone (unknown : IsUnknown State Symbol) (before after : Context State Symbol)
    (first : Tracks unknown before) (last : Tracks unknown after) (retained : Retains before after)
    (seen : before.unknown = true) : after.unknown = true := by
  obtain ⟨suffix, appended⟩ := retained
  unfold Tracks at first last
  rw [last, ← appended, List.any_append, ← first, seen]
  rfl

/-- No acceptance worker path can clear an Unknown observed earlier in the same query. -/
theorem unshared_unknown_monotone [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (unknown : IsUnknown State Symbol) (fuel : Nat) (key : State) (term : Term Symbol) (context : Context State Symbol)
    (tracks : Tracks unknown context) (seen : context.unknown = true) :
    (unshared automaton unknown fuel key term context).2.unknown = true :=
  unknown_monotone unknown context _ tracks (unshared_tracks automaton unknown fuel key term context tracks)
    (unshared_retains automaton unknown fuel key term context) seen

/-- A new refinement query starts with no cached values, no Unknown result, and no executed callback. -/
def initial : Context State Symbol := ⟨fun _ => none, false, []⟩

/-- The source gives a confirmed accepting run precedence over earlier undecided alternatives. -/
def finish (result : Bool × Context State Symbol) : Guards.Verdict :=
  if result.1 then .yes else if result.2.unknown then .unknown else .no

/-- Execute the complete refinement acceptance worker with the input term's structural height. -/
def accepts [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (unknown : IsUnknown State Symbol) (key : State) (term : Term Symbol) : Guards.Verdict :=
  finish (unshared automaton unknown term.height key term initial)

/-- The trace contains exactly the callback events executed by the complete adaptive search. -/
def events [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (unknown : IsUnknown State Symbol) (key : State) (term : Term Symbol) : List (Event State Symbol) :=
  (unshared automaton unknown term.height key term initial).2.events

/-- A final Yes means exactly an accepting run whose guards are all confirmed Yes. -/
theorem accepts_yes [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (unknown : IsUnknown State Symbol) (key : State) (term : Term Symbol) :
    accepts automaton unknown key term = .yes ↔ Accepts automaton key term := by
  unfold accepts finish
  rw [unshared_project]
  cases accepted : AcceptanceDispatch.unshared automaton term.height key term <;>
    simp [accepted, ← AcceptanceDispatch.acceptsBy_exact automaton key term]
  split <;> simp

/-- A final Unknown means no confirmed run and an Unknown callback in the actual executed trace. -/
theorem accepts_unknown [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (unknown : IsUnknown State Symbol) (key : State) (term : Term Symbol) :
    accepts automaton unknown key term = .unknown ↔
      ¬ Accepts automaton key term ∧ ∃ event ∈ events automaton unknown key term, unknown event.1 event.2.1 event.2.2 = true := by
  have tracked := unshared_tracks automaton unknown term.height key term initial (by rfl)
  unfold Tracks at tracked
  unfold accepts finish
  rw [unshared_project, tracked]
  change (if AcceptanceDispatch.unshared automaton term.height key term then Guards.Verdict.yes
    else if (events automaton unknown key term).any (fun event => unknown event.1 event.2.1 event.2.2) then .unknown else .no) = .unknown ↔ _
  rw [← AcceptanceDispatch.acceptsBy_exact automaton key term]
  cases accepted : AcceptanceDispatch.unshared automaton term.height key term <;> simp [List.any_eq_true]

/-- A final No means no confirmed run and no Unknown among any callback the search evaluated. -/
theorem accepts_no [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (unknown : IsUnknown State Symbol) (key : State) (term : Term Symbol) :
    accepts automaton unknown key term = .no ↔
      ¬ Accepts automaton key term ∧ ∀ event ∈ events automaton unknown key term, unknown event.1 event.2.1 event.2.2 = false := by
  have tracked := unshared_tracks automaton unknown term.height key term initial (by rfl)
  unfold Tracks at tracked
  unfold accepts finish
  rw [unshared_project, tracked]
  change (if AcceptanceDispatch.unshared automaton term.height key term then Guards.Verdict.yes
    else if (events automaton unknown key term).any (fun event => unknown event.1 event.2.1 event.2.2) then .unknown else .no) = .no ↔ _
  rw [← AcceptanceDispatch.acceptsBy_exact automaton key term]
  cases accepted : AcceptanceDispatch.unshared automaton term.height key term <;> simp

/-- Stable three-way guard decisions, as returned by the refinement callback. -/
abbrev Callback (State Symbol : Type) := State → Edge State Symbol → Term Symbol → Guards.Verdict

/-- The actual callback's Unknown branch sets the global flag and returns false. -/
def unknownOf (callback : Callback State Symbol) : IsUnknown State Symbol :=
  fun key edge term => decide (callback key edge term = .unknown)

/-- The Boolean guard used for confirmed-run acceptance is exactly the callback's Yes branch. -/
def Compatible (automaton : Automaton State Symbol) (callback : Callback State Symbol) : Prop :=
  ∀ key edge, edge ∈ automaton key → ∀ term, edge.guard term = decide (callback key edge term = .yes)

/-- This interface condition identifies the tracked primitive with the source's three-way callback case. -/
theorem check_callback (automaton : Automaton State Symbol) (callback : Callback State Symbol)
    (compatible : Compatible automaton callback) (key : State) (edge : Edge State Symbol)
    (member : edge ∈ automaton key) (term : Term Symbol) (context : Context State Symbol) :
    (check (unknownOf callback) key edge term context).1 = decide (callback key edge term = .yes) ∧
      (check (unknownOf callback) key edge term context).2.unknown =
        (context.unknown || decide (callback key edge term = .unknown)) :=
  ⟨compatible key edge member term, rfl⟩

/-- A confirmed run checks the callback verdict itself at every transition. -/
inductive Confirmed (automaton : Automaton State Symbol) (callback : Callback State Symbol) : State → Term Symbol → Prop where
  | node (edge : Edge State Symbol) (children : List (Term Symbol)) (member : edge ∈ automaton key)
      (accepted : All₂ (Confirmed automaton callback) edge.children children)
      (guard : callback key edge (.node edge.label children) = .yes) :
      Confirmed automaton callback key (.node edge.label children)

/-- Callback compatibility equates Boolean accepting runs with explicitly confirmed guard runs. -/
theorem confirmed_exact (automaton : Automaton State Symbol) (callback : Callback State Symbol)
    (compatible : Compatible automaton callback) (key : State) (term : Term Symbol) :
    Accepts automaton key term ↔ Confirmed automaton callback key term := by
  constructor
  · intro accepted
    induction accepted using Accepts.rec
      (motive_2 := fun keys terms _ => All₂ (Confirmed automaton callback) keys terms) with
    | @node key edge children member accepted guard ih =>
        exact .node edge children member ih (of_decide_eq_true ((compatible key edge member _).symm.trans guard))
    | nil => exact .nil
    | cons head tail ih iht => exact .cons ih iht
  · intro accepted
    induction accepted using Confirmed.rec
      (motive_2 := fun keys terms _ => All₂ (Accepts automaton) keys terms) with
    | @node key edge children member accepted guard ih =>
        exact .node edge children member ih (by rw [compatible key edge member _, guard]; rfl)
    | nil => exact .nil
    | cons head tail ih iht => exact .cons ih iht

/-- Yes means an actual run with every executed guard confirmation equal to Yes. -/
theorem accepts_confirmed [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (callback : Callback State Symbol) (compatible : Compatible automaton callback) (key : State) (term : Term Symbol) :
    accepts automaton (unknownOf callback) key term = .yes ↔ Confirmed automaton callback key term :=
  (accepts_yes automaton (unknownOf callback) key term).trans (confirmed_exact automaton callback compatible key term)

/-- Unknown means no confirmed run and an actual Unknown callback in the executed search. -/
theorem accepts_unknown_callback [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (callback : Callback State Symbol) (compatible : Compatible automaton callback) (key : State) (term : Term Symbol) :
    accepts automaton (unknownOf callback) key term = .unknown ↔
      ¬ Confirmed automaton callback key term ∧
        ∃ event ∈ events automaton (unknownOf callback) key term,
          callback event.1 event.2.1 event.2.2 = .unknown := by
  rw [accepts_unknown, confirmed_exact automaton callback compatible]
  simp [unknownOf]

/-- No means that no confirmed run exists and every guard the search evaluated returned Yes or No. -/
theorem accepts_no_decided [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (callback : Callback State Symbol) (compatible : Compatible automaton callback) (key : State) (term : Term Symbol) :
    accepts automaton (unknownOf callback) key term = .no ↔
      ¬ Confirmed automaton callback key term ∧
        ∀ event ∈ events automaton (unknownOf callback) key term,
          callback event.1 event.2.1 event.2.2 = .yes ∨ callback event.1 event.2.1 event.2.2 = .no := by
  rw [accepts_no, confirmed_exact automaton callback compatible]
  constructor
  · rintro ⟨absent, decided⟩
    refine ⟨absent, ?_⟩
    intro event member
    have known := decided event member
    cases verdict : callback event.1 event.2.1 event.2.2 <;> simp_all [unknownOf]
  · rintro ⟨absent, decided⟩
    refine ⟨absent, ?_⟩
    intro event member
    rcases decided event member with yes | no <;> simp [unknownOf, *]

/-- Two root alternatives revisit one rejected child, which must keep its earlier Unknown effect. -/
def repeatedUnknown : Automaton Nat Nat := fun key =>
  if key = 0 then [⟨0, [1], fun _ => false⟩, ⟨0, [1], fun _ => false⟩]
  else [⟨1, [], fun _ => false⟩]

/-- The repeated child is checked once, cached as false, and the final answer remains Unknown. -/
theorem cached_unknown_retained :
    let term : Term Nat := .node 0 [.node 1 []]
    let unknown : IsUnknown Nat Nat := fun key _ _ => decide (key = 1)
    accepts repeatedUnknown unknown 0 term = .unknown ∧ (events repeatedUnknown unknown 0 term).length = 1 := by
  simp only [accepts, events, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero, Nat.zero_add]
  decide +kernel

/-- A second root alternative can confirm a run after an earlier child produced Unknown. -/
def laterConfirmed : Automaton Nat Nat := fun key =>
  if key = 0 then [⟨0, [1], fun _ => true⟩, ⟨0, [2], fun _ => true⟩]
  else [⟨1, [], fun _ => decide (key = 2)⟩]

/-- A confirmed run takes precedence while the earlier Unknown remains recorded. -/
theorem yes_after_unknown :
    let term : Term Nat := .node 0 [.node 1 []]
    let unknown : IsUnknown Nat Nat := fun key _ _ => decide (key = 1)
    accepts laterConfirmed unknown 0 term = .yes ∧
      (events laterConfirmed unknown 0 term).any (fun event => unknown event.1 event.2.1 event.2.2) = true := by
  simp only [accepts, events, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero, Nat.zero_add]
  decide +kernel

end MicroCFTA.AcceptanceEffects
