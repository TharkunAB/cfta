import MicroCFTA.AcceptanceCache

/-!
# Shared acceptance worker

The worker tries matching alternatives in order. Each child visit reads and
updates the position/state cache. Children and alternatives short-circuit.
The cache invariant is derived from the numbered subtree registry.
-/

namespace MicroCFTA.AcceptanceWorker
open Language NumberedTerms AcceptanceReference AcceptanceCache

/-- Run child actions from left to right and stop at the first false result. -/
def allM (check : α → σ → Bool × σ) : List α → σ → Bool × σ
  | [], state => (true, state)
  | first :: rest, state =>
      let result := check first state
      if result.1 then allM check rest result.2 else (false, result.2)

/-- Run alternative actions from left to right and stop at the first true result. -/
def anyM (check : α → σ → Bool × σ) : List α → σ → Bool × σ
  | [], state => (false, state)
  | first :: rest, state =>
      let result := check first state
      if result.1 then (true, result.2) else anyM check rest result.2

/-- Ordered child evaluation preserves the state invariant and complete conjunction semantics. -/
theorem allM_correct (check : α → σ → Bool × σ) (predicate : α → Bool) (invariant : σ → Prop)
    (items : List α) (state : σ) (valid : invariant state)
    (correct : ∀ item ∈ items, ∀ state, invariant state →
      (check item state).1 = predicate item ∧ invariant (check item state).2) :
    (allM check items state).1 = items.all predicate ∧ invariant (allM check items state).2 := by
  induction items generalizing state with
  | nil => exact ⟨rfl, valid⟩
  | cons first rest ih =>
      have head := correct first (by simp) state valid
      have tailCorrect : ∀ item ∈ rest, ∀ state, invariant state →
          (check item state).1 = predicate item ∧ invariant (check item state).2 :=
        fun item present => correct item (by simp [present])
      cases accepted : (check first state).1 with
      | false =>
          have rejected : predicate first = false := head.1.symm.trans accepted
          simpa [allM, accepted, rejected] using head.2
      | true =>
          have acceptedHead : predicate first = true := head.1.symm.trans accepted
          simpa [allM, accepted, acceptedHead] using ih (check first state).2 head.2 tailCorrect

/-- Ordered alternative evaluation preserves the state invariant and complete disjunction semantics. -/
theorem anyM_correct (check : α → σ → Bool × σ) (predicate : α → Bool) (invariant : σ → Prop)
    (items : List α) (state : σ) (valid : invariant state)
    (correct : ∀ item ∈ items, ∀ state, invariant state →
      (check item state).1 = predicate item ∧ invariant (check item state).2) :
    (anyM check items state).1 = items.any predicate ∧ invariant (anyM check items state).2 := by
  induction items generalizing state with
  | nil => exact ⟨rfl, valid⟩
  | cons first rest ih =>
      have head := correct first (by simp) state valid
      have tailCorrect : ∀ item ∈ rest, ∀ state, invariant state →
          (check item state).1 = predicate item ∧ invariant (check item state).2 :=
        fun item present => correct item (by simp [present])
      cases accepted : (check first state).1 with
      | false =>
          have rejected : predicate first = false := head.1.symm.trans accepted
          simpa [anyM, accepted, rejected] using ih (check first state).2 head.2 tailCorrect
      | true =>
          have acceptedHead : predicate first = true := head.1.symm.trans accepted
          simpa [anyM, accepted, acceptedHead] using head.2

/-- Child short-circuiting preserves any invariant maintained by each visited action. -/
theorem allM_preserves (check : α → σ → Bool × σ) (invariant : σ → Prop)
    (items : List α) (state : σ) (valid : invariant state)
    (preserves : ∀ item ∈ items, ∀ state, invariant state → invariant (check item state).2) :
    invariant (allM check items state).2 := by
  induction items generalizing state with
  | nil => exact valid
  | cons first rest ih =>
      have head := preserves first (by simp) state valid
      cases accepted : (check first state).1 with
      | false => simpa [allM, accepted] using head
      | true =>
          simpa [allM, accepted] using ih (check first state).2 head
            (fun item present => preserves item (by simp [present]))

/-- Alternative short-circuiting preserves any invariant maintained by each visited action. -/
theorem anyM_preserves (check : α → σ → Bool × σ) (invariant : σ → Prop)
    (items : List α) (state : σ) (valid : invariant state)
    (preserves : ∀ item ∈ items, ∀ state, invariant state → invariant (check item state).2) :
    invariant (anyM check items state).2 := by
  induction items generalizing state with
  | nil => exact valid
  | cons first rest ih =>
      have head := preserves first (by simp) state valid
      cases accepted : (check first state).1 with
      | true => simpa [anyM, accepted] using head
      | false =>
          simpa [anyM, accepted] using ih (check first state).2 head
            (fun item present => preserves item (by simp [present]))

/-- Zipped child actions implement precisely the source's zip conjunction. -/
theorem zipAll_eq_all (check : α → β → Bool) (left : List α) (right : List β) :
    zipAll check left right = (left.zip right).all (fun pair => check pair.1 pair.2) := by
  induction left generalizing right with
  | nil => simp [zipAll]
  | cons first rest ih => cases right <;> simp [zipAll, ih]

/-- Reading stored originals commutes with zip-based child checking. -/
theorem zipAll_original (check : State → Term Symbol → Bool) (keys : List State) (nodes : List (Positioned Symbol)) :
    zipAll check keys (nodes.map original) =
      (keys.zip nodes).all (fun pair => check pair.1 (original pair.2)) := by
  rw [zipAll_eq_all, List.zip_map_right, List.all_map]
  rfl

/-- The shared source worker evaluates matching alternatives and caches every child visit. -/
def shared [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol) :
    Nat → State → Positioned Symbol → Cache State → Bool × Cache State
  | 0, _, _, cache => (false, cache)
  | fuel + 1, key, .node _ term children, cache =>
      anyM (fun edge cache =>
        let checked := allM (fun pair cache => visit (shared automaton fuel) pair.1 pair.2 cache)
          (edge.children.zip children) cache
        if checked.1 then (edge.guard term, checked.2) else (false, checked.2))
        ((automaton key).filter (fun edge => matchesRoot edge term)) cache

/-- Shared search never deletes or changes a previously cached result. -/
theorem shared_extends [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (fuel : Nat) (key : State) (node : Positioned Symbol) (cache : Cache State) :
    Extends cache (shared automaton fuel key node cache).2 := by
  induction fuel generalizing key node cache with
  | zero => exact fun _ _ found => found
  | succ fuel ih =>
      cases node with
      | node index term children =>
          apply anyM_preserves _ (Extends cache) _ cache (fun _ _ found => found)
          intro edge _ current retained
          have checked := allM_preserves
            (fun pair state => visit (shared automaton fuel) pair.1 pair.2 state) (Extends cache)
            (edge.children.zip children) current retained
            (fun pair _ state previous => extends_trans cache state _ previous
              (visit_extends (shared automaton fuel) pair.1 pair.2 state (ih pair.1 pair.2 state)))
          dsimp only
          split <;> exact checked

/-- Once a child visit stores an answer, every later shared search retains it for an immediate cache hit. -/
theorem shared_retains_visit [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (fuel laterFuel : Nat) (key laterKey : State) (node laterNode : Positioned Symbol) (cache : Cache State) :
    (shared automaton laterFuel laterKey laterNode (visit (shared automaton fuel) key node cache).2).2
      (position node, key) = some (visit (shared automaton fuel) key node cache).1 :=
  shared_extends automaton laterFuel laterKey laterNode _ _ _ (visit_stored (shared automaton fuel) key node cache)

/-- Shared search computes exact acceptance and preserves all cache entries' meaning. -/
theorem shared_correct [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (fuel : Nat) (key : State) (node : Positioned Symbol) (registry : Nat → Option (Term Symbol))
    (cache : Cache State) (valid : Valid node) (registered : Registered registry node)
    (sound : Sound automaton registry cache) (enough : (original node).height ≤ fuel) :
    (shared automaton fuel key node cache).1 = truth automaton key (original node) ∧
      Sound automaton registry (shared automaton fuel key node cache).2 := by
  induction fuel generalizing key node cache with
  | zero => have positive := (original node).height_pos; omega
  | succ fuel ih =>
      cases node with
      | node index term children =>
          obtain ⟨⟨symbol, rfl⟩, childrenValid⟩ := valid
          have forestBound : forestHeight (children.map original) ≤ fuel := by
            simpa [original, Term.height, forestHeight] using enough
          have childCorrect (pair : State × Positioned Symbol) (present : pair.2 ∈ children)
              (cache : Cache State) (sound : Sound automaton registry cache) :
              (visit (shared automaton fuel) pair.1 pair.2 cache).1 = accept automaton fuel pair.1 (original pair.2) ∧
                Sound automaton registry (visit (shared automaton fuel) pair.1 pair.2 cache).2 := by
            have childBound : (original pair.2).height ≤ fuel :=
              Nat.le_trans (height_le_forestHeight (children.map original) (original pair.2)
                (List.mem_map.mpr ⟨pair.2, present, rfl⟩)) forestBound
            have childRegistered := registered_child registry index _ children registered pair.2 present
            have result := visit_correct automaton registry (shared automaton fuel) pair.1 pair.2 cache childRegistered sound
              (ih pair.1 pair.2 cache (valid_child children childrenValid pair.2 present) childRegistered sound childBound)
            exact ⟨result.1.trans (accept_truth automaton fuel pair.1 (original pair.2) childBound).symm, result.2⟩
          have edgeCorrect (edge : Edge State Symbol) (_member : edge ∈ (automaton key).filter
              (fun edge => matchesRoot edge (.node symbol (children.map original))))
              (cache : Cache State) (sound : Sound automaton registry cache) :
              (let checked := allM (fun pair cache => visit (shared automaton fuel) pair.1 pair.2 cache)
                (edge.children.zip children) cache
               if checked.1 then (edge.guard (.node symbol (children.map original)), checked.2) else (false, checked.2)).1 =
                (zipAll (accept automaton fuel) edge.children (children.map original) && edge.guard (.node symbol (children.map original))) ∧
              Sound automaton registry
                (let checked := allM (fun pair cache => visit (shared automaton fuel) pair.1 pair.2 cache)
                  (edge.children.zip children) cache
                 if checked.1 then (edge.guard (.node symbol (children.map original)), checked.2) else (false, checked.2)).2 := by
            have checked := allM_correct (fun pair cache => visit (shared automaton fuel) pair.1 pair.2 cache)
              (fun pair => accept automaton fuel pair.1 (original pair.2)) (Sound automaton registry)
              (edge.children.zip children) cache sound
              (fun pair member cache sound => childCorrect pair (List.of_mem_zip member).2 cache sound)
            rw [← zipAll_original] at checked
            cases returned : (allM (fun pair cache => visit (shared automaton fuel) pair.1 pair.2 cache)
                (edge.children.zip children) cache).1 <;> simp_all
          have alternatives := anyM_correct _ _ (Sound automaton registry)
            ((automaton key).filter (fun edge => matchesRoot edge (.node symbol (children.map original)))) cache sound edgeCorrect
          have result : (shared automaton (fuel + 1) key (.node index (.node symbol (children.map original)) children) cache).1 =
              accept automaton (fuel + 1) key (.node symbol (children.map original)) ∧
            Sound automaton registry (shared automaton (fuel + 1) key (.node index (.node symbol (children.map original)) children) cache).2 := by
            simpa [shared, accept, List.any_filter] using alternatives
          exact ⟨result.1.trans (accept_truth automaton (fuel + 1) key _ enough), result.2⟩

/-- Numbering and an empty cache establish every premise of exact shared acceptance. -/
theorem numbered_shared_exact [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (key : State) (term : Term Symbol) :
    (shared automaton term.height key (number term 0).2 (fun _ => none)).1 = true ↔ Accepts automaton key term := by
  have correct := shared_correct automaton term.height key (number term 0).2
    (fun index => (nodeEntries (number term 0).2).lookup index) (fun _ => none)
    (number_valid term 0) (number_registered term 0) (empty_sound _ _)
    (by rw [number_original]; exact Nat.le_refl _)
  rw [correct.1, number_original]
  exact accept_complete automaton term.height key term (Nat.le_refl _)

end MicroCFTA.AcceptanceWorker
