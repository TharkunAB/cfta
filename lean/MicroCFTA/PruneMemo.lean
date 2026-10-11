import MicroCFTA.PruneCandidates

/-!
# Memoized finite-plan graph specialization

The memo key contains the node and the observation plan. It does not contain
recursion fuel. A sufficient structural budget gives the same exact graph
variants, which justifies this key for a fixed graph interpretation.
-/
namespace MicroCFTA.PruneMemo
open Language Observation ObservationGraph

mutual
  /-- Compare finite observation tries without a graph or solver query. -/
  def planDecEq : (left right : Plan) → Decidable (left = right)
    | .node observation children, .node other rest =>
        if root : observation = other then
          match childrenDecEq children rest with
          | .isTrue same => .isTrue (by cases root; cases same; rfl)
          | .isFalse different => .isFalse (fun same => different (Plan.node.inj same).2)
        else .isFalse (fun same => root (Plan.node.inj same).1)
  termination_by left right => sizeOf left + sizeOf right
  decreasing_by all_goals simp_wf; all_goals omega

  /-- Compare sparse child-plan lists in their stored order. -/
  def childrenDecEq : (left right : List (Nat × Plan)) → Decidable (left = right)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse (by intro same; cases same)
    | _ :: _, [] => .isFalse (by intro same; cases same)
    | (key, child) :: children, (other, plan) :: rest =>
        if index : key = other then
          match planDecEq child plan with
          | .isFalse different => .isFalse (fun same => different (Prod.mk.inj (List.cons.inj same).1).2)
          | .isTrue same => match childrenDecEq children rest with
            | .isFalse different => .isFalse (fun equal => different (List.cons.inj equal).2)
            | .isTrue equal => .isTrue (by cases index; cases same; cases equal; rfl)
        else .isFalse (fun same => index (Prod.mk.inj (List.cons.inj same).1).1)
  termination_by left right => sizeOf left + sizeOf right
  decreasing_by all_goals simp_wf; all_goals omega
end

instance : DecidableEq Plan := planDecEq

/-- Child lookup returns a subtree of the finite plan representation. -/
theorem childAt_smaller (observation : Option Need) (children : List (Nat × Plan))
    (index : Nat) (child : Plan) (found : childAt index children = some child) :
    sizeOf child < sizeOf (Plan.node observation children) := by
  have member : (index, child) ∈ children := by
    induction children with
    | nil => simp [childAt] at found
    | cons entry rest ih =>
        rcases entry with ⟨key, plan⟩
        by_cases same : index = key
        · subst key
          have equal : plan = child := by simpa [childAt] using found
          subst plan
          simp
        · exact List.mem_cons_of_mem _ (ih (by simpa [childAt, same] using found))
  have bound := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec, Plan.node.sizeOf_spec] at bound ⊢
  omega

/-- Cartesian products depend only on the choices of entries actually present. -/
theorem products_congr (left right : α → List β) (items : List α)
    (same : ∀ item ∈ items, left item = right item) : products left items = products right items := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      simp only [products, same first (by simp), ih (fun item member => same item (by simp [member]))]

/-- One edge specialization uses only its actual requested child plans. -/
theorem edgeCandidates_congr (left right : Plan → State → List (Variant State Symbol Refinement))
    (observation : Option Need) (planned : List (Nat × Plan)) (edge : Edge State (Label Symbol Refinement))
    (same : ∀ index plan, childAt index planned = some plan → ∀ state, left plan state = right plan state) :
    edgeCandidates left (.node observation planned) edge = edgeCandidates right (.node observation planned) edge := by
  simp only [edgeCandidates]
  congr 1
  apply products_congr
  intro child _
  cases found : childAt child.2 planned with
  | none => simp [childChoices, found]
  | some plan => simp [childChoices, found, same child.2 plan found child.1]

/-- Every sufficient structural budget computes exactly the same variants, not only the same language. -/
theorem specialize_stable [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (fuel extra : Nat) (plan : Plan) (state : State)
    (enough : sizeOf plan ≤ fuel) (enoughExtra : sizeOf plan ≤ extra) :
    specialize automaton fuel plan state = specialize automaton extra plan state := by
  induction fuel generalizing extra plan state with
  | zero => cases plan; simp_all
  | succ fuel ih =>
      cases extra with
      | zero => cases plan; simp_all
      | succ extra =>
          cases plan with
          | node observation planned =>
              simp only [specialize]
              congr 1
              apply congrArg List.flatten
              apply List.map_congr_left
              intro edge _
              apply edgeCandidates_congr
              intro index child found key
              have smaller := childAt_smaller observation planned index child found
              exact ih extra child key (by omega) (by omega)

/-- Source-order traversal of a stateful list computation. -/
def walk (action : α → σ → β × σ) : List α → σ → List β × σ
  | [], state => ([], state)
  | item :: rest, state =>
      let first := action item state
      let later := walk action rest first.2
      (first.1 :: later.1, later.2)

/-- Exact per-item results and a state invariant compose through the complete traversal. -/
theorem walk_correct (action : α → σ → β × σ) (reference : α → β) (invariant : σ → Prop)
    (items : List α) (state : σ) (valid : invariant state)
    (correct : ∀ item ∈ items, ∀ state, invariant state →
      (action item state).1 = reference item ∧ invariant (action item state).2) :
    (walk action items state).1 = items.map reference ∧ invariant (walk action items state).2 := by
  induction items generalizing state with
  | nil => exact ⟨rfl, valid⟩
  | cons first rest ih =>
      have head := correct first (by simp) state valid
      have tail := ih (action first state).2 head.2 (fun item member => correct item (by simp [member]))
      exact ⟨by simpa only [walk, List.map_cons, head.1] using congrArg (reference first :: ·) tail.1, tail.2⟩

/-- Traversing children before forming their Cartesian product preserves source choice order. -/
theorem products_map (choice : α → List β) (items : List α) :
    products id (items.map choice) = products choice items := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp [products, ih]

/-- A split-memo key is precisely an original graph state and an observation plan. -/
abbrev Memo (State Symbol Refinement : Type) := State × Plan → Option (List (Variant State Symbol Refinement))

/-- Every stored result is the exact finite-plan specialization of the fixed graph. -/
def ValidMemo [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (memo : Memo State Symbol Refinement) : Prop :=
  ∀ key variants, memo key = some variants → variants = specialize automaton (sizeOf key.2) key.2 key.1

/-- Store a completed split result after all nested child queries return. -/
def store [DecidableEq State] (memo : Memo State Symbol Refinement) (key : State × Plan)
    (variants : List (Variant State Symbol Refinement)) : Memo State Symbol Refinement :=
  fun query => if query = key then some variants else memo query

/-- A newly proved split result preserves every old memo relation. -/
theorem store_valid [DecidableEq State] [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (memo : Memo State Symbol Refinement)
    (valid : ValidMemo automaton memo) (key : State × Plan) (variants : List (Variant State Symbol Refinement))
    (correct : variants = specialize automaton (sizeOf key.2) key.2 key.1) :
    ValidMemo automaton (store memo key variants) := by
  intro query values found
  by_cases same : query = key
  · subst query
    have equal : variants = values := by simpa [store] using found
    exact equal ▸ correct
  · exact valid query values (by simpa [store, same] using found)

/-- The source specialization schedule with nested memo reads and writes. -/
def specializeMemo [DecidableEq State] [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) :
    Nat → Plan → State → Memo State Symbol Refinement → List (Variant State Symbol Refinement) × Memo State Symbol Refinement
  | fuel, plan, state, memo =>
      match memo (state, plan) with
      | some variants => (variants, memo)
      | none =>
          match fuel with
          | 0 => let variants := [originalVariant state]; (variants, store memo (state, plan) variants)
          | fuel + 1 =>
              match plan with
              | .node observation planned =>
                  let candidates := walk (fun edge memo =>
                    let choices := walk (fun child memo =>
                      match childAt child.2 planned with
                      | none => ([originalVariant child.1], memo)
                      | some plan => specializeMemo automaton fuel plan child.1 memo) edge.children.zipIdx memo
                    ((products id choices.1).map (assemble (.node observation planned) edge), choices.2)) (automaton state) memo
                  let variants := groupCandidates (.node observation planned) candidates.1.flatten
                  (variants, store candidates.2 (state, .node observation planned) variants)

/-- Memo lookup and all nested writes preserve exact specialization and the complete memo invariant. -/
theorem specializeMemo_correct [DecidableEq State] [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (fuel : Nat) (plan : Plan) (state : State)
    (memo : Memo State Symbol Refinement) (enough : sizeOf plan ≤ fuel) (valid : ValidMemo automaton memo) :
    (specializeMemo automaton fuel plan state memo).1 = specialize automaton fuel plan state ∧
      ValidMemo automaton (specializeMemo automaton fuel plan state memo).2 := by
  induction fuel generalizing plan state memo with
  | zero => cases plan; simp_all
  | succ fuel ih =>
      cases found : memo (state, plan) with
      | some variants =>
          have correct := (valid _ _ found).trans (specialize_stable automaton (sizeOf plan) (fuel + 1) plan state (Nat.le_refl _) enough)
          cases plan with
          | node observation planned => simpa only [specializeMemo, found] using And.intro correct valid
      | none =>
          cases plan with
          | node observation planned =>
              have childCorrect (child : State × Nat) (current : Memo State Symbol Refinement) (good : ValidMemo automaton current) :
                  (match childAt child.2 planned with
                   | none => ([originalVariant child.1], current)
                   | some plan => specializeMemo automaton fuel plan child.1 current).1 =
                      childChoices (specialize automaton fuel) planned child ∧
                    ValidMemo automaton (match childAt child.2 planned with
                      | none => ([originalVariant child.1], current)
                      | some plan => specializeMemo automaton fuel plan child.1 current).2 := by
                cases childFound : childAt child.2 planned with
                | none => exact ⟨by simp [childChoices, childFound], good⟩
                | some childPlan =>
                    have smaller := childAt_smaller observation planned child.2 childPlan childFound
                    simpa [childChoices, childFound] using ih childPlan child.1 current (by omega) good
              have edgeCorrect (edge : Edge State (Label Symbol Refinement)) (current : Memo State Symbol Refinement)
                  (good : ValidMemo automaton current) :
                  (let choices := walk (fun child memo => match childAt child.2 planned with
                      | none => ([originalVariant child.1], memo)
                      | some plan => specializeMemo automaton fuel plan child.1 memo) edge.children.zipIdx current
                   ((products id choices.1).map (assemble (.node observation planned) edge), choices.2)).1 =
                      edgeCandidates (specialize automaton fuel) (.node observation planned) edge ∧
                    ValidMemo automaton (walk (fun child memo => match childAt child.2 planned with
                      | none => ([originalVariant child.1], memo)
                      | some plan => specializeMemo automaton fuel plan child.1 memo) edge.children.zipIdx current).2 := by
                have children := walk_correct _ (childChoices (specialize automaton fuel) planned) (ValidMemo automaton)
                  edge.children.zipIdx current good (fun child _ => childCorrect child)
                refine ⟨?_, children.2⟩
                dsimp only
                rw [children.1, products_map]
                rfl
              have edges := walk_correct _ (edgeCandidates (specialize automaton fuel) (.node observation planned))
                (ValidMemo automaton) (automaton state) memo valid (fun edge _ => edgeCorrect edge)
              have result : (specializeMemo automaton (fuel + 1) (.node observation planned) state memo).1 =
                  specialize automaton (fuel + 1) (.node observation planned) state := by
                simp only [specializeMemo, found, specialize]
                rw [edges.1]
                rfl
              refine ⟨result, ?_⟩
              simp only [specializeMemo, found]
              apply store_valid automaton _ edges.2
              simpa only [specializeMemo, found] using result.trans (specialize_stable automaton (fuel + 1) (sizeOf (Plan.node observation planned))
                (.node observation planned) state enough (Nat.le_refl _))


/-- Structural plan size reaches every requested observation. -/
theorem size_sufficient (plan : Plan) : PlanBound (sizeOf plan) plan := by
  intro path need requested
  induction path generalizing plan with
  | nil => cases plan; simp only [Plan.node.sizeOf_spec, List.length_nil]; omega
  | cons index rest ih =>
      cases plan with
      | node observation planned =>
          obtain ⟨child, found, requested⟩ := Option.bind_eq_some_iff.mp requested
          have bound := ih child requested
          have smaller := childAt_smaller observation planned index child found
          simp only [List.length_cons]
          omega

/-- The public memoized specialization preserves all concrete terms and every planned observation. -/
theorem specializeMemo_exact [DecidableEq State] [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (plan : Plan) (state : State)
    (memo : Memo State Symbol Refinement) (valid : ValidMemo automaton memo) :
    (∀ term, (∃ variant ∈ (specializeMemo automaton (sizeOf plan) plan state memo).1,
      AcceptsNode automaton variant.node term) ↔ Accepts automaton state term) ∧
    (∀ variant ∈ (specializeMemo automaton (sizeOf plan) plan state memo).1,
      ValidVariant automaton plan variant) ∧
    ValidMemo automaton (specializeMemo automaton (sizeOf plan) plan state memo).2 := by
  have correct := specializeMemo_correct automaton (sizeOf plan) plan state memo (Nat.le_refl _) valid
  rw [correct.1]
  exact ⟨fun term => specialize_cover automaton _ plan state term,
    fun variant present => specialize_valid automaton _ plan (size_sufficient plan) state variant present, correct.2⟩

/-- The empty split memo establishes its entire correctness invariant. -/
theorem empty_valid [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) : ValidMemo automaton (fun _ => none) := by
  intro key variants found
  cases found

/-- Existing memo entries are retained as exact values. -/
def Extends (before after : Memo State Symbol Refinement) : Prop :=
  ∀ key variants, before key = some variants → after key = some variants

/-- Source-order traversal composes memo retention. -/
theorem walk_extends (action : α → Memo State Symbol Refinement → β × Memo State Symbol Refinement)
    (items : List α) (memo : Memo State Symbol Refinement)
    (retains : ∀ item ∈ items, ∀ memo, Extends memo (action item memo).2) :
    Extends memo (walk action items memo).2 := by
  induction items generalizing memo with
  | nil => exact fun _ _ found => found
  | cons first rest ih =>
      have head := retains first (by simp) memo
      have tail := ih (action first memo).2 (fun item member => retains item (by simp [member]))
      exact fun key variants found => tail key variants (head key variants found)

/-- Nested specialization never deletes or changes any existing split-memo entry. -/
theorem specializeMemo_extends [DecidableEq State] [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (fuel : Nat) (plan : Plan) (state : State)
    (memo : Memo State Symbol Refinement) : Extends memo (specializeMemo automaton fuel plan state memo).2 := by
  induction fuel generalizing plan state memo with
  | zero =>
      cases plan with
      | node observation planned =>
          cases cached : memo (state, .node observation planned) with
          | some variants => simpa [specializeMemo, cached] using (show Extends memo memo from fun _ _ found => found)
          | none =>
              intro key variants found
              have different : key ≠ (state, .node observation planned) := by intro same; subst key; simp_all
              simpa [specializeMemo, cached, store, different] using found
  | succ fuel ih =>
      cases plan with
      | node observation planned =>
          cases cached : memo (state, .node observation planned) with
          | some variants => simpa [specializeMemo, cached] using (show Extends memo memo from fun _ _ found => found)
          | none =>
              have children (edge : Edge State (Label Symbol Refinement)) (current : Memo State Symbol Refinement) :
                  Extends current (walk (fun child memo => match childAt child.2 planned with
                    | none => ([originalVariant child.1], memo)
                    | some plan => specializeMemo automaton fuel plan child.1 memo) edge.children.zipIdx current).2 := by
                apply walk_extends
                intro child _ next
                cases found : childAt child.2 planned with
                | none => exact fun _ _ found => found
                | some plan => exact ih plan child.1 next
              have edges := walk_extends (fun edge memo =>
                let choices := walk (fun child memo => match childAt child.2 planned with
                  | none => ([originalVariant child.1], memo)
                  | some plan => specializeMemo automaton fuel plan child.1 memo) edge.children.zipIdx memo
                ((products id choices.1).map (assemble (.node observation planned) edge), choices.2))
                (automaton state) memo (fun edge _ => children edge)
              intro key variants found
              have different : key ≠ (state, .node observation planned) := by intro same; subst key; simp_all
              simpa only [specializeMemo, cached, store, ite_eq_right different] using edges key variants found

/-- A repeated query is a direct cache hit with no child traversal or new write. -/
theorem specializeMemo_hit [DecidableEq State] [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (fuel : Nat) (plan : Plan) (state : State)
    (memo : Memo State Symbol Refinement) (variants : List (Variant State Symbol Refinement))
    (found : memo (state, plan) = some variants) : specializeMemo automaton fuel plan state memo = (variants, memo) := by
  cases fuel <;> cases plan <;> simp [specializeMemo, found]

/-- A successful call leaves its exact returned variants available for later reuse. -/
theorem specializeMemo_stored [DecidableEq State] [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (fuel : Nat) (plan : Plan) (state : State)
    (memo : Memo State Symbol Refinement) :
    (specializeMemo automaton fuel plan state memo).2 (state, plan) =
      some (specializeMemo automaton fuel plan state memo).1 := by
  cases fuel <;> cases plan <;> rename_i observation planned <;>
    cases found : memo (state, .node observation planned) <;> simp [specializeMemo, found, store]


/-- A cached variant's stored-view query equals the complete-term query. -/
theorem memo_verdict_exact [DecidableEq State] [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (queries : Queries Refinement)
    (guard : Guards.Guard (Atom Refinement)) (state : State) (memo : Memo State Symbol Refinement)
    (valid : ValidMemo automaton memo) (variant : Variant State Symbol Refinement)
    (present : variant ∈ (specializeMemo automaton (sizeOf (guardPlan guard)) (guardPlan guard) state memo).1)
    (term : Term (Label Symbol Refinement)) (accepted : AcceptsNode automaton variant.node term) :
    variantVerdict queries guard variant = verdict queries guard term := by
  have exactView := ((specializeMemo_exact automaton (guardPlan guard) state memo valid).2.1 variant present).2 term accepted
  apply guardQuery_ext
  intro path used
  have request : lookup (guardPlan guard) path = some .refinement := by simp [lookup_guardPlan, used]
  simp only [refinementView, exactView]
  rw [signature_refinement (guardPlan guard) term path request]
  cases refinementAt term path <;> rfl

mutual
  /-- Compute a structural recursion budget for the finite observation trie. -/
  def planSize : Plan → Nat
    | .node observation children => 1 + (if observation.isSome then 2 else 1) + childrenSize children
  /-- Count the stored sparse child-plan representation. -/
  def childrenSize : List (Nat × Plan) → Nat
    | [] => 1
    | (index, child) :: rest => 1 + (1 + index + planSize child) + childrenSize rest
end

mutual
  /-- The executable plan budget equals the structural bound used by the proof. -/
  theorem planSize_correct (plan : Plan) : planSize plan = sizeOf plan := by
    cases plan with
    | node observation children =>
        cases observation with
        | none => simp [planSize, childrenSize_correct]
        | some need => cases need <;> simp [planSize, childrenSize_correct]
  /-- Child representation counting agrees with its structural measure. -/
  theorem childrenSize_correct (children : List (Nat × Plan)) : childrenSize children = sizeOf children := by
    cases children with
    | nil => rfl
    | cons first rest => cases first; simp [childrenSize, planSize_correct, childrenSize_correct]
end

/-- Run the complete candidate pass after nested memoized specialization. -/
def pruneMemo [DecidableEq State] [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (queries : Queries Refinement)
    (guard : Guards.Guard (Atom Refinement)) (state : State) (test : Term (Label Symbol Refinement) → Bool)
    (ambiguous : Variant State Symbol Refinement → Bool) (memo : Memo State Symbol Refinement) :
    Except PruneSchedule.Error (List (ObservationGraph.Node State (Label Symbol Refinement)) × Memo State Symbol Refinement) :=
  let specialized := specializeMemo automaton (planSize (guardPlan guard)) (guardPlan guard) state memo
  let candidates := specialized.1.map (fun variant =>
    (⟨variant.node, variantVerdict queries guard variant, ambiguous variant⟩ : PruneSchedule.Candidate _))
  match PruneSchedule.check (guardedRoot automaton state test) [] candidates with
  | .error error => .error error
  | .ok result => .ok (result, specialized.2)

/-- Memoized splitting and every successful query/fallback branch preserve the declared language and memo invariant. -/
theorem pruneMemo_exact [DecidableEq State] [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (queries : Queries Refinement)
    (guard : Guards.Guard (Atom Refinement)) (state : State) (test : Term (Label Symbol Refinement) → Bool)
    (sound : ∀ term, Guards.Supports (verdict queries guard term) (test term = true))
    (ambiguous : Variant State Symbol Refinement → Bool) (memo : Memo State Symbol Refinement)
    (valid : ValidMemo automaton memo) (result : List (ObservationGraph.Node State (Label Symbol Refinement)))
    (next : Memo State Symbol Refinement) (success : pruneMemo automaton queries guard state test ambiguous memo = .ok (result, next)) :
    (∀ term, PruneCandidates.Denotes (AcceptsNode automaton) result term ↔
      AcceptsNode automaton (guardedRoot automaton state test) term) ∧ ValidMemo automaton next ∧ Extends memo next := by
  let variants := (specializeMemo automaton (sizeOf (guardPlan guard)) (guardPlan guard) state memo).1
  let candidates : List (PruneSchedule.Candidate (ObservationGraph.Node State (Label Symbol Refinement))) :=
    variants.map (fun variant => ⟨variant.node, variantVerdict queries guard variant, ambiguous variant⟩)
  have specialized := specializeMemo_exact automaton (guardPlan guard) state memo valid
  cases checked : PruneSchedule.check (guardedRoot automaton state test) [] candidates with
  | error failure =>
      dsimp only [candidates, variants] at checked
      simp [pruneMemo, planSize_correct, checked] at success
  | ok retained =>
      dsimp only [candidates, variants] at checked
      have resultEq : retained = result ∧
          (specializeMemo automaton (sizeOf (guardPlan guard)) (guardPlan guard) state memo).2 = next := by
        simpa only [pruneMemo, planSize_correct, checked, Except.ok.injEq, Prod.mk.injEq] using success
      obtain ⟨rfl, rfl⟩ := resultEq
      refine ⟨?_, specialized.2.2, specializeMemo_extends automaton _ _ state memo⟩
      intro term
      apply PruneCandidates.check_exact (AcceptsNode automaton)
        (fun candidate term => AcceptsNode automaton candidate.edge term ∧ test term = true)
        _ candidates _ _ _ retained checked term
      · intro term
        rw [guardedRoot_accepts_iff]
        constructor
        · rintro ⟨candidate, member, accepted, proved⟩
          obtain ⟨variant, present, rfl⟩ := List.mem_map.mp member
          exact ⟨(specialized.1 term).mp ⟨variant, present, accepted⟩, proved⟩
        · rintro ⟨accepted, proved⟩
          obtain ⟨variant, present, run⟩ := (specialized.1 term).mpr accepted
          exact ⟨_, List.mem_map.mpr ⟨variant, present, rfl⟩, run, proved⟩
      · intro candidate member proved term
        obtain ⟨variant, present, rfl⟩ := List.mem_map.mp member
        constructor
        · intro accepted
          have decision : verdict queries guard term = .yes :=
            (memo_verdict_exact automaton queries guard state memo valid variant present term accepted).symm.trans proved
          exact ⟨accepted, by simpa [decision, Guards.Supports] using sound term⟩
        · exact And.left
      · intro candidate member disproved term ⟨accepted, proved⟩
        obtain ⟨variant, present, rfl⟩ := List.mem_map.mp member
        have decision : verdict queries guard term = .no :=
          (memo_verdict_exact automaton queries guard state memo valid variant present term accepted).symm.trans disproved
        have falseGuard : test term ≠ true := by simpa [decision, Guards.Supports] using sound term
        exact falseGuard proved

end MicroCFTA.PruneMemo
