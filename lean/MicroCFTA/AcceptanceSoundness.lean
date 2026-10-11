import MicroCFTA.AcceptanceEffects

/-!
# Semantic soundness of decided acceptance results

A stable callback gives sound Yes and No results. Unknown gives no semantic
evidence. A rejected cache entry carries a refutation whenever the global
Unknown flag is false. This invariant permits sound rejection without any
assumption that an unvisited guard has a decided result.
-/

namespace MicroCFTA.AcceptanceSoundness
open Language NumberedTerms AcceptanceReference AcceptanceCache AcceptanceWorker AcceptanceDispatch AcceptanceEffects

/-- Semantic guards may be propositions that the callback cannot decide. -/
abbrev Meaning (State Symbol : Type) := State → Edge State Symbol → Term Symbol → Prop

/-- A semantic run uses the declared transitions and the meaning of each guard. -/
inductive Run (automaton : Automaton State Symbol) (meaning : Meaning State Symbol) : State → Term Symbol → Prop where
  | node (edge : Edge State Symbol) (children : List (Term Symbol)) (member : edge ∈ automaton key)
      (accepted : All₂ (Run automaton meaning) edge.children children)
      (guard : meaning key edge (.node edge.label children)) : Run automaton meaning key (.node edge.label children)

/-- A confirmed run is sound when every Yes callback gives a valid semantic guard. -/
theorem confirmed_sound (automaton : Automaton State Symbol) (callback : Callback State Symbol)
    (meaning : Meaning State Symbol)
    (sound : ∀ key edge, edge ∈ automaton key → ∀ term, callback key edge term = .yes → meaning key edge term)
    (key : State) (term : Term Symbol) (confirmed : Confirmed automaton callback key term) : Run automaton meaning key term := by
  induction confirmed using Confirmed.rec
    (motive_2 := fun keys terms _ => All₂ (Run automaton meaning) keys terms) with
  | @node key edge children member accepted guard ih => exact .node edge children member ih (sound key edge member _ guard)
  | nil => exact .nil
  | cons head tail ih iht => exact .cons ih iht

/-- The public Yes result has semantic soundness under the explicit callback contract. -/
theorem yes_sound [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (callback : Callback State Symbol) (compatible : Compatible automaton callback) (meaning : Meaning State Symbol)
    (sound : ∀ key edge, edge ∈ automaton key → ∀ term, callback key edge term = .yes → meaning key edge term)
    (key : State) (term : Term Symbol) (accepted : accepts automaton (unknownOf callback) key term = .yes) :
    Run automaton meaning key term :=
  confirmed_sound automaton callback meaning sound key term ((accepts_confirmed automaton callback compatible key term).mp accepted)

/-- A later unset flag implies an earlier unset flag when the tracked call list only grows. -/
theorem earlier_decided (unknown : IsUnknown State Symbol) (before after : Context State Symbol)
    (left : Tracks unknown before) (right : Tracks unknown after) (retains : Retains before after)
    (decided : after.unknown = false) : before.unknown = false := by
  cases previous : before.unknown with
  | false => rfl
  | true => have contradiction := unknown_monotone unknown before after left right retains previous; simp_all

/-- A computation preserves its invariant and can refute its proposition when it returns a decided false. -/
def Checked (unknown : IsUnknown State Symbol) (invariant : Context State Symbol → Prop)
    (proposition : Prop) (before : Context State Symbol) (result : Bool × Context State Symbol) : Prop :=
  invariant result.2 ∧ Tracks unknown result.2 ∧ Retains before result.2 ∧
    (result.2.unknown = false → result.1 = false → ¬ proposition)

/-- Ordered conjunction carries a refutation from the first rejected child. -/
theorem allM_checked (unknown : IsUnknown State Symbol) (invariant : Context State Symbol → Prop)
    (action : α → Context State Symbol → Bool × Context State Symbol) (proposition : α → Prop)
    (items : List α) (before : Context State Symbol) (valid : invariant before) (tracked : Tracks unknown before)
    (checked : ∀ item ∈ items, ∀ context, invariant context → Tracks unknown context →
      Checked unknown invariant (proposition item) context (action item context)) :
    Checked unknown invariant (∀ item ∈ items, proposition item) before (allM action items before) := by
  induction items generalizing before with
  | nil => exact ⟨valid, tracked, ⟨[], by simp [allM]⟩, by simp [allM]⟩
  | cons first rest ih =>
      have head := checked first (by simp) before valid tracked
      cases answer : (action first before).1 with
      | false =>
          simp only [allM, answer, Bool.false_eq_true, ↓reduceIte]
          refine ⟨head.1, head.2.1, head.2.2.1, ?_⟩
          intro decided _ all
          exact head.2.2.2 decided answer (all first (by simp))
      | true =>
          have tail := ih (action first before).2 head.1 head.2.1
            (fun item member context valid tracked => checked item (by simp [member]) context valid tracked)
          simp only [allM, answer, ↓reduceIte]
          refine ⟨tail.1, tail.2.1, head.2.2.1.trans tail.2.2.1, ?_⟩
          intro decided rejected all
          exact tail.2.2.2 decided rejected (fun item member => all item (by simp [member]))

/-- Ordered disjunction retains every earlier refutation when all alternatives fail without Unknown. -/
theorem anyM_checked (unknown : IsUnknown State Symbol) (invariant : Context State Symbol → Prop)
    (action : α → Context State Symbol → Bool × Context State Symbol) (proposition : α → Prop)
    (items : List α) (before : Context State Symbol) (valid : invariant before) (tracked : Tracks unknown before)
    (checked : ∀ item ∈ items, ∀ context, invariant context → Tracks unknown context →
      Checked unknown invariant (proposition item) context (action item context)) :
    Checked unknown invariant (∃ item ∈ items, proposition item) before (anyM action items before) := by
  induction items generalizing before with
  | nil => exact ⟨valid, tracked, ⟨[], by simp [anyM]⟩, by simp⟩
  | cons first rest ih =>
      have head := checked first (by simp) before valid tracked
      cases answer : (action first before).1 with
      | true =>
          simp only [anyM, answer, ↓reduceIte]
          exact ⟨head.1, head.2.1, head.2.2.1, by simp⟩
      | false =>
          have tail := ih (action first before).2 head.1 head.2.1
            (fun item member context valid tracked => checked item (by simp [member]) context valid tracked)
          simp only [anyM, answer, Bool.false_eq_true, ↓reduceIte]
          refine ⟨tail.1, tail.2.1, head.2.2.1.trans tail.2.2.1, ?_⟩
          intro decided rejected ⟨item, member, proof⟩
          rcases List.mem_cons.mp member with rfl | later
          · exact head.2.2.2 (earlier_decided unknown _ _ head.2.1 tail.2.1 tail.2.2.1 decided) answer proof
          · exact tail.2.2.2 decided rejected ⟨item, later, proof⟩


/-- A false cached answer refutes its registered subtree if no executed query was Unknown. -/
def Refutes (automaton : Automaton State Symbol) (meaning : Meaning State Symbol)
    (registry : Nat → Option (Term Symbol)) (context : Context State Symbol) : Prop :=
  ∀ index key, context.cache (index, key) = some false → context.unknown = false →
    ∀ term, registry index = some term → ¬ Run automaton meaning key term

/-- The empty local table satisfies the refutation invariant. -/
theorem empty_refutes (automaton : Automaton State Symbol) (meaning : Meaning State Symbol)
    (registry : Nat → Option (Term Symbol)) (context : Context State Symbol) :
    Refutes automaton meaning registry {context with cache := fun _ => none} := by
  intro index key found
  cases found

/-- A callback either supplies a sound refutation or sets the global Unknown flag. -/
theorem check_checked (automaton : Automaton State Symbol) (callback : Callback State Symbol)
    (compatible : Compatible automaton callback) (meaning : Meaning State Symbol)
    (noSound : ∀ key edge, edge ∈ automaton key → ∀ term, callback key edge term = .no → ¬ meaning key edge term)
    (registry : Nat → Option (Term Symbol)) (key : State) (edge : Edge State Symbol) (member : edge ∈ automaton key)
    (term : Term Symbol) (context : Context State Symbol) (safe : Refutes automaton meaning registry context)
    (tracked : Tracks (unknownOf callback) context) :
    Checked (unknownOf callback) (Refutes automaton meaning registry) (meaning key edge term)
      context (check (unknownOf callback) key edge term context) := by
  refine ⟨?_, check_tracks _ _ _ _ _ tracked, check_retains _ _ _ _ _, ?_⟩
  · intro index state found decided value registered
    exact safe index state found (by simpa [check] using (Bool.or_eq_false_iff.mp decided).1) value registered
  · intro decided rejected
    have notUnknown : callback key edge term ≠ .unknown := by
      have := (Bool.or_eq_false_iff.mp decided).2
      simpa [unknownOf] using this
    have notYes : callback key edge term ≠ .yes := by
      have := (compatible key edge member term).symm.trans rejected
      simpa using this
    have verdict : callback key edge term = .no := by
      cases answer : callback key edge term <;> simp_all
    exact noSound key edge member term verdict

/-- Inserting a fresh answer preserves refutations, including when that answer is false. -/
theorem insert_refutes [DecidableEq State] (automaton : Automaton State Symbol) (meaning : Meaning State Symbol)
    (registry : Nat → Option (Term Symbol)) (key : State) (node : Positioned Symbol)
    (context : Context State Symbol) (answer : Bool) (safe : Refutes automaton meaning registry context)
    (registered : Registered registry node)
    (refuted : context.unknown = false → answer = false → ¬ Run automaton meaning key (original node)) :
    Refutes automaton meaning registry {context with cache := insert context.cache (position node) key answer} := by
  intro index state found decided term stored
  by_cases same : (index, state) = (position node, key)
  · cases same
    have rejected : answer = false := by simpa [AcceptanceCache.insert] using found
    have equal : term = original node := Option.some.inj (stored.symm.trans (registered_root registry node registered))
    simpa [equal] using refuted decided rejected
  · exact safe index state (by simpa [AcceptanceCache.insert, same] using found) decided term stored

/-- A cache hit uses its stored refutation; a cache miss records the computed refutation. -/
theorem visit_checked [DecidableEq State] (automaton : Automaton State Symbol) (meaning : Meaning State Symbol)
    (unknown : IsUnknown State Symbol) (registry : Nat → Option (Term Symbol))
    (compute : State → Positioned Symbol → Context State Symbol → Bool × Context State Symbol)
    (key : State) (node : Positioned Symbol) (context : Context State Symbol)
    (registered : Registered registry node) (safe : Refutes automaton meaning registry context)
    (tracked : Tracks unknown context)
    (computed : Checked unknown (Refutes automaton meaning registry) (Run automaton meaning key (original node))
      context (compute key node context)) :
    Checked unknown (Refutes automaton meaning registry) (Run automaton meaning key (original node))
      context (AcceptanceEffects.visit compute key node context) := by
  cases found : context.cache (position node, key) with
  | none =>
      simp only [AcceptanceEffects.visit, found]
      exact ⟨insert_refutes automaton meaning registry key node _ _ computed.1 registered computed.2.2.2,
        computed.2.1, computed.2.2.1, computed.2.2.2⟩
  | some answer =>
      simp only [AcceptanceEffects.visit, found]
      refine ⟨safe, tracked, ⟨[], by simp⟩, ?_⟩
      intro decided rejected
      change answer = false at rejected
      exact safe _ key (by simpa [rejected] using found) decided _ (registered_root registry node registered)

/-- A complete pointwise relation applies to every pair visited by the source zip loop. -/
theorem all₂_zip_member (relation : α → β → Prop) (keys : List α) (terms : List β)
    (related : All₂ relation keys terms) (pair : α × β) (member : pair ∈ keys.zip terms) : relation pair.1 pair.2 := by
  induction related with
  | nil => simp at member
  | @cons key term keys terms head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact ih later

/-- Semantic runs expose one matching transition and its complete child derivations. -/
theorem run_node_iff (automaton : Automaton State Symbol) (meaning : Meaning State Symbol)
    (key : State) (symbol : Symbol) (children : List (Term Symbol)) :
    Run automaton meaning key (.node symbol children) ↔
      ∃ edge ∈ automaton key, edge.label = symbol ∧ All₂ (Run automaton meaning) edge.children children ∧
        meaning key edge (.node symbol children) := by
  constructor
  · intro run
    cases run with
    | node edge children member accepted guard => exact ⟨edge, member, rfl, accepted, guard⟩
  · rintro ⟨edge, member, symbolMatches, accepted, guard⟩
    subst symbol
    exact .node edge children member accepted guard


/-- Shared search preserves cached refutations and rejects only impossible semantic runs when decided. -/
theorem shared_checked [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (callback : Callback State Symbol) (compatible : Compatible automaton callback) (meaning : Meaning State Symbol)
    (noSound : ∀ key edge, edge ∈ automaton key → ∀ term, callback key edge term = .no → ¬ meaning key edge term)
    (fuel : Nat) (key : State) (node : Positioned Symbol) (registry : Nat → Option (Term Symbol))
    (context : Context State Symbol) (valid : Valid node) (registered : Registered registry node)
    (safe : Refutes automaton meaning registry context) (tracked : Tracks (unknownOf callback) context)
    (enough : (original node).height ≤ fuel) :
    Checked (unknownOf callback) (Refutes automaton meaning registry) (Run automaton meaning key (original node))
      context (AcceptanceEffects.shared automaton (unknownOf callback) fuel key node context) := by
  induction fuel generalizing key node context with
  | zero => have positive := (original node).height_pos; omega
  | succ fuel ih =>
      cases node with
      | node index term children =>
          obtain ⟨⟨symbol, rfl⟩, childrenValid⟩ := valid
          have forestBound : forestHeight (children.map original) ≤ fuel := by
            simpa [original, Term.height, forestHeight] using enough
          have childChecked (pair : State × Positioned Symbol) (present : pair.2 ∈ children)
              (current : Context State Symbol) (safe : Refutes automaton meaning registry current)
              (tracked : Tracks (unknownOf callback) current) :
              Checked (unknownOf callback) (Refutes automaton meaning registry)
                (Run automaton meaning pair.1 (original pair.2)) current
                (AcceptanceEffects.visit (AcceptanceEffects.shared automaton (unknownOf callback) fuel) pair.1 pair.2 current) := by
            have childBound : (original pair.2).height ≤ fuel :=
              Nat.le_trans (height_le_forestHeight (children.map original) (original pair.2)
                (List.mem_map.mpr ⟨pair.2, present, rfl⟩)) forestBound
            have childRegistered := registered_child registry index _ children registered pair.2 present
            exact visit_checked automaton meaning (unknownOf callback) registry _ pair.1 pair.2 current childRegistered safe tracked
              (ih pair.1 pair.2 current (valid_child children childrenValid pair.2 present) childRegistered safe tracked childBound)
          have edgeChecked (edge : Edge State Symbol) (member : edge ∈ (automaton key).filter
              (fun edge => matchesRoot edge (.node symbol (children.map original))))
              (current : Context State Symbol) (safe : Refutes automaton meaning registry current)
              (tracked : Tracks (unknownOf callback) current) :
              Checked (unknownOf callback) (Refutes automaton meaning registry)
                ((∀ pair ∈ edge.children.zip children, Run automaton meaning pair.1 (original pair.2)) ∧
                  meaning key edge (.node symbol (children.map original))) current
                (let checked := allM (fun pair context =>
                    AcceptanceEffects.visit (AcceptanceEffects.shared automaton (unknownOf callback) fuel) pair.1 pair.2 context)
                    (edge.children.zip children) current
                 if checked.1 then check (unknownOf callback) key edge (.node symbol (children.map original)) checked.2
                 else (false, checked.2)) := by
            have checked := allM_checked (unknownOf callback) (Refutes automaton meaning registry)
              (fun pair context => AcceptanceEffects.visit (AcceptanceEffects.shared automaton (unknownOf callback) fuel)
                pair.1 pair.2 context) (fun pair => Run automaton meaning pair.1 (original pair.2))
              (edge.children.zip children) current safe tracked
              (fun pair member context safe tracked => childChecked pair (List.of_mem_zip member).2 context safe tracked)
            cases answer : (allM (fun pair context =>
                AcceptanceEffects.visit (AcceptanceEffects.shared automaton (unknownOf callback) fuel) pair.1 pair.2 context)
                (edge.children.zip children) current).1 with
            | false =>
                simp only [answer, Bool.false_eq_true, ↓reduceIte]
                exact ⟨checked.1, checked.2.1, checked.2.2.1, fun decided _ proof => checked.2.2.2 decided answer proof.1⟩
            | true =>
                simp only [answer, ↓reduceIte]
                have guard := check_checked automaton callback compatible meaning noSound registry key edge
                  (List.mem_filter.mp member).1 (.node symbol (children.map original)) _ checked.1 checked.2.1
                exact ⟨guard.1, guard.2.1, checked.2.2.1.trans guard.2.2.1,
                  fun decided rejected proof => guard.2.2.2 decided rejected proof.2⟩
          have alternatives := anyM_checked (unknownOf callback) (Refutes automaton meaning registry) _ _
            ((automaton key).filter (fun edge => matchesRoot edge (.node symbol (children.map original))))
            context safe tracked edgeChecked
          refine ⟨alternatives.1, alternatives.2.1, alternatives.2.2.1, ?_⟩
          intro decided rejected accepted
          obtain ⟨edge, member, symbolMatches, acceptedChildren, guard⟩ := (run_node_iff automaton meaning key _ _).mp accepted
          apply alternatives.2.2.2 decided rejected
          refine ⟨edge, ?_, ?_, guard⟩
          · exact List.mem_filter.mpr ⟨member, by simp [matchesRoot, symbolMatches, acceptedChildren.length_eq]⟩
          · intro pair present
            apply all₂_zip_member _ _ _ acceptedChildren (pair.1, original pair.2)
            rw [List.zip_map_right]
            exact List.mem_map.mpr ⟨pair, present, rfl⟩


/-- The adaptive worker retains sound refutations across direct recursion and fresh local cache scopes. -/
theorem unshared_checked [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (callback : Callback State Symbol) (compatible : Compatible automaton callback) (meaning : Meaning State Symbol)
    (noSound : ∀ key edge, edge ∈ automaton key → ∀ term, callback key edge term = .no → ¬ meaning key edge term)
    (fuel : Nat) (key : State) (term : Term Symbol) (registry : Nat → Option (Term Symbol))
    (context : Context State Symbol) (safe : Refutes automaton meaning registry context)
    (tracked : Tracks (unknownOf callback) context) (enough : term.height ≤ fuel) :
    Checked (unknownOf callback) (Refutes automaton meaning registry) (Run automaton meaning key term)
      context (AcceptanceEffects.unshared automaton (unknownOf callback) fuel key term context) := by
  induction fuel generalizing key term context with
  | zero => have positive := term.height_pos; omega
  | succ fuel ih =>
      cases term with
      | node symbol children =>
          have forestBound : forestHeight children ≤ fuel := by simpa [Term.height, forestHeight] using enough
          cases first : fromMatch (.node symbol children) (automaton key) with
          | nil =>
              simp only [AcceptanceEffects.unshared, first]
              refine ⟨safe, tracked, ⟨[], by simp⟩, ?_⟩
              intro _ _ run
              obtain ⟨edge, member, symbolMatches, accepted, _⟩ := (run_node_iff automaton meaning key _ _).mp run
              have absent := (fromMatch_empty _ _).mp first edge member
              simp [matchesRoot, symbolMatches, accepted.length_eq] at absent
          | cons edge rest =>
              cases second : fromMatch (.node symbol children) rest with
              | nil =>
                  have filtered := sole_match (.node symbol children) (automaton key) edge rest first second
                  have member : edge ∈ automaton key := (List.mem_filter.mp (by rw [filtered]; simp)).1
                  have childChecked := allM_checked (unknownOf callback) (Refutes automaton meaning registry)
                    (fun pair context => AcceptanceEffects.unshared automaton (unknownOf callback) fuel pair.1 pair.2 context)
                    (fun pair => Run automaton meaning pair.1 pair.2) (edge.children.zip children) context safe tracked
                    (fun pair present current safe tracked => ih pair.1 pair.2 current safe tracked
                      (Nat.le_trans (height_le_forestHeight children pair.2 (List.of_mem_zip present).2) forestBound))
                  have runParts : Run automaton meaning key (.node symbol children) →
                      (∀ pair ∈ edge.children.zip children, Run automaton meaning pair.1 pair.2) ∧
                        meaning key edge (.node symbol children) := by
                    intro run
                    obtain ⟨other, otherMember, symbolMatches, accepted, guard⟩ := (run_node_iff automaton meaning key _ _).mp run
                    have matching : other ∈ (automaton key).filter (fun edge => matchesRoot edge (.node symbol children)) :=
                      List.mem_filter.mpr ⟨otherMember, by simp [matchesRoot, symbolMatches, accepted.length_eq]⟩
                    rw [filtered] at matching
                    have equal : other = edge := by simpa using matching
                    subst other
                    exact ⟨fun pair present => all₂_zip_member _ _ _ accepted pair present, guard⟩
                  simp only [AcceptanceEffects.unshared, first, second]
                  cases answer : (allM (fun pair context => AcceptanceEffects.unshared automaton (unknownOf callback)
                      fuel pair.1 pair.2 context) (edge.children.zip children) context).1 with
                  | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      exact ⟨childChecked.1, childChecked.2.1, childChecked.2.2.1,
                        fun decided _ run => childChecked.2.2.2 decided answer (runParts run).1⟩
                  | true =>
                      simp only [↓reduceIte]
                      have guard := check_checked automaton callback compatible meaning noSound registry key edge member
                        (.node symbol children) _ childChecked.1 childChecked.2.1
                      exact ⟨guard.1, guard.2.1, childChecked.2.2.1.trans guard.2.2.1,
                        fun decided rejected run => guard.2.2.2 decided rejected (runParts run).2⟩
              | cons other later =>
                  let numbered := (number (.node symbol children) 0).2
                  let localRegistry := fun index => (nodeEntries numbered).lookup index
                  have cached := shared_checked automaton callback compatible meaning noSound (fuel + 1) key numbered
                    localRegistry {context with cache := fun _ => none} (number_valid _ _) (number_registered _ _)
                    (empty_refutes automaton meaning localRegistry context) tracked (by simpa [numbered, number_original] using enough)
                  simp only [AcceptanceEffects.unshared, first, second]
                  refine ⟨?_, cached.2.1, cached.2.2.1, ?_⟩
                  · intro index state found decided value registered
                    exact safe index state found (earlier_decided (unknownOf callback) _ _ tracked cached.2.1 cached.2.2.1 decided)
                      value registered
                  · simpa only [numbered, number_original] using cached.2.2.2

/-- The public No result refutes every semantic run using sound No decisions only for guards that were visited. -/
theorem no_sound [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (callback : Callback State Symbol) (compatible : Compatible automaton callback) (meaning : Meaning State Symbol)
    (noSound : ∀ key edge, edge ∈ automaton key → ∀ term, callback key edge term = .no → ¬ meaning key edge term)
    (key : State) (term : Term Symbol) (rejected : accepts automaton (unknownOf callback) key term = .no) :
    ¬ Run automaton meaning key term := by
  have checked := unshared_checked automaton callback compatible meaning noSound term.height key term (fun _ => none)
    initial (by intro index state found; cases found) (by rfl) (Nat.le_refl _)
  unfold accepts finish at rejected
  split at rejected
  · contradiction
  · split at rejected
    · contradiction
    · rename_i notAccepted notUnknown
      exact checked.2.2.2 (by simpa using notUnknown) (by simpa using notAccepted)

/-- Sound stable callback decisions make both decided public results semantically sound. -/
theorem accepts_supports [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (callback : Callback State Symbol) (compatible : Compatible automaton callback) (meaning : Meaning State Symbol)
    (sound : ∀ key edge, edge ∈ automaton key → ∀ term,
      Guards.Supports (callback key edge term) (meaning key edge term)) (key : State) (term : Term Symbol) :
    Guards.Supports (accepts automaton (unknownOf callback) key term) (Run automaton meaning key term) := by
  cases verdict : accepts automaton (unknownOf callback) key term with
  | yes =>
      exact yes_sound automaton callback compatible meaning
        (fun key edge member term decided => by simpa [decided, Guards.Supports] using sound key edge member term)
        key term verdict
  | no =>
      exact no_sound automaton callback compatible meaning
        (fun key edge member term decided => by simpa [decided, Guards.Supports] using sound key edge member term)
        key term verdict
  | unknown => trivial

end MicroCFTA.AcceptanceSoundness
