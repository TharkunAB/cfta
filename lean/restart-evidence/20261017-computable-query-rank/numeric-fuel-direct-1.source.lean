import MicroCFTA.IntersectRequiredFuel

/-!
# Numeric fuel from an initial decreasing call rank

The rank decreases at each actual recursive semantic call. Root reset may
change the two closed roots. The other calls preserve their combined size.
No completed execution or least successful fuel is an initial input.
-/
namespace MicroCFTA.IntersectSchedule
open Language Binding BinderLanguage

private def NumericBound (amount : Nat) (action : Nat → Except Error α) : Prop :=
  ∃ value, ∀ fuel, amount ≤ fuel → action fuel = .ok value

private theorem numeric_pure (amount : Nat) (value : α) :
    NumericBound amount (fun _ => (.ok value : Except Error α)) :=
  ⟨value, fun _ _ => rfl⟩

private theorem numeric_map (action : Nat → Except Error α) (convert : α → β)
    (total : NumericBound amount action) : NumericBound amount (fun fuel => (action fuel).map convert) := by
  obtain ⟨value, result⟩ := total
  exact ⟨convert value, fun fuel enough => by dsimp only; rw [result fuel enough]; rfl⟩

private theorem numeric_walk (action : Nat → α → Except Error β) (input : List α)
    (total : ∀ item ∈ input, NumericBound amount (fun fuel => action fuel item)) :
    NumericBound amount (fun fuel => walk (action fuel) input) := by
  induction input with
  | nil => exact ⟨[], fun _ _ => rfl⟩
  | cons first rest ih =>
    obtain ⟨value, headResult⟩ := total first (by simp)
    obtain ⟨values, tailResult⟩ := ih (fun item member => total item (by simp [member]))
    exact ⟨value :: values, fun fuel enough => by
      simp [walk, headResult fuel enough, tailResult fuel enough, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

private theorem numeric_succ (action : Nat → Except Error α)
    (total : NumericBound amount (fun fuel => action (fuel + 1))) : NumericBound (amount + 1) action := by
  obtain ⟨value, result⟩ := total
  refine ⟨value, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => exact result fuel (by omega)

private theorem numeric_weaken (action : Nat → Except Error α)
    (total : NumericBound first action) (enough : first ≤ last) : NumericBound last action := by
  obtain ⟨value, result⟩ := total
  exact ⟨value, fun fuel supplied => result fuel (Nat.le_trans enough supplied)⟩

section Rank
variable [DecidableEq Symbol]
variable (view : View Symbol) (inputs : FiniteInput view) (freeCorrect : FreeCorrect view)
variable (bounds : InputBounds view inputs)
variable (rank : ClosedRoots view inputs → Call Symbol → Nat)
variable (root_decrease : ∀ (roots nextRoots : ClosedRoots view inputs) (parent child : Call Symbol),
  bounds.size nextRoots.left + bounds.size nextRoots.right < bounds.size roots.left + bounds.size roots.right →
  WorkReady bounds roots parent → WorkReady bounds nextRoots child → rank nextRoots child < rank roots parent)
variable (local_decrease : ∀ (roots nextRoots : ClosedRoots view inputs) (parent child : Call Symbol),
  bounds.size nextRoots.left + bounds.size nextRoots.right = bounds.size roots.left + bounds.size roots.right →
  WorkReady bounds roots parent → WorkReady bounds nextRoots child → LocalStep view bounds.pairs child parent →
  rank nextRoots child < rank roots parent)

/-- Initial decreasing rank supplies one stable exact semantic result at rank plus one. -/
theorem call_numeric (roots : ClosedRoots view inputs) (call : Call Symbol) (ready : WorkReady bounds roots call) :
    ∃ result, ∀ fuel, rank roots call + 1 ≤ fuel → execute view fuel call = .ok result := by
  suffices all : ∀ amount (roots : ClosedRoots view inputs) (call : Call Symbol),
      rank roots call = amount → WorkReady bounds roots call →
      NumericBound (amount + 1) (fun fuel => execute view fuel call) by
    exact all _ roots call rfl ready
  intro amount
  induction amount using Nat.strongRecOn with
  | ind amount ih =>
    intro roots call sameRank ready
    have recurse : ∀ (nextRoots : ClosedRoots view inputs) (child : Call Symbol),
        WorkReady bounds nextRoots child → rank nextRoots child < amount →
        NumericBound amount (fun fuel => execute view fuel child) := by
      intro nextRoots child nextReady smaller
      exact numeric_weaken _ (ih _ smaller nextRoots child rfl nextReady) (by omega)
      cases call with
      | node domain left right =>
        change NodeReady roots domain left right at ready
        change NumericBound (amount + 1) (fun fuel => run view fuel domain left right)
        apply numeric_succ
        conv => arg 1; ext fuel; rw [run.eq_def]
        dsimp only
        by_cases empty : left = .empty ∨ right = .empty
        · simp only [ite_eq_left empty]
          exact numeric_pure _
        simp only [ite_eq_right empty]
        have leftNonempty : left ≠ .empty := fun same => empty (Or.inl same)
        have rightNonempty : right ≠ .empty := fun same => empty (Or.inr same)
        have leftValid := input_reach_valid view inputs roots.left left roots.left_valid ready.left_reach
        have rightValid := input_reach_valid view inputs roots.right right roots.right_valid ready.right_reach
        by_cases reset : (closed view left && closed view right && !domain.free.isEmpty) = true
        · simp only [ite_eq_left reset]
          have isClosed : closed view left = true ∧ closed view right = true := by
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at reset
            exact reset.1
          let nextRoots : ClosedRoots view inputs := ⟨left, right, leftValid, rightValid, isClosed.1, isClosed.2⟩
          have resetLess := reset_decreases bounds roots domain left right ready reset
          exact recurse nextRoots (.node {} left right) (roots_ready view inputs nextRoots) (by
            rw [← sameRank]
            exact root_decrease roots nextRoots _ _ resetLess ready (roots_ready view inputs nextRoots))
        simp only [ite_eq_right reset]
        by_cases same : left = right ∧ closed view left = true
        · simp only [ite_eq_left same]
          exact numeric_pure _
        simp only [ite_eq_right same]
        by_cases swap : greater left right = true
        · simp only [ite_eq_left swap]
          have localStep : LocalStep view bounds.pairs (.node domain right left) (.node domain left right) := .swap domain left right swap
          exact recurse roots.swap (.node domain right left) (ready_swap roots domain left right ready) (by
            rw [← sameRank]
            exact local_decrease roots roots.swap _ _ (by simp [ClosedRoots.swap, Nat.add_comm])
              ready (ready_swap roots domain left right ready) localStep)
        simp only [ite_eq_right swap]
        by_cases seen : pair left right ∈ domain.seen
        · simp only [ite_eq_left seen]
          exact numeric_pure _
        simp only [ite_eq_right seen]
        have possible := bounds.pair_mem left right leftValid rightValid leftNonempty rightNonempty
        split
        · next first second =>
          apply numeric_map
          have nextReady : NodeReady roots (extend domain [(first, .mu first), (second, .mu second)] (pair (.mu first) (.mu second)))
              (view.body first) (view.body second) := by
            apply ready_descend roots _ _ _ (.body ready.left_reach) (.body ready.right_reach)
              (valid_extend view domain [first, second] _ ready.domain_valid (by
                intro name member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                rcases member with rfl | rfl
                · exact ready.left_covered
                · exact ready.right_covered))
              (binder_body_covered view freeCorrect domain [first, second] _ first (by simp) ready.left_covered)
              (binder_body_covered view freeCorrect domain [first, second] _ second (by simp) ready.right_covered)
              (started_extend roots domain _ _ ready.started _)
            rintro ⟨same, _⟩
            exact payload_ne_root bounds roots.left (.mu first) _ roots.left_valid roots.left_closed ready.left_reach
              (bounds.body first leftValid) same
          have localStep := LocalStep.both (view := view) domain first second possible seen
          exact recurse roots (.node _ _ _) nextReady (by
            rw [← sameRank]
            exact local_decrease roots roots _ _ rfl ready nextReady localStep)
        · next name _ =>
          apply numeric_map
          have nextReady : NodeReady roots (extend domain [(name, .mu name)] (pair (.mu name) right)) (view.body name) right := by
            apply ready_descend roots _ _ _ (.body ready.left_reach) ready.right_reach
              (valid_extend view domain [name] _ ready.domain_valid (by
                intro found member; have equal : found = name := by simpa using member
                subst found; exact ready.left_covered))
              (binder_body_covered view freeCorrect domain [name] _ name (by simp) ready.left_covered)
              (covers_extend view domain [name] _ right ready.right_covered)
              (started_extend roots domain _ _ ready.started _)
            rintro ⟨same, _⟩
            exact payload_ne_root bounds roots.left (.mu name) _ roots.left_valid roots.left_closed ready.left_reach
              (bounds.body name leftValid) same
          have localStep := LocalStep.leftMu (view := view) domain name right possible seen
          exact recurse roots (.node _ _ _) nextReady (by
            rw [← sameRank]
            exact local_decrease roots roots _ _ rfl ready nextReady localStep)
        · next name _ =>
          apply numeric_map
          have nextReady : NodeReady roots (extend domain [(name, .mu name)] (pair left (.mu name))) left (view.body name) := by
            apply ready_descend roots _ _ _ ready.left_reach (.body ready.right_reach)
              (valid_extend view domain [name] _ ready.domain_valid (by
                intro found member; have equal : found = name := by simpa using member
                subst found; exact ready.right_covered))
              (covers_extend view domain [name] _ left ready.left_covered)
              (binder_body_covered view freeCorrect domain [name] _ name (by simp) ready.right_covered)
              (started_extend roots domain _ _ ready.started _)
            rintro ⟨_, same⟩
            exact payload_ne_root bounds roots.right (.mu name) _ roots.right_valid roots.right_closed ready.right_reach
              (bounds.body name rightValid) same
          have localStep := LocalStep.rightMu (view := view) domain left name possible seen
          exact recurse roots (.node _ _ _) nextReady (by
            rw [← sameRank]
            exact local_decrease roots roots _ _ rfl ready nextReady localStep)
        · next name excluded =>
          apply numeric_map
          apply numeric_walk
          intro child member
          have protection := started_nonbinders roots domain (.union name) right ready.started
            (by intro binder same; cases same) (by intro binder same; subst right; simp_all)
          have nextReady : NodeReady roots domain child right := by
            apply ready_descend roots domain child right (.member ready.left_reach member) ready.right_reach ready.domain_valid
              (union_member_covered view freeCorrect domain name child member ready.left_covered) ready.right_covered protection
            rintro ⟨same, _⟩
            exact payload_ne_root bounds roots.left (.union name) child roots.left_valid roots.left_closed ready.left_reach
              (bounds.member name leftValid child member) same
          have localStep := LocalStep.leftUnion (view := view) (pairs := bounds.pairs) domain name right child member
          exact recurse roots (.node _ _ _) nextReady (by
            rw [← sameRank]
            exact local_decrease roots roots _ _ rfl ready nextReady localStep)
        · next name excluded excludedUnion =>
          apply numeric_map
          apply numeric_walk
          intro child member
          have protection := started_nonbinders roots domain left (.union name) ready.started
            (by intro binder same; subst left; simp_all) (by intro binder same; cases same)
          have nextReady : NodeReady roots domain left child := by
            apply ready_descend roots domain left child ready.left_reach (.member ready.right_reach member) ready.domain_valid
              ready.left_covered (union_member_covered view freeCorrect domain name child member ready.right_covered) protection
            rintro ⟨_, same⟩
            exact payload_ne_root bounds roots.right (.union name) child roots.right_valid roots.right_closed ready.right_reach
              (bounds.member name rightValid child member) same
          have localStep := LocalStep.rightUnion (view := view) (pairs := bounds.pairs) domain left name child member
          exact recurse roots (.node _ _ _) nextReady (by
            rw [← sameRank]
            exact local_decrease roots roots _ _ rfl ready nextReady localStep)
        · next name excluded excludedUnion =>
          have found := reference_resolves view freeCorrect domain name ready.left_covered
          simp only [found]
          have protection := started_nonbinders roots domain (.ref name) right ready.started
            (by intro binder same; cases same) (by intro binder same; subst right; simp_all)
          have nextReady : NodeReady roots domain (.mu name) right :=
            ready_descend roots domain _ _ (.reference ready.left_reach) ready.right_reach ready.domain_valid
              (ready.domain_valid.closed name found) ready.right_covered protection
              (protected_reference_left roots domain name right protection seen)
          have localStep := LocalStep.leftRef (view := view) (pairs := bounds.pairs) domain name right
          exact recurse roots (.node _ _ _) nextReady (by
            rw [← sameRank]
            exact local_decrease roots roots _ _ rfl ready nextReady localStep)
        · next name excluded excludedUnion excludedRef =>
          have found := reference_resolves view freeCorrect domain name ready.right_covered
          simp only [found]
          have protection := started_nonbinders roots domain left (.ref name) ready.started
            (by intro binder same; subst left; simp_all) (by intro binder same; cases same)
          have changed : ¬ (left = roots.left ∧ Input.mu name = roots.right) := by
            rintro ⟨one, two⟩
            exact protected_reference_left roots.swap domain name left (protected_swap roots domain protection)
              (by simpa [pair_symmetric] using seen) ⟨two, one⟩
          have nextReady : NodeReady roots domain left (.mu name) :=
            ready_descend roots domain _ _ ready.left_reach (.reference ready.right_reach) ready.domain_valid
              ready.left_covered (ready.domain_valid.closed name found) protection changed
          have localStep := LocalStep.rightRef (view := view) (pairs := bounds.pairs) domain left name
          exact recurse roots (.node _ _ _) nextReady (by
            rw [← sameRank]
            exact local_decrease roots roots _ _ rfl ready nextReady localStep)
        · next first second =>
          apply numeric_map
          apply numeric_walk
          intro rows member
          have originals := joined_members (view.rows first) (view.rows second) rows member
          have nextReady := ready_rows view inputs freeCorrect bounds roots domain first second ready rows.1 rows.2 originals.1 originals.2
          have localStep := LocalStep.nodeRows (view := view) (pairs := bounds.pairs) domain first second rows.1 rows.2 originals.1 originals.2
          exact recurse roots (.edge _ _ _) nextReady (by
            rw [← sameRank]
            exact local_decrease roots roots _ _ rfl ready nextReady localStep)
        · exact False.elim (leftNonempty rfl)
        · exact False.elim (rightNonempty rfl)
      | edge domain left right =>
        change EdgeReady bounds roots domain left right at ready
        change NumericBound (amount + 1) (fun fuel => edge view fuel domain left right)
        apply numeric_succ
        conv => arg 1; ext fuel; rw [edge.eq_def]
        dsimp only
        by_cases arity : left.children.length ≠ right.children.length
        · simp only [ite_eq_left arity]
          exact numeric_pure _
        simp only [ite_eq_right arity]
        apply numeric_map
        apply numeric_walk
        intro children member
        have nextReady := ready_child bounds roots domain left right ready children member
        have localStep := LocalStep.edgeChild (view := view) (pairs := bounds.pairs) domain left right children member
        exact recurse roots (.node _ _ _) nextReady (by
            rw [← sameRank]
            exact local_decrease roots roots _ _ rfl ready nextReady localStep)

/-- The least successful semantic fuel is bounded by the initial numeric rank. -/
theorem requiredFuel_le_numeric (roots : ClosedRoots view inputs) (call : Call Symbol)
    (ready : WorkReady bounds roots call) (complete : Completes view call) :
    requiredFuel view call complete ≤ rank roots call + 1 := by
  obtain ⟨result, done⟩ := call_numeric view inputs freeCorrect bounds rank root_decrease local_decrease roots call ready
  exact requiredFuel_le view call complete _ result (done _ (Nat.le_refl _))

end Rank
end MicroCFTA.IntersectSchedule
