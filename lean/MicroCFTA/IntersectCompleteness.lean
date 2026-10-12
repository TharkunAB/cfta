import MicroCFTA.IntersectSoundness

/-!
# Language completeness of the recursive intersection schedule

Finite input derivations have a rank that decreases when a binder unfolds.
Constructor and union descent do not increase this rank. The proof uses the
sum of the two input ranks before it uses the execution bound. Thus a generated
least binder contains every term with a finite pair of input derivations.
-/
namespace MicroCFTA.IntersectSchedule
open Language Binding BinderLanguage

/-- A nonempty input uses its shared binder identity at each derivation rank. -/
def inputAt (languages : Nat → Nat → Lang Symbol) (input : Input) (rank : Nat) : Lang Symbol :=
  inputLanguage (fun name => languages name rank) input

/-- Independent finite input derivations decrease at binder unfolding. -/
structure RankedInput (view : View Symbol) (valid : Input → Prop) where
  languages : Nat → Nat → Lang Symbol
  body : ∀ name, valid (.mu name) → ∀ rank term, languages name rank term →
    ∃ smaller, smaller < rank ∧ inputAt languages (view.body name) smaller term
  row : ∀ name, valid (.node name) → ∀ rank term, languages name rank term →
    ∃ row ∈ view.rows name, ∃ terms, term = .node row.label terms ∧
      All₂ (fun child term => inputAt languages child rank term) row.children terms ∧ row.guard term = true
  union : ∀ name, valid (.union name) → ∀ rank term, languages name rank term →
    ∃ child ∈ view.members name, inputAt languages child rank term
  copy : ∀ input, valid input → closed view input = true → ∀ rank term,
    inputAt languages input rank term → ∀ environment, meaning environment (view.copy input) term

/-- A common term has two finite input derivations within the combined rank. -/
def RankedCommon (languages : Nat → Nat → Lang Symbol) (bound : Nat) (key : Pair) : Lang Symbol :=
  fun term => ∃ first second, first + second ≤ bound ∧ languages key.1 first term ∧ languages key.2 second term

/-- Enclosing references contain all common terms within the current derivation bound. -/
def CompleteEnvironment (languages : Nat → Nat → Lang Symbol) (bound : Nat)
    (domain : Domain) (environment : Env Symbol) : Prop :=
  ∀ key ∈ domain.seen, Included (RankedCommon languages bound key) (environment (pairName key))

/-- Decreasing the derivation bound weakens the environment requirement. -/
theorem complete_environment_mono (languages : Nat → Nat → Lang Symbol) (before after : Nat)
    (smaller : before ≤ after) (domain : Domain) (environment : Env Symbol)
    (complete : CompleteEnvironment languages after domain environment) :
    CompleteEnvironment languages before domain environment := by
  intro key member term accepted
  obtain ⟨first, second, bounded, left, right⟩ := accepted
  exact complete key member term ⟨first, second, Nat.le_trans bounded smaller, left, right⟩

/-- Canonical pairs retain the two ranks, with their order changed when necessary. -/
theorem ranked_pair (languages : Nat → Nat → Lang Symbol) (bound : Nat) (left right : Input)
    (leftNonempty : left ≠ .empty) (rightNonempty : right ≠ .empty) (term : Term Symbol) :
    RankedCommon languages bound (pair left right) term ↔
      ∃ first second, first + second ≤ bound ∧ inputAt languages left first term ∧ inputAt languages right second term := by
  have leftEq : ∀ rank, inputAt languages left rank = languages (identity left) rank := by
    intro rank; cases left <;> simp_all [inputAt, inputLanguage]
  have rightEq : ∀ rank, inputAt languages right rank = languages (identity right) rank := by
    intro rank; cases right <;> simp_all [inputAt, inputLanguage]
  simp only [leftEq, rightEq]
  unfold RankedCommon pair
  by_cases ordered : identity left ≤ identity right
  · simp [Nat.min_eq_left ordered, Nat.max_eq_right ordered]
  · have reversed : identity right ≤ identity left := by omega
    simp only [Nat.min_eq_right reversed, Nat.max_eq_left reversed]
    constructor <;> rintro ⟨first, second, bounded, one, two⟩
    · exact ⟨second, first, by omega, two, one⟩
    · exact ⟨second, first, by omega, two, one⟩

/-- A fresh complete binder interpretation preserves the enclosing interpretations. -/
theorem complete_bind (languages : Nat → Nat → Lang Symbol) (bound : Nat) (domain : Domain)
    (environment : Env Symbol) (canonical : Canonical domain)
    (complete : CompleteEnvironment languages bound domain environment)
    (bindings : List (Nat × Input)) (key : Pair) (ordered : key.1 ≤ key.2) (fresh : key ∉ domain.seen)
    (value : Lang Symbol) (contains : Included (RankedCommon languages bound key) value) :
    CompleteEnvironment languages bound (extend domain bindings key)
      (BinderLanguage.bind environment (pairName key) value) := by
  intro found member term accepted
  rcases List.mem_cons.mp member with rfl | member
  · simpa [BinderLanguage.bind] using contains term accepted
  · have different : pairName found ≠ pairName key := by
      intro same
      have equal := pairName_injective found key (canonical found member) ordered same
      exact fresh (equal ▸ member)
    simpa [BinderLanguage.bind, different] using complete found member term accepted

/-- Complete paired children accept the original ordered common forest. -/
theorem forest_complete (languages : Nat → Nat → Lang Symbol) (environment : Env Symbol)
    (first second : Nat) (left right : List Input) (shapes : List (Shape (Payload Symbol)))
    (paired : All₂ (fun inputs shape => ∀ term,
      inputAt languages inputs.1 first term → inputAt languages inputs.2 second term →
      meaning environment shape term) (left.zip right) shapes)
    (terms : List (Term Symbol))
    (leftAccepted : All₂ (fun input term => inputAt languages input first term) left terms)
    (rightAccepted : All₂ (fun input term => inputAt languages input second term) right terms) :
    forest environment shapes terms := by
  induction leftAccepted generalizing right shapes with
  | nil => cases rightAccepted; cases paired; simp [forest]
  | cons head tail ih =>
    cases rightAccepted with
    | cons rightHead rightTail =>
      cases paired with
      | cons common rest =>
        rw [forest]
        exact ⟨common _ head rightHead, ih _ _ rest rightTail⟩

/-- Cleanup preserves the unfolding equation of the generated least binder. -/
theorem maybeMu_unfold (environment : Env Symbol) (key : Pair) (body : Shape (Payload Symbol))
    (term : Term Symbol) : meaning environment (maybeMu key body) term ↔
      meaning (BinderLanguage.bind environment (pairName key) (meaning environment (maybeMu key body))) body term := by
  simp only [maybeMu_exact]
  exact binder_unfold environment (pairName key) body term

/-- Completed executions preserve every common finite pair of input derivations. -/
theorem run_complete [DecidableEq Symbol] (view : View Symbol) (model : InputMeaning view)
    (ranked : RankedInput view model.valid) (bound fuel : Nat) :
    (∀ domain left right result, Typed domain → Canonical domain → model.valid left → model.valid right →
      run view fuel domain left right = .ok result → ∀ environment,
      CompleteEnvironment ranked.languages bound domain environment → ∀ first second, first + second ≤ bound →
      ∀ term, inputAt ranked.languages left first term → inputAt ranked.languages right second term →
      meaning environment result term) ∧
    (∀ domain left right result, Typed domain → Canonical domain →
      (∀ child ∈ left.children, model.valid child) → (∀ child ∈ right.children, model.valid child) →
      edge view fuel domain left right = .ok result → ∀ environment,
      CompleteEnvironment ranked.languages bound domain environment → ∀ first second, first + second ≤ bound →
      ∀ terms,
      All₂ (fun child term => inputAt ranked.languages child first term) left.children terms →
      All₂ (fun child term => inputAt ranked.languages child second term) right.children terms →
      left.guard (.node left.label terms) = true → right.guard (.node left.label terms) = true →
      meaning environment result (.node left.label terms)) := by
  induction bound using Nat.strongRecOn generalizing fuel with
  | ind bound smaller =>
    induction fuel with
    | zero => constructor <;> intro domain left right result typed canonical leftValid rightValid completed <;> cases completed
    | succ fuel ih =>
      constructor
      · intro domain left right result typed canonical leftValid rightValid completed environment environmentComplete
          first second bounded term leftAccepted rightAccepted
        have original := completed
        rw [run.eq_def] at completed
        dsimp only at completed
        by_cases empty : left = .empty ∨ right = .empty
        · rcases empty with rfl | rfl
          · exact False.elim leftAccepted
          · exact False.elim rightAccepted
        rw [ite_eq_right empty] at completed
        have leftNonempty : left ≠ .empty := fun same => empty (Or.inl same)
        have rightNonempty : right ≠ .empty := fun same => empty (Or.inr same)
        by_cases reset : (closed view left && closed view right && !domain.free.isEmpty) = true
        · rw [ite_eq_left reset] at completed
          exact ih.1 {} left right result (by intro name input stored; cases stored)
            (by intro key member; cases member) leftValid rightValid completed environment
            (by intro key member; cases member) first second bounded term leftAccepted rightAccepted
        rw [ite_eq_right reset] at completed
        by_cases same : left = right ∧ closed view left = true
        · rw [ite_eq_left same] at completed
          cases completed
          exact ranked.copy left leftValid same.2 first term leftAccepted environment
        rw [ite_eq_right same] at completed
        by_cases swap : greater left right = true
        · rw [ite_eq_left swap] at completed
          exact ih.1 domain right left result typed canonical rightValid leftValid completed environment environmentComplete
            second first (by omega) term rightAccepted leftAccepted
        rw [ite_eq_right swap] at completed
        by_cases seen : pair left right ∈ domain.seen
        · rw [ite_eq_left seen] at completed
          cases completed
          rw [meaning]
          exact environmentComplete _ seen term
            ((ranked_pair ranked.languages bound left right leftNonempty rightNonempty term).mpr
              ⟨first, second, bounded, leftAccepted, rightAccepted⟩)
        rw [ite_eq_right seen] at completed
        have recursiveComplete : ∀ lower, lower < bound → ∀ bindings,
            CompleteEnvironment ranked.languages lower (extend domain bindings (pair left right))
              (BinderLanguage.bind environment (pairName (pair left right)) (meaning environment result)) := by
          intro lower less bindings
          apply complete_bind ranked.languages lower domain environment canonical
            (complete_environment_mono ranked.languages lower bound (Nat.le_of_lt less) domain environment environmentComplete)
            bindings (pair left right) (canonical_pair left right) seen
          intro output accepted
          obtain ⟨one, two, sum, leftTerm, rightTerm⟩ :=
            (ranked_pair ranked.languages lower left right leftNonempty rightNonempty output).mp accepted
          exact (smaller lower less (fuel + 1)).1 domain left right result typed canonical leftValid rightValid
            original environment
            (complete_environment_mono ranked.languages lower bound (Nat.le_of_lt less) domain environment environmentComplete)
            one two sum output leftTerm rightTerm
        split at completed
        · next leftName rightName =>
          obtain ⟨body, built, rfl⟩ := map_success _ _ _ completed
          obtain ⟨one, oneLess, leftBody⟩ := ranked.body leftName leftValid first term leftAccepted
          obtain ⟨two, twoLess, rightBody⟩ := ranked.body rightName rightValid second term rightAccepted
          have decrease : one + two < bound := by omega
          apply (maybeMu_unfold environment _ body term).mpr
          exact (smaller (one + two) decrease fuel).1 _ _ _ body (typed_extend domain typed [leftName, rightName] _)
            (canonical_extend domain canonical _ _ _) (model.body_valid leftName leftValid) (model.body_valid rightName rightValid)
            built _ (recursiveComplete _ decrease _) one two (Nat.le_refl _) term leftBody rightBody
        · next leftName _ =>
          obtain ⟨body, built, rfl⟩ := map_success _ _ _ completed
          obtain ⟨one, oneLess, leftBody⟩ := ranked.body leftName leftValid first term leftAccepted
          have decrease : one + second < bound := by omega
          apply (maybeMu_unfold environment _ body term).mpr
          exact (smaller (one + second) decrease fuel).1 _ _ _ body (typed_extend domain typed [leftName] _)
            (canonical_extend domain canonical _ _ _) (model.body_valid leftName leftValid) rightValid
            built _ (recursiveComplete _ decrease _) one second (Nat.le_refl _) term leftBody rightAccepted
        · next rightName _ =>
          obtain ⟨body, built, rfl⟩ := map_success _ _ _ completed
          obtain ⟨two, twoLess, rightBody⟩ := ranked.body rightName rightValid second term rightAccepted
          have decrease : first + two < bound := by omega
          apply (maybeMu_unfold environment _ body term).mpr
          exact (smaller (first + two) decrease fuel).1 _ _ _ body (typed_extend domain typed [rightName] _)
            (canonical_extend domain canonical _ _ _) leftValid (model.body_valid rightName rightValid)
            built _ (recursiveComplete _ decrease _) first two (Nat.le_refl _) term leftAccepted rightBody
        · next name _ =>
          obtain ⟨shapes, built, rfl⟩ := map_success _ _ _ completed
          obtain ⟨input, present, inputAccepted⟩ := ranked.union name leftValid first term leftAccepted
          obtain ⟨shape, member, execution⟩ := BinderSchedule.related_target _ (walk_exact _ _ _ built) input present
          rw [meaning]
          exact ⟨⟨shape, member⟩, ih.1 domain input right shape typed canonical (model.union_valid name leftValid input present)
            rightValid execution environment environmentComplete first second bounded term inputAccepted rightAccepted⟩
        · next name _ _ =>
          obtain ⟨shapes, built, rfl⟩ := map_success _ _ _ completed
          obtain ⟨input, present, inputAccepted⟩ := ranked.union name rightValid second term rightAccepted
          obtain ⟨shape, member, execution⟩ := BinderSchedule.related_target _ (walk_exact _ _ _ built) input present
          rw [meaning]
          exact ⟨⟨shape, member⟩, ih.1 domain left input shape typed canonical leftValid (model.union_valid name rightValid input present)
            execution environment environmentComplete first second bounded term leftAccepted inputAccepted⟩
        · next name _ _ =>
          cases found : lookup domain name with
          | none => rw [found] at completed; cases completed
          | some binder =>
            rw [found] at completed
            have same := typed name binder found
            subst binder
            exact ih.1 domain (.mu name) right result typed canonical (model.reference_valid name leftValid) rightValid
              completed environment environmentComplete first second bounded term leftAccepted rightAccepted
        · next name _ _ _ =>
          cases found : lookup domain name with
          | none => rw [found] at completed; cases completed
          | some binder =>
            rw [found] at completed
            have same := typed name binder found
            subst binder
            exact ih.1 domain left (.mu name) result typed canonical leftValid (model.reference_valid name rightValid)
              completed environment environmentComplete first second bounded term leftAccepted rightAccepted
        · next leftName rightName =>
          obtain ⟨shapes, built, rfl⟩ := map_success _ _ _ completed
          obtain ⟨leftRow, leftMember, leftTerms, leftTerm, leftChildren, leftGuard⟩ := ranked.row leftName leftValid first term leftAccepted
          obtain ⟨rightRow, rightMember, rightTerms, rightTerm, rightChildren, rightGuard⟩ := ranked.row rightName rightValid second term rightAccepted
          have equal : leftRow.label = rightRow.label ∧ leftTerms = rightTerms := by
            exact Term.node.inj (leftTerm.symm.trans rightTerm)
          have sameTerms := equal.2
          subst rightTerms
          have present : (leftRow, rightRow) ∈ joined (view.rows leftName) (view.rows rightName) :=
            (SymbolicHashJoin.hashJoin_member Row.label (fun a b => (a, b)) _ _ _).mpr
              ⟨leftRow, leftMember, rightRow, rightMember, equal.1, rfl⟩
          obtain ⟨shape, member, execution⟩ := BinderSchedule.related_target _ (walk_exact _ _ _ built) (leftRow, rightRow) present
          rw [meaning]
          refine ⟨⟨shape, member⟩, ?_⟩
          rw [leftTerm]
          exact ih.2 domain leftRow rightRow shape typed canonical (model.row_valid leftName leftValid leftRow leftMember)
            (model.row_valid rightName rightValid rightRow rightMember) execution environment environmentComplete
            first second bounded leftTerms leftChildren rightChildren (by rw [← leftTerm]; exact leftGuard)
            (by rw [← leftTerm]; exact rightGuard)
        · exact False.elim leftAccepted
        · exact False.elim rightAccepted
      · intro domain left right result typed canonical leftValid rightValid completed environment environmentComplete
          first second bounded terms leftAccepted rightAccepted leftGuard rightGuard
        rw [edge.eq_def] at completed
        dsimp only at completed
        have sameLength : left.children.length = right.children.length := leftAccepted.length_eq.trans rightAccepted.length_eq.symm
        rw [ite_eq_right (not_not_intro sameLength)] at completed
        obtain ⟨shapes, built, rfl⟩ := map_success _ _ _ completed
        rw [meaning]
        refine ⟨terms, rfl, ?_, leftGuard, rightGuard⟩
        apply forest_complete ranked.languages environment first second left.children right.children shapes _ terms leftAccepted rightAccepted
        exact SymbolicInternedView.all₂_scoped_imp _ _ _ _ (walk_exact _ _ _ built) (by
          intro inputs member shape _ execution output leftTerm rightTerm
          have originals := List.of_mem_zip member
          exact ih.1 domain inputs.1 inputs.2 shape typed canonical (leftValid inputs.1 originals.1) (rightValid inputs.2 originals.2)
            execution environment environmentComplete first second bounded output leftTerm rightTerm)

/-- A completed top-level intersection retains every term with two finite input derivations. -/
theorem top_complete [DecidableEq Symbol] (view : View Symbol) (model : InputMeaning view)
    (ranked : RankedInput view model.valid) (fuel : Nat) (left right : Input)
    (leftValid : model.valid left) (rightValid : model.valid right) (result : Shape (Payload Symbol))
    (completed : run view fuel {} left right = .ok result) (environment : Env Symbol) (term : Term Symbol)
    (leftAccepted : ∃ rank, inputAt ranked.languages left rank term)
    (rightAccepted : ∃ rank, inputAt ranked.languages right rank term) : meaning environment result term := by
  obtain ⟨first, leftAccepted⟩ := leftAccepted
  obtain ⟨second, rightAccepted⟩ := rightAccepted
  exact (run_complete view model ranked (first + second) fuel).1 {} left right result
    (by intro name input stored; cases stored) (by intro key member; cases member) leftValid rightValid
    completed environment (by intro key member; cases member) first second (Nat.le_refl _) term leftAccepted rightAccepted

/-- Independent finite derivations make every successful output exactly the input intersection. -/
theorem top_exact [DecidableEq Symbol] (view : View Symbol) (model : InputMeaning view)
    (ranked : RankedInput view model.valid)
    (finite : ∀ input, model.valid input → ∀ term,
      inputLanguage model.languages input term → ∃ rank, inputAt ranked.languages input rank term)
    (fuel : Nat) (left right : Input) (leftValid : model.valid left) (rightValid : model.valid right)
    (result : Shape (Payload Symbol)) (completed : run view fuel {} left right = .ok result)
    (environment : Env Symbol) (term : Term Symbol) :
    meaning environment result term ↔ inputLanguage model.languages left term ∧ inputLanguage model.languages right term := by
  constructor
  · exact top_sound view model fuel left right leftValid rightValid result completed environment term
  · intro accepted
    exact top_complete view model ranked fuel left right leftValid rightValid result completed environment term
      (finite left leftValid term accepted.1) (finite right rightValid term accepted.2)

end MicroCFTA.IntersectSchedule
