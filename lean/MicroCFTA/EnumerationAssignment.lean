import MicroCFTA.EnumerationOrder

/-!
# Constructing complete assignments from stored fragment equations

The proved dependency levels bound evaluation of every stored fragment.
Free equality variables receive one fixed finite term.
-/

namespace MicroCFTA.EnumerationAssignment
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress EnumerationDependencies EnumerationReferences EnumerationOrder

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Equal values at contained holes give equal completed fragments. -/
theorem fill_holes_congr (left right : Nat → Term Symbol) (fragment : Fragment Symbol)
    (same : ∀ uv, HasHole fragment uv → left uv = right uv) : fill left fragment = fill right fragment := by
  revert same
  induction fragment using Fragment.rec
    (motive_2 := fun children => (∀ child ∈ children, ∀ uv, HasHole child uv → left uv = right uv) →
      children.map (fill left) = children.map (fill right)) with
  | hole uv => intro same; simpa [fill] using same uv (.hole uv)
  | node symbol children ih =>
      intro same
      simp only [fill]
      apply congrArg (Term.node symbol)
      exact ih (fun child member uv hole => same uv (.child symbol children child uv member hole))
  | nil => rfl
  | cons child children ih ihs =>
      rename_i same
      simp only [List.map_cons]
      rw [ih (fun uv hole => same child (by simp) uv hole), ihs (fun child member => same child (by simp [member]))]

/-- Evaluate one stored variable with a finite bound on fragment dependencies. -/
def evaluateSlots (values : List (UVarValue Symbol)) (roots : Nat → Nat) (fallback : Term Symbol) : Nat → Nat → Term Symbol
  | 0, _ => fallback
  | fuel + 1, uv =>
      match values[roots uv]? with
      | some (.enumerated fragment) => fill (evaluateSlots values roots fallback fuel) fragment
      | _ => fallback

/-- Evaluation stabilizes once its bound exceeds the variable's remaining dependency levels. -/
theorem evaluateSlots_stable (state : State Symbol Guard) (roots : Nat → Nat) (paths : Roots state.representatives roots)
    (level : Nat → Nat) (frontier : Nat) (stratified : Stratified state level frontier) (fallback : Term Symbol)
    (uv leftFuel rightFuel : Nat) (leftBound : frontier - level uv < leftFuel) (rightBound : frontier - level uv < rightFuel) :
    evaluateSlots state.values roots fallback leftFuel uv = evaluateSlots state.values roots fallback rightFuel uv := by
  have stable : ∀ deficit uv, frontier - level uv = deficit → ∀ leftFuel rightFuel,
      deficit < leftFuel → deficit < rightFuel →
      evaluateSlots state.values roots fallback leftFuel uv = evaluateSlots state.values roots fallback rightFuel uv := by
    intro deficit
    induction deficit using Nat.strongRecOn with
    | ind deficit ih =>
        intro uv difference leftFuel rightFuel leftBound rightBound
        cases leftFuel with
        | zero => omega
        | succ leftFuel =>
            cases rightFuel with
            | zero => omega
            | succ rightFuel =>
                cases stored : state.values[roots uv]? with
                | none => simp [evaluateSlots, stored]
                | some value =>
                    cases value with
                    | eliminated | unenumerated _ _ => simp [evaluateSlots, stored]
                    | enumerated fragment =>
                        simp only [evaluateSlots, stored]
                        apply fill_holes_congr
                        intro hole present
                        obtain ⟨size, path⟩ := paths uv
                        have sameLevel := stratified.classes uv (roots uv) (UnionFind.sameClass_root path)
                        obtain ⟨bound, dependencies⟩ := stratified.expanded (roots uv) fragment stored
                        have increases := dependencies hole present
                        have smaller : frontier - level hole < deficit := by omega
                        exact ih (frontier - level hole) smaller hole rfl leftFuel rightFuel (by omega) (by omega)
  exact stable (frontier - level uv) uv rfl leftFuel rightFuel leftBound rightBound

/-- A finite dependency ordering constructs a solution of every completed stored equation. -/
theorem stratified_assignment (state : State Symbol Guard) (safe : Safe state) (level : Nat → Nat) (frontier : Nat)
    (stratified : Stratified state level frontier) (fallback : Term Symbol) (language : NodeLanguage Symbol)
    (free : ∀ (uv : Nat) (node : Option Nat) (scs : List Suspended), state.values[uv]? = some (.unenumerated node scs) → node = none ∧ scs = []) :
    ∃ assignment : Nat → Term Symbol, Fragments.stateSatisfies state.representatives (heap language state.values) assignment := by
  obtain ⟨roots, paths⟩ := roots_exist state.representatives safe.1.total
  let assignment := evaluateSlots state.values roots fallback (frontier + 1)
  refine ⟨assignment, ?_, ?_⟩
  · intro left right same
    have sameRoot := (class_iff state.representatives roots paths left right).mp same
    simp [assignment, evaluateSlots, sameRoot]
  · intro uv
    cases stored : state.values[uv]? with
    | none => simp [heap, stored, slot, slotSatisfies]
    | some value =>
        cases value with
        | eliminated => simp [heap, stored, slot, slotSatisfies]
        | unenumerated node scs =>
            obtain ⟨rfl, rfl⟩ := free uv node scs stored
            simp [heap, stored, slot, slotSatisfies, permits]
        | enumerated fragment =>
            simp only [heap, stored, Option.getD_some, slot, slotSatisfies]
            have fixed := stored_root_fixed state safe roots paths uv _ stored (by simp)
            change fill assignment fragment = evaluateSlots state.values roots fallback (frontier + 1) uv
            rw [evaluateSlots, fixed, stored]
            apply fill_holes_congr
            intro hole present
            obtain ⟨bound, dependencies⟩ := stratified.expanded uv fragment stored
            have higher := dependencies hole present
            exact evaluateSlots_stable state roots paths level frontier stratified fallback hole (frontier + 1) frontier (by omega) (by omega)

/-- Every successful initialized complete caller has a complete solution of its forest and fragment equations. -/
theorem completed_assignment (graph : Graph Symbol Guard) (complete : CompleteGraph graph) (fuel root : Nat)
    (after : State Symbol Guard) (fallback : Term Symbol) (language : NodeLanguage Symbol)
    (success : Success (enumerateFully graph (fun _ _ => none) noPruning fuel ()) (initial root) () after) :
    ∃ assignment : Nat → Term Symbol, Fragments.stateSatisfies after.representatives (heap language after.values) assignment := by
  obtain ⟨safe, _, finished⟩ := enumerateFully_outcome graph (fun _ _ => none) noPruning noPruning_readOnly fuel ()
    (initial root) after ⟨initial_storage root, initial_live root⟩ success
  have proper := initialized_proper graph complete fuel root after success
  obtain ⟨level, frontier, stratified⟩ := initialized_stratified graph complete fuel root after success
  exact stratified_assignment after safe level frontier stratified fallback language (finished_free graph complete after proper finished)

/-- Every actual initialized complete run is accepted when its returned residual predicates hold. -/
theorem runs_sound (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (marker : Symbol) (fuel root : Nat) (term : Term Symbol) (pending : List (Guard × Term Symbol))
    (after : State Symbol Guard) (success : .ok ((term, pending), after) ∈ runs graph marker fuel root)
    (checked : ∀ obligation ∈ pending, meaning obligation.1 obligation.2) : Accepted graph meaning root term := by
  unfold runs at success
  change Success _ (initial root) (term, pending) after at success
  obtain ⟨ignored, enumerated, enumeration, continued⟩ := (success_bind _ _ _ _ _).mp success
  cases ignored
  obtain ⟨safe, supply⟩ := initialized_enumeration_safe graph fuel root enumerated enumeration
  obtain ⟨assignment, equations⟩ := completed_assignment graph complete fuel root enumerated (.node marker [])
    (Accepted graph meaning) enumeration
  have valid : RenderValid graph (Accepted graph meaning) (fun _ _ => True) assignment enumerated :=
    ⟨safe.1.total, ⟨equations, by simp [guardsHold]⟩, complete_noMarkers graph complete enumerated⟩
  obtain ⟨rendered, renderedState, rendering, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨renderedValid, rootTerm⟩ := expandUVar_sound graph (Accepted graph meaning) (fun _ _ => True) assignment marker fuel 0
    enumerated renderedState rendered valid rendering
  have renderedStable := expandUVar_storage graph marker fuel 0 enumerated renderedState rendered safe (by omega) rendering
  obtain ⟨current, readState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨currentSame, readSame⟩ := (get_success renderedState readState current).mp reading
  subst current
  subst readState
  obtain ⟨obligations, guarded, traversal, final⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨pairSame, _⟩ := (success_pure (rendered, obligations) (term, pending) guarded after).mp final
  have termSame : term = rendered := congrArg Prod.fst pairSame
  have pendingSame : pending = obligations := congrArg Prod.snd pairSame
  subst term
  subst pending
  let action := fun obligation : Guard × Fragment Symbol => do
    pure (obligation.1, ← expandFragment graph marker fuel obligation.2)
  have step : ∀ obligation previous output next, RenderValid graph (Accepted graph meaning) (fun _ _ => True) assignment previous →
      Success (action obligation) previous output next →
      RenderValid graph (Accepted graph meaning) (fun _ _ => True) assignment next ∧
        output = (obligation.1, fill assignment obligation.2) := by
    intro obligation previous output next previousValid success
    obtain ⟨guardedTerm, middle, rendering, final⟩ := (success_bind _ _ _ _ _).mp success
    obtain ⟨middleValid, exactTerm⟩ := expandFragment_sound graph (Accepted graph meaning) (fun _ _ => True) assignment marker fuel
      obligation.2 previous middle guardedTerm previousValid rendering
    obtain ⟨outputSame, nextSame⟩ := (success_pure (obligation.1, guardedTerm) output middle next).mp final
    subst output
    subst next
    exact ⟨middleValid, by simp [exactTerm]⟩
  obtain ⟨_, related⟩ := mapM_sound action (RenderValid graph (Accepted graph meaning) (fun _ _ => True) assignment)
    (fun obligation output => output = (obligation.1, fill assignment obligation.2)) step
    renderedState.obligations renderedState guarded obligations renderedValid traversal
  have exactObligations := all₂_map_eq (fun obligation => (obligation.1, fill assignment obligation.2)) renderedState.obligations obligations related
  have satisfies : Satisfies (Accepted graph meaning) meaning assignment enumerated := by
    refine ⟨equations, ?_⟩
    intro obligation member
    apply checked (obligation.1, fill assignment obligation.2)
    rw [exactObligations]
    apply List.mem_map.mpr
    exact ⟨obligation, by simpa [renderedStable.obligations] using member, rfl⟩
  have accepted := initialized_assignment_accepted graph meaning complete correct assignment fuel root enumerated enumeration satisfies
  simpa [rootTerm] using accepted

end MicroCFTA.EnumerationAssignment
