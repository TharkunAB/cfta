import MicroCFTA.EnumerationRenderability

/-!
# Sufficient bounds for final rendering

Completed graph-bearing classes contain stored fragments. Their strict
dependency levels bound every representative expansion during rendering.
-/

namespace MicroCFTA.EnumerationRendering
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationSemantics EnumerationFrame EnumerationValidity EnumerationSoundness EnumerationProgress EnumerationDependencies EnumerationReferences EnumerationOrder EnumerationAssignment EnumerationExecution EnumerationCompleteness EnumerationConstruction EnumerationOutConstruction EnumerationDecrease EnumerationHistogram EnumerationTermination EnumerationCarriers EnumerationGraphReferences EnumerationRenderability

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
    simp only [List.map_const']
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, pure]
  bind_pure_comp := by intros; simp [bind, pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; exact List.flatMap_assoc

/-- The completed-state facts used to construct final rendering. -/
structure RenderReady (graph : Graph Symbol Guard) (level : Nat → Nat) (frontier : Nat) (state : State Symbol Guard) : Prop where
  safe : Safe state
  finished : Finished graph state
  references : ReferencesCarry state
  stratified : Stratified state level frontier

/-- Rendering reads retain the completed-state facts and the same dependency levels. -/
theorem ready_read (graph : Graph Symbol Guard) (level : Nat → Nat) (frontier : Nat) (before after : State Symbol Guard)
    (ready : RenderReady graph level frontier before) (stable : RenderStable before after) : RenderReady graph level frontier after := by
  refine ⟨stable.safe, ?_, references_read before after stable ready.references, stratified_read before after level frontier stable ready.stratified⟩
  intro value member
  exact ready.finished value (by simpa [stable.values] using member)

/-- A completed graph-bearing variable admits an actual enumerated-value read. -/
theorem getEnumerated_terminates (graph : Graph Symbol Guard) (complete : CompleteGraph graph) (before : State Symbol Guard)
    (safe : Safe before) (finished : Finished graph before) (uv : Nat) (carried : CarriesGraph before uv) :
    ∃ fuel root fragment after, Success (getValue fuel uv) before (.enumerated fragment) after ∧ RenderStable before after ∧
      before.values[root]? = some (.enumerated fragment) ∧ ∃ size, UnionFind.Reaches before.representatives uv root size := by
  obtain ⟨root, size, path⟩ := safe.1.total uv
  obtain ⟨fragment, stored⟩ := completed_carrier graph complete before safe finished uv root size carried path
  obtain ⟨fuel, found, lookup⟩ := UnionFind.findRoot_terminates path
  have rootSame := (UnionFind.reaches_unique (UnionFind.findRoot_correct fuel before.representatives uv found lookup).1 path).1
  let after := {before with representatives := found.forest}
  have execution : Success (getValue fuel uv) before (.enumerated fragment) after :=
    (getValue_success fuel uv before after (.enumerated fragment)).mpr ⟨found, lookup, by simpa [rootSame] using stored, rfl⟩
  exact ⟨fuel, root, fragment, after, execution,
    (getValue_storage fuel uv before after (.enumerated fragment) safe (carrier_inside before safe uv carried) execution).1, stored, size, path⟩

/-- Every graph-bearing fragment in a completed stratified state has a successful finite rendering. -/
theorem expandFragment_complete (graph : Graph Symbol Guard) (complete : CompleteGraph graph) (marker : Symbol)
    (level : Nat → Nat) (frontier : Nat) (fragment : Fragment Symbol) (before : State Symbol Guard)
    (ready : RenderReady graph level frontier before) (carried : FragmentCarries before fragment) :
    ∃ fuel term after, Success (expandFragment graph marker fuel fragment) before term after ∧ RenderStable before after := by
  have construct : ∀ depth, ∀ fragment (before : State Symbol Guard), RenderReady graph level frontier before → FragmentCarries before fragment →
      (∀ uv, HasHole fragment uv → frontier - level uv < depth) →
      ∃ fuel term after, Success (expandFragment graph marker fuel fragment) before term after ∧ RenderStable before after := by
    intro depth
    induction depth using Nat.strongRecOn with
    | ind depth ih =>
        intro fragment
        induction fragment using Fragment.rec
          (motive_2 := fun fragments => ∀ (before : State Symbol Guard), RenderReady graph level frontier before →
            (∀ fragment ∈ fragments, FragmentCarries before fragment) →
            (∀ fragment ∈ fragments, ∀ uv, HasHole fragment uv → frontier - level uv < depth) →
            ∃ fuel terms after, Success (fragments.mapM (expandFragment graph marker fuel)) before terms after ∧ RenderStable before after) with
        | hole uv =>
            intro before ready carried bounded
            have small := bounded uv (.hole uv)
            obtain ⟨readFuel, root, storedFragment, resolved, reading, readStable, stored, size, path⟩ :=
              getEnumerated_terminates graph complete before ready.safe ready.finished uv (carried uv (.hole uv))
            have sameLevel := ready.stratified.classes uv root (UnionFind.sameClass_root path)
            obtain ⟨rootBound, dependencies⟩ := ready.stratified.expanded root storedFragment stored
            have storedCarried := (ready.references.1 root storedFragment stored).preserve storedFragment (carriers_read before resolved readStable)
            have storedBound : ∀ child, HasHole storedFragment child → frontier - level child < frontier - level uv := by
              intro child hole
              have higher := dependencies child hole
              omega
            obtain ⟨renderFuel, term, after, rendering, renderedStable⟩ := ih (frontier - level uv) small storedFragment resolved
              (ready_read graph level frontier before resolved ready readStable) storedCarried storedBound
            let fuel := readFuel + renderFuel
            refine ⟨fuel + 1, term, after, ?_, readStable.trans renderedStable⟩
            simp only [expandFragment]
            apply (success_bind _ _ _ _ _).mpr
            refine ⟨.enumerated storedFragment, resolved, ?_, ?_⟩
            · exact atLeast _ (fun fuel extra => getValue_moreFuel fuel extra uv) readFuel (fuel + 1) (by dsimp [fuel]; omega) before resolved _ reading
            · exact atLeast _ (fun fuel extra => expandFragment_moreFuel graph marker fuel extra storedFragment) renderFuel fuel (by dsimp [fuel]; omega) resolved after term rendering
        | node symbol children childIH =>
            intro before ready carried bounded
            obtain ⟨fuel, terms, after, traversal, stable⟩ := childIH before ready
              (fun child member uv hole => carried uv (.child symbol children child uv member hole))
              (fun child member uv hole => bounded uv (.child symbol children child uv member hole))
            exact ⟨fuel + 1, .node symbol terms, after,
              (success_bind _ _ _ _ _).mpr ⟨terms, after, traversal, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩, stable⟩
        | nil =>
            rename_i before ready carried bounded
            exact ⟨0, [], before, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩, .refl before ready.safe⟩
        | cons child children childIH childrenIH =>
            rename_i before ready carried bounded
            obtain ⟨firstFuel, term, middle, first, firstStable⟩ := childIH before ready (carried child (by simp)) (bounded child (by simp))
            obtain ⟨restFuel, terms, after, continued, lastStable⟩ := childrenIH middle (ready_read graph level frontier before middle ready firstStable)
              (fun fragment member => (carried fragment (by simp [member])).preserve fragment (carriers_read before middle firstStable))
              (fun fragment member => bounded fragment (by simp [member]))
            refine ⟨firstFuel + restFuel, term :: terms, after, ?_, firstStable.trans lastStable⟩
            rw [List.mapM_cons]
            apply (success_bind _ _ _ _ _).mpr
            refine ⟨term, middle, expandFragment_moreFuel graph marker firstFuel restFuel child before term middle first, ?_⟩
            apply (success_bind _ _ _ _ _).mpr
            refine ⟨terms, after, ?_, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
            have more := retains_mapM _ _ (fun fragment => expandFragment_moreFuel graph marker restFuel firstFuel fragment) children middle terms after continued
            simpa [Nat.add_comm] using more
  exact construct (frontier + 1) fragment before ready carried (by intro uv _; omega)

/-- Every completed graph-bearing root has a successful finite root rendering. -/
theorem expandUVar_complete (graph : Graph Symbol Guard) (complete : CompleteGraph graph) (marker : Symbol)
    (level : Nat → Nat) (frontier uv : Nat) (before : State Symbol Guard)
    (ready : RenderReady graph level frontier before) (carried : CarriesGraph before uv) :
    ∃ fuel term after, Success (expandUVar graph marker fuel uv) before term after ∧ RenderStable before after := by
  obtain ⟨readFuel, root, fragment, resolved, reading, readStable, stored, _⟩ := getEnumerated_terminates graph complete before ready.safe ready.finished uv carried
  obtain ⟨renderFuel, term, after, rendering, renderedStable⟩ := expandFragment_complete graph complete marker level frontier fragment resolved
    (ready_read graph level frontier before resolved ready readStable)
    ((ready.references.1 root fragment stored).preserve fragment (carriers_read before resolved readStable))
  let fuel := readFuel + renderFuel
  refine ⟨fuel, term, after, ?_, readStable.trans renderedStable⟩
  unfold expandUVar
  apply (success_bind _ _ _ _ _).mpr
  refine ⟨.enumerated fragment, resolved, ?_, ?_⟩
  · exact atLeast _ (fun fuel extra => getValue_moreFuel fuel extra uv) readFuel (fuel + 1) (by dsimp [fuel]; omega) before resolved _ reading
  · exact atLeast _ (fun fuel extra => expandFragment_moreFuel graph marker fuel extra fragment) renderFuel fuel (by dsimp [fuel]; omega) resolved after term rendering

/-- Every finite residual list with graph-bearing holes has a successful common rendering bound. -/
theorem renderObligations_complete (graph : Graph Symbol Guard) (complete : CompleteGraph graph) (marker : Symbol)
    (level : Nat → Nat) (frontier : Nat) (obligations : List (Guard × Fragment Symbol)) (before : State Symbol Guard)
    (ready : RenderReady graph level frontier before)
    (carried : ∀ obligation ∈ obligations, FragmentCarries before obligation.2) :
    ∃ fuel pending after, Success (obligations.mapM fun obligation => do
      pure (obligation.1, ← expandFragment graph marker fuel obligation.2)) before pending after ∧ RenderStable before after := by
  induction obligations generalizing before with
  | nil => exact ⟨0, [], before, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩, .refl before ready.safe⟩
  | cons obligation rest ih =>
      obtain ⟨firstFuel, term, middle, first, firstStable⟩ := expandFragment_complete graph complete marker level frontier obligation.2 before ready (carried obligation (by simp))
      obtain ⟨restFuel, pending, after, continued, lastStable⟩ := ih middle (ready_read graph level frontier before middle ready firstStable)
        (fun obligation member => (carried obligation (by simp [member])).preserve obligation.2 (carriers_read before middle firstStable))
      refine ⟨firstFuel + restFuel, (obligation.1, term) :: pending, after, ?_, firstStable.trans lastStable⟩
      rw [List.mapM_cons]
      apply (success_bind _ _ _ _ _).mpr
      refine ⟨(obligation.1, term), middle, ?_, ?_⟩
      · exact (success_bind _ _ _ _ _).mpr ⟨term, middle,
          expandFragment_moreFuel graph marker firstFuel restFuel obligation.2 before term middle first,
          (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
      · apply (success_bind _ _ _ _ _).mpr
        refine ⟨pending, after, ?_, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
        have more := retains_mapM _ _ (fun (obligation : Guard × Fragment Symbol) => retains_bind _ _ _ _
          (expandFragment_moreFuel graph marker restFuel firstFuel obligation.2) (fun _ => retains_refl _)) rest middle pending after continued
        simpa [Nat.add_comm] using more

end MicroCFTA.EnumerationRendering
