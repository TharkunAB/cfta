import MicroCFTA.SourceCurrentNativeNormalizationFreshness
import MicroCFTA.SourceCurrentNativeStrippedAlternatives
import MicroCFTA.SourceCurrentNativeInputExchange
import MicroCFTA.InternedRecordDepthExecution

/-!
# Symbolic observations for normalized original-input comparison

The two source executions can assign different references to each varying
lexical slot. Fixed captures remain complete available records.
-/
namespace MicroCFTA.SourceCurrentNativeNormalizedComparison
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open InternedDeepFreeDepth InternedRecordDepthShape InternedDepthSemantics
open InternedBinderProtocol (Reference)
variable {Atom : Type}

/-- Fixed records retain their decoded shape and varying slots remain distinct roots. -/
def inputShape : Sum (Value Symbol Guard) Atom → Shape (Sum Reference Atom)
  | .inl value => (shape value).map Sum.inl
  | .inr atom => ⟨[.inr atom], [], false, 0⟩

/-- One symbolic execution retains fixed names separately from all varying slots. -/
def symbolic (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom)) :
    Shape (Sum Reference Atom) := evaluate expression (inputs.map inputShape)

private theorem input_shape (names : Atom → Reference) (selected : Sum (Value Symbol Guard) Atom) :
    shape (input names selected) = (inputShape selected).map (Sum.elim id names) := by
  cases selected with
  | inl value => simp [input, inputShape, Shape.map, List.map_map, Function.comp_def]
  | inr atom => simp [input, inputShape, shape, Shape.map]

private theorem input_shapes (names : Atom → Reference) (inputs : List (Sum (Value Symbol Guard) Atom)) :
    (inputs.map (input names)).map shape = (inputs.map inputShape).map (Shape.map (Sum.elim id names)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro selected member
  exact input_shape names selected

/-- Renaming varying slots commutes with the complete shape interpreter. -/
theorem instantiated (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) :
    evaluate expression ((inputs.map (input names)).map shape) =
      (symbolic expression inputs).map (Sum.elim id names) := by
  rw [input_shapes, evaluate_map]
  rfl

/-- Actual full source execution has exactly the instantiated symbolic deep occurrences. -/
theorem actual_deep [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (before after : State Symbol Guard)
    (context : Context before (inputs.map (input names)))
    (heap : InternedFreshOrdinaryDepthHeap.Heap before) (value : Value Symbol Guard)
    (actual : build expression (inputs.map (input names)) before = .done value after)
    (name : Reference) :
    name ∈ deepNames value ↔ name ∈ ((symbolic expression inputs).deep.map (Sum.elim id names)) := by
  have observed := (InternedRecordDepthExecution.build_depth expression _ before context heap).result value after actual
  simpa only [instantiated, Shape.map] using observed.deep name

private theorem shape_profiles (inputs : List (Sum (Value Symbol Guard) Atom)) :
    (inputs.map inputShape).map InternedDepthSemanticProjections.profile = inputs.map inputProfile := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro selected member
  cases selected with
  | inl value =>
      exact (InternedDepthSemanticProjections.profile_map Sum.inl (shape value)).trans
        (congrArg (InternedProfileSemantics.mapNames Sum.inl) (shape_profile value))
  | inr atom => rfl

private theorem shapes_coherent (inputs : List (Sum (Value Symbol Guard) Atom)) :
    InternedDepthSemanticProjections.CoherentMany (inputs.map inputShape) := by
  intro value member
  obtain ⟨selected, present, rfl⟩ := List.mem_map.mp member
  cases selected with
  | inl value => exact InternedDepthSemanticProjections.coherent_map Sum.inl _ (shape_coherent value)
  | inr atom => intro _; rfl

private theorem input_free (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference)
    (before : State Symbol Guard) (context : Context before (inputs.map (input names)))
    (index : Nat) (label : Sum Reference Atom) :
    label ∈ (((inputs.map inputShape).map Shape.free)[index]?).getD [] ↔
      label ∈ ((inputs.map SourceCurrentNativeNormalizationInputs.inputNames)[index]?).getD [] := by
  cases found : inputs[index]? with
  | none => simp [List.getElem?_map, found]
  | some selected =>
      have available := context.inputs (input names selected)
        (List.mem_map.mpr ⟨selected, List.mem_of_getElem? found, rfl⟩)
      simp only [List.getElem?_map, found, Option.map_some, Option.getD_some]
      cases selected with
      | inl value =>
          simp only [inputShape, InternedDepthFreeProjection.map_free,
            SourceCurrentNativeNormalizationInputs.inputNames]
          constructor
          · intro member
            obtain ⟨name, present, rfl⟩ := List.mem_map.mp member
            exact List.mem_map.mpr ⟨name, (shape_free value before context.normal.facts.coherent available name).mp present, rfl⟩
          · intro member
            obtain ⟨name, present, rfl⟩ := List.mem_map.mp member
            exact List.mem_map.mpr ⟨name, (shape_free value before context.normal.facts.coherent available name).mpr present, rfl⟩
      | inr atom => rfl

/-- Full symbolic shape free names agree with the independently defined fixed and varying support. -/
theorem symbolic_free_support (expression : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference)
    (before : State Symbol Guard) (context : Context before (inputs.map (input names)))
    (label : Sum Reference Atom) :
    label ∈ (symbolic expression inputs).free ↔
      label ∈ SourceCurrentNativeNormalizationInputs.support expression inputs := by
  rw [symbolic, InternedDepthFreeProjection.evaluate_member expression _ (shapes_coherent inputs), shape_profiles]
  constructor
  · exact InternedFreeNameInputSubset.evaluate_included expression _ _ _
      (fun index label member => (input_free inputs names before context index label).mp member) label
  · exact InternedFreeNameInputSubset.evaluate_included expression _ _ _
      (fun index label member => (input_free inputs names before context index label).mpr member) label

/-- Fresh fixed captures transport absence of every varying deep name through arbitrary nested source calls. -/
theorem deep_transport [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference)
    (before after later final : State Symbol Guard)
    (context : Context before (inputs.map (input firstNames)))
    (laterContext : Context later (inputs.map (input secondNames)))
    (heap : InternedFreshOrdinaryDepthHeap.Heap before)
    (laterHeap : InternedFreshOrdinaryDepthHeap.Heap later)
    (first second : Value Symbol Guard)
    (firstActual : build expression (inputs.map (input firstNames)) before = .done first after)
    (secondActual : build expression (inputs.map (input secondNames)) later = .done second final)
    (absent : ∀ atom, firstNames atom ∉ deepNames first)
    (fresh : ∀ atom, .inl (secondNames atom) ∉ SourceCurrentNativeNormalizationInputs.support expression inputs) :
    ∀ atom, secondNames atom ∉ deepNames second := by
  intro atom member
  obtain ⟨label, present, same⟩ := List.mem_map.mp
    ((actual_deep expression inputs secondNames later final laterContext laterHeap second secondActual _).mp member)
  cases label with
  | inl fixed =>
      have supported := (symbolic_free_support expression inputs firstNames before context (.inl fixed)).mp
        (List.mem_append_right _ present)
      exact fresh atom (same ▸ supported)
  | inr varied =>
      exact absent varied ((actual_deep expression inputs firstNames before after context heap first firstActual _).mpr
        (List.mem_map.mpr ⟨.inr varied, present, rfl⟩))

/-- An available free name outside every boundary is an actual bare root alternative. -/
theorem free_root (value : Value Symbol Guard) (state : State Symbol Guard)
    (normal : InternedStoredMuOrigins.Normal state) (available : Available state value)
    (name : Reference) (free : name ∈ value.free) (shallow : name ∉ deepNames value) :
    Value.reference name ∈ unionMembers value := by
  obtain ⟨child, present, named⟩ :=
    (InternedNormalizationFree.unionMembers_free state normal.facts.coherent value available name).mp free
  by_cases same : child = .reference name
  · exact same ▸ present
  · exact False.elim (shallow ((InternedDeepFreeNormalization.flatten_deep value name).mpr
      ⟨child, present, (atomic_deep child
        (InternedUnionNormalForm.flat_members value
          (InternedUnionNormalForm.resident_flat state normal.flat value available.resident) child present) name).mpr
        ⟨named, same⟩⟩))

/-- A live varying slot with no deep occurrence supplies an actual source root reference. -/
theorem live_root [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (before after : State Symbol Guard)
    (context : Context before (inputs.map (input names))) (value : Value Symbol Guard)
    (actual : build expression (inputs.map (input names)) before = .done value after)
    (atom : Atom) (live : .inr atom ∈ SourceCurrentNativeNormalizationInputs.support expression inputs)
    (shallow : names atom ∉ deepNames value) : Value.reference (names atom) ∈ unionMembers value := by
  have afterContext : Context after (inputs.map (input names)) := by
    simpa only [actual, Outcome.state] using context.build expression
  have available := (build_verified expression _ before context.normal.facts context.inputs).result value after actual
  have free := (SourceCurrentNativeNormalizationInputs.actual_free expression inputs names before after context value actual _).mpr
    (List.mem_map.mpr ⟨.inr atom, live, rfl⟩)
  exact free_root value after afterContext.normal available _ free shallow

/-- Fixed-name freshness identifies a live varying source label from an actual assigned free name. -/
theorem varying_origin [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (before after : State Symbol Guard)
    (context : Context before (inputs.map (input names))) (value : Value Symbol Guard)
    (actual : build expression (inputs.map (input names)) before = .done value after)
    (atom : Atom) (fresh : .inl (names atom) ∉ SourceCurrentNativeNormalizationInputs.support expression inputs)
    (free : names atom ∈ value.free) :
    ∃ label, .inr label ∈ SourceCurrentNativeNormalizationInputs.support expression inputs := by
  obtain ⟨label, present, same⟩ := List.mem_map.mp
    ((SourceCurrentNativeNormalizationInputs.actual_free expression inputs names before after context value actual _).mp free)
  cases label with
  | inl fixed => exact False.elim (fresh (same ▸ present))
  | inr varied => exact ⟨varied, present⟩

/-- A live varying name that is not deep occurs in the symbolic root alternatives. -/
theorem active_roots [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (before after : State Symbol Guard)
    (context : Context before (inputs.map (input names)))
    (heap : InternedFreshOrdinaryDepthHeap.Heap before) (value : Value Symbol Guard)
    (actual : build expression (inputs.map (input names)) before = .done value after)
    (atom : Atom) (live : .inr atom ∈ SourceCurrentNativeNormalizationInputs.support expression inputs)
    (shallow : names atom ∉ deepNames value) : .inr atom ∈ (symbolic expression inputs).roots := by
  have free := (symbolic_free_support expression inputs names before context (.inr atom)).mpr live
  rcases List.mem_append.mp free with root | deep
  · exact root
  · exact False.elim (shallow ((actual_deep expression inputs names before after context heap value actual _).mpr
      (List.mem_map.mpr ⟨.inr atom, deep, rfl⟩)))

private theorem symbolic_callback (body : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference) :
    InternedRecordDepthCallback.symbolic body (inputs.map (input names)) =
      (evaluate body (⟨[Sum.inl ()], [], false, 0⟩ ::
        (inputs.map inputShape).map (Shape.map Sum.inr))).map (Sum.map id (Sum.elim id names)) := by
  unfold InternedRecordDepthCallback.symbolic
  rw [input_shapes, ← local_map, evaluate_map]

private theorem uses_mapped (function : First → Reference) (names : List (Sum Unit First)) :
    InternedProfileCallbackForm.usesArgument (names.map (Sum.map id function)) =
      hasLocal names := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      cases name <;> simp [InternedProfileCallbackForm.usesArgument, hasLocal] at ih ⊢
      exact ih

/-- The syntax-local occurrence decision does not depend on the assigned reference names. -/
theorem uses_same (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) :
    InternedRecordDepthCallback.uses body (inputs.map (input firstNames)) =
      InternedRecordDepthCallback.uses body (inputs.map (input secondNames)) := by
  simp only [InternedRecordDepthCallback.uses, symbolic_callback, Shape.map, uses_mapped]

/-- A live outer root excludes both raw binding and a deep local in the actual binder branch. -/
theorem binder_unused [DecidableEq (EdgeKey Symbol Guard)]
    (smart : Bool) (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (before after : State Symbol Guard)
    (context : Context before (inputs.map (input names)))
    (heap : InternedFreshOrdinaryDepthHeap.Heap before) (value : Value Symbol Guard)
    (actual : build (.binder smart body) (inputs.map (input names)) before = .done value after)
    (atom : Atom) (live : .inr atom ∈ SourceCurrentNativeNormalizationInputs.support (.binder smart body) inputs)
    (shallow : names atom ∉ deepNames value) :
    smart = true ∧ InternedRecordDepthCallback.uses body (inputs.map (input names)) = false := by
  have root := active_roots (.binder smart body) inputs names before after context heap value actual atom live shallow
  cases smart with
  | false => simp [symbolic, evaluate, binder] at root
  | true =>
      refine ⟨rfl, ?_⟩
      have unused : hasLocal (evaluate body (⟨[Sum.inl ()], [], false, 0⟩ ::
          (inputs.map inputShape).map (Shape.map Sum.inr))).deep = false := by
        cases used : hasLocal (evaluate body (⟨[Sum.inl ()], [], false, 0⟩ ::
            (inputs.map inputShape).map (Shape.map Sum.inr))).deep with
        | false => rfl
        | true =>
            simp only [symbolic, evaluate, binder, Bool.not_true, Bool.false_or, used,
              ↓reduceIte, List.not_mem_nil] at root
      simpa only [InternedRecordDepthCallback.uses, symbolic_callback, Shape.map, uses_mapped] using unused

/-- Both actual probes recover the syntax-local decision at their actual chosen ordinary level. -/
theorem probes_use [DecidableEq (EdgeKey Symbol Guard)]
    (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (before afterDepth afterOrdinary : State Symbol Guard)
    (context : Context before environment) (heap : InternedFreshOrdinaryDepthHeap.Heap before)
    (depth ordinary : Value Symbol Guard)
    (depthActual : callback body environment .depth before = .done depth afterDepth)
    (ordinaryActual : callback body environment (.uninterned (ordinaryLevel depth)) afterDepth =
      .done ordinary afterOrdinary) :
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = InternedRecordDepthCallback.uses body environment := by
  have depthChecked := InternedRecordDepthCallback.callback_checked body environment .depth before context
    (InternedNestedProvenance.depth_available before)
    (InternedRecordDepthExecution.build_depth body _ before
      (context.local .depth (InternedNestedProvenance.depth_available before)) heap)
  have depthObservation := (depthChecked.result depth afterDepth depthActual).2
  have depthContext : Context afterDepth environment := by
    simpa only [depthActual, Outcome.state] using
      context.callback body .depth (InternedNestedProvenance.depth_available before)
  have afterHeap : InternedFreshOrdinaryDepthHeap.Heap afterDepth := by
    simpa only [depthActual, Outcome.state] using depthChecked.heap
  have ordinaryChecked := InternedRecordDepthCallback.callback_checked body environment
    (.uninterned (ordinaryLevel depth)) afterDepth depthContext
    (InternedNestedProvenance.ordinary_available afterDepth _)
    (InternedRecordDepthExecution.build_depth body _ afterDepth
      (depthContext.local _ (InternedNestedProvenance.ordinary_available afterDepth _)) afterHeap)
  have ordinaryObservation := (ordinaryChecked.result ordinary afterOrdinary ordinaryActual).2
  have depthAvailable := (callback_verified body environment .depth before context.normal.facts
    (context.local .depth (InternedNestedProvenance.depth_available before)).inputs).result _ _ depthActual
  have fresh : .uninterned (ordinaryLevel depth) ∉ InternedRecordDepthCallback.captured body environment := by
    intro present
    have named := (InternedFreshOrdinaryDepthHeap.observed_other _ _ .depth depth depthObservation _
      (by intro impossible; cases impossible)).mpr present
    exact ordinary_fresh depth (InternedDeepFreeNormalization.deep_free depth afterDepth
      depthContext.normal.facts.coherent depthAvailable _ named)
  apply Bool.eq_iff_iff.mpr
  simpa only [InternedFreshOrdinaryDepthHeap.usesLocal, decide_eq_true_eq] using
    InternedFreshOrdinaryDepthHeap.observed_own _ _ _ ordinary ordinaryObservation fresh

/-- Two complete original-input probe pairs make the same local decision at their separate chosen levels. -/
theorem probes_same [DecidableEq (EdgeKey Symbol Guard)]
    (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference)
    (before afterDepth afterOrdinary later laterDepth laterOrdinary : State Symbol Guard)
    (context : Context before (inputs.map (input firstNames)))
    (laterContext : Context later (inputs.map (input secondNames)))
    (heap : InternedFreshOrdinaryDepthHeap.Heap before)
    (laterHeap : InternedFreshOrdinaryDepthHeap.Heap later)
    (firstDepth firstOrdinary secondDepth secondOrdinary : Value Symbol Guard)
    (firstDepthActual : callback body (inputs.map (input firstNames)) .depth before = .done firstDepth afterDepth)
    (firstOrdinaryActual : callback body (inputs.map (input firstNames))
      (.uninterned (ordinaryLevel firstDepth)) afterDepth = .done firstOrdinary afterOrdinary)
    (secondDepthActual : callback body (inputs.map (input secondNames)) .depth later = .done secondDepth laterDepth)
    (secondOrdinaryActual : callback body (inputs.map (input secondNames))
      (.uninterned (ordinaryLevel secondDepth)) laterDepth = .done secondOrdinary laterOrdinary) :
    InternedFreshOrdinaryDepthHeap.usesLocal firstDepth firstOrdinary =
      InternedFreshOrdinaryDepthHeap.usesLocal secondDepth secondOrdinary := by
  rw [probes_use body _ before afterDepth afterOrdinary context heap _ _ firstDepthActual firstOrdinaryActual,
    probes_use body _ later laterDepth laterOrdinary laterContext laterHeap _ _ secondDepthActual secondOrdinaryActual]
  exact uses_same body inputs firstNames secondNames

/-- A probe-decoded deep local forces the actual smart finish to retain its Mu boundary. -/
theorem retained_of_used (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (correct : InternedFreshOrdinaryDepthHeap.Correct entry body depth ordinary)
    (used : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true) :
    InternedNestedConstruction.finish true (.mu entry body depth ordinary) = .mu entry body depth ordinary := by
  have raw := (correct false).1
  have smart := (correct true).1
  have bodyDepth : body.depth = depth.depth := by
    have same : body.depth + 1 = depth.depth + 1 := by
      simpa only [InternedNestedConstruction.finish, Bool.false_eq_true, ↓reduceIte, Value.depth,
        InternedFreshOrdinaryDepthHeap.decodedDepth, Bool.not_false, Bool.true_or] using raw
    omega
  simp only [InternedFreshOrdinaryDepthHeap.decodedDepth, used, Bool.not_true, Bool.false_or,
    ↓reduceIte] at smart
  unfold InternedNestedConstruction.finish cleanup
  simp only [↓reduceIte]
  split
  · rename_i unused
    have unwrapped : InternedNestedConstruction.finish true (.mu entry body depth ordinary) = body := by
      simp [InternedNestedConstruction.finish, cleanup, unused]
    rw [unwrapped, bodyDepth] at smart
    omega
  · rename_i usedBody
    split
    · rename_i bare
      have erased : InternedNestedConstruction.finish true (.mu entry body depth ordinary) = .empty := by
        simp [InternedNestedConstruction.finish, cleanup, usedBody, bare]
      rw [erased, Value.depth] at smart
      omega
    · rfl

private theorem full_lift_names (selected : Sum (Value Symbol Guard) Atom) :
    SourceCurrentNativeNormalizationInputs.inputNames (liftInput selected) =
      (SourceCurrentNativeNormalizationInputs.inputNames selected).map (fun name => liftName (.inr name)) := by
  cases selected with
  | inl value =>
      simp [SourceCurrentNativeNormalizationInputs.inputNames, liftInput, liftName, List.map_map, Function.comp_def]
  | inr atom => rfl

private theorem body_support (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom)) :
    SourceCurrentNativeNormalizationInputs.support body (.inr (.inl ()) :: inputs.map liftInput) =
      (InternedFreeNameSemantics.evaluate body
        (some [.inl ()] :: (inputs.map inputProfile).map (InternedProfileSemantics.mapNames Sum.inr))
        ([.inl ()] :: (inputs.map SourceCurrentNativeNormalizationInputs.inputNames).map (List.map Sum.inr))).map liftName := by
  rw [SourceCurrentNativeNormalizationInputs.support, ← InternedFreeNameSemantics.evaluate_map liftName]
  congr 1
  · simp only [List.map_cons, List.map_map, inputProfile, InternedProfileSemantics.mapNames,
      Option.map_some, List.map_cons, List.map_nil, liftName]
    congr 1
    apply List.map_congr_left
    intro selected member
    exact lift_profile selected
  · simp only [List.map_cons, List.map_map, SourceCurrentNativeNormalizationInputs.inputNames,
      List.map_cons, List.map_nil, liftName]
    congr 1
    apply List.map_congr_left
    intro selected member
    simpa only [List.map_map, Function.comp_def] using full_lift_names selected

private theorem liftName_injective : Function.Injective (liftName (Atom := Atom)) := by
  let undo : Sum Reference (Sum Unit Atom) → Sum Unit (Sum Reference Atom)
    | .inl name => .inr (.inl name)
    | .inr (.inl bound) => .inl bound
    | .inr (.inr atom) => .inr (.inr atom)
  have cancel (label : Sum Unit (Sum Reference Atom)) : undo (liftName label) = label := by
    cases label with
    | inl bound => rfl
    | inr selected => cases selected <;> rfl
  intro first second same
  exact (cancel first).symm.trans ((congrArg undo same).trans (cancel second))

/-- Entering a body preserves exactly the original fixed and varying capture support. -/
theorem capture_support (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (label : Sum Reference Atom) :
    liftName (.inr label) ∈ SourceCurrentNativeNormalizationInputs.support body
        (.inr (.inl ()) :: inputs.map liftInput) ↔
      label ∈ SourceCurrentNativeNormalizationInputs.support (.binder true body) inputs := by
  rw [body_support, SourceCurrentNativeNormalizationInputs.support,
    InternedFreeNameSemantics.evaluate, InternedFreeNameSemantics.lower_member]
  constructor
  · intro member
    obtain ⟨original, present, same⟩ := List.mem_map.mp member
    exact (liftName_injective same) ▸ present
  · intro member
    exact List.mem_map.mpr ⟨.inr label, member, rfl⟩

/-- A fresh inner label and fresh outer labels establish the next body's fixed-capture freshness. -/
theorem extend_fresh (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (argument : Reference)
    (outer : ∀ atom, .inl (names atom) ∉ SourceCurrentNativeNormalizationInputs.support (.binder true body) inputs)
    (localFresh : .inl argument ∉ SourceCurrentNativeNormalizationInputs.support (.binder true body) inputs) :
    ∀ atom : Sum Unit Atom, .inl (Sum.elim (fun _ => argument) names atom) ∉
      SourceCurrentNativeNormalizationInputs.support body (.inr (.inl ()) :: inputs.map liftInput) := by
  intro atom member
  cases atom with
  | inl token =>
      exact localFresh ((capture_support body inputs (.inl argument)).mp member)
  | inr atom =>
      exact outer atom ((capture_support body inputs (.inl (names atom))).mp member)

end MicroCFTA.SourceCurrentNativeNormalizedComparison
