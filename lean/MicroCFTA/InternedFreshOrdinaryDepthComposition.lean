import MicroCFTA.InternedDepthFreeProjectionCallback
import MicroCFTA.InternedFreshOrdinaryDepthRequest
import MicroCFTA.InternedFreshOrdinaryCallbackDepth

/-!
# Cached-depth observations compose through ordinary source effects

The observation retains actual emptiness, cached Mu depth, and deep names.
Ordered child observations determine edge deletion and surviving maximum
depth. Union normalization retains the ordered maximum and deep names.
-/
namespace MicroCFTA.InternedFreshOrdinaryDepthComposition
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedDepthSemantics
open InternedDeepFreeDepth
open InternedFreshOrdinaryContext
open InternedOccurrenceObservations (Paired)
open InternedNormalizationDepthExact
open InternedBinderProtocol (Reference)

/-- A complete source record has its predicted emptiness, cached depth, and deep names. -/
structure Observed (value : Value Symbol Guard) (shape : Shape Reference) : Prop where
  empty : (value.referenceOf == .empty) = shape.isEmpty
  depth : value.depth = shape.depth
  deep : ∀ name, name ∈ deepNames value ↔ name ∈ shape.deep

/-- The source list retains one complete observation at every original position. -/
abbrev Matches (values : List (Value Symbol Guard)) (shapes : List (Shape Reference)) : Prop := Paired Observed values shapes

/-- The cached maximum of a child list starts with its first child's depth. -/
theorem maximumDepth_cons (value : Value Symbol Guard) (rest : List (Value Symbol Guard)) :
    maximumDepth (value :: rest) = max value.depth (maximumDepth rest) := by
  rw [show value :: rest = [value] ++ rest from rfl, maximumDepth_append]
  simp [maximumDepth]

/-- Matched child lists retain the exact maximum depth and every deep occurrence. -/
theorem many_observed {values : List (Value Symbol Guard)} {shapes : List (Shape Reference)} (matched : Matches values shapes) :
    maximumDepth values = (combineMany shapes).depth ∧
      ∀ name, (∃ value ∈ values, name ∈ deepNames value) ↔ name ∈ (combineMany shapes).deep := by
  induction matched with
  | nil => exact ⟨rfl, by simp [combineMany]⟩
  | @cons first shape values shapes observed rest ih =>
      refine ⟨?_, ?_⟩
      · simp only [maximumDepth_cons, combineMany, combine, observed.depth, ih.1]
      · intro name
        simp only [List.mem_cons, combineMany, combine, List.mem_append]
        constructor
        · rintro ⟨value, rfl | member, named⟩
          · exact Or.inl ((observed.deep name).mp named)
          · exact Or.inr ((ih.2 name).mp ⟨value, member, named⟩)
        · rintro (named | named)
          · exact ⟨first, Or.inl rfl, (observed.deep name).mpr named⟩
          · obtain ⟨value, member, named⟩ := (ih.2 name).mpr named
            exact ⟨value, Or.inr member, named⟩

/-- Matched child lists delete exactly the same source edges. -/
theorem children_empty {values : List (Value Symbol Guard)} {shapes : List (Shape Reference)} (matched : Matches values shapes) :
    values.any (fun value => value.referenceOf == .empty) = shapes.any Shape.isEmpty := by
  induction matched with
  | nil => rfl
  | cons observed rest ih => simp only [List.any_cons, observed.empty, ih]

/-- Shape union is empty exactly when both operands are empty. -/
theorem combine_empty (first second : Shape Atom) :
    (combine first second).isEmpty = (first.isEmpty && second.isEmpty) := by
  simp only [Shape.isEmpty, combine]
  cases first.roots <;> cases second.roots <;> cases first.hasOpaque <;> cases second.hasOpaque <;> rfl

/-- The empty decision of an ordered union retains every actual input position. -/
theorem many_empty {values : List (Value Symbol Guard)} {shapes : List (Shape Reference)} (matched : Matches values shapes) :
    values.all (fun value => value.referenceOf == .empty) = (combineMany shapes).isEmpty := by
  induction matched with
  | nil => rfl
  | cons observed rest ih => simp only [List.all_cons, combineMany, combine_empty, observed.empty, ih]

/-- Actual union normalization has the exact shape observations of its ordered operands. -/
theorem union_observed [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (shapes : List (Shape Reference)) (state : State Symbol Guard)
    (context : Context state environment) (available : ∀ value ∈ values, Available state value) (matched : Matches values shapes) :
    Observed (run (makeUnion values) state).1 (combineMany shapes) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← many_empty matched]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, List.all_eq_true]
    exact InternedEmptyNormalization.makeUnion_empty_iff values state context.normal.facts.coherent
      context.normal.facts.linked context.normal.live context.normal.proper available
  · exact (makeUnion_depth values state context.normal.facts.coherent context.normal.facts.cached
      context.normal.facts.linked context.normal.live available).trans (many_observed matched).1
  · intro name
    exact (InternedDeepFreeNormalization.makeUnion_deep values state context.normal.facts.coherent context.normal.facts.cached
      context.normal.facts.linked context.normal.live available name).trans ((many_observed matched).2 name)

/-- The surviving maximum of an edge list follows its first actual empty-child test. -/
theorem surviving_cons_depth (edge : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) :
    maximumDepth ((surviving (edge :: rest)).flatMap EdgeValue.children) =
      max (if edge.children.any (fun value => value.referenceOf == .empty) then 0 else maximumDepth edge.children)
        (maximumDepth ((surviving rest).flatMap EdgeValue.children)) := by
  cases selected : edge.children.any (fun value => value.referenceOf == .empty) <;>
    simp [surviving, selected, maximumDepth_append]

/-- Ordered observed children determine the actual edge's surviving cached-depth contribution. -/
theorem edge_depth (edge : EdgeValue Symbol Guard) (values : List (Value Symbol Guard))
    (shapes : List (Shape Reference)) (children : edge.children = values) (matched : Matches values shapes) :
    (if edge.children.any (fun value => value.referenceOf == .empty) then 0 else maximumDepth edge.children) =
      (InternedDepthSemantics.edge shapes).depth := by
  rw [children, children_empty matched]
  simp only [InternedDepthSemantics.edge]
  split
  · rfl
  · exact (many_observed matched).1

/-- The existing source profile proof supplies the richer interpreter's actual empty decision. -/
theorem source_empty [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (names : List Reference) (state : State Symbol Guard) (context : Context state (names.map Value.reference))
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : InternedFreshOrdinaryConstruction.build expression (names.map Value.reference) state = .done value after) :
    (value.referenceOf == .empty) = (evaluate expression (names.map InternedDepthFreeProjectionSource.literal)).isEmpty := by
  have verified := InternedFreshOrdinaryFacts.build_verified expression _ state context.normal.facts context.inputs
  have afterContext : Context after (names.map Value.reference) := by
    simpa only [done, Outcome.state] using context.build expression
  have actual := (InternedFreshOrdinaryProfiles.build_profile expression _ state context.normal context.inputs context.profiles).result value after done
  have pure := InternedDepthSemanticProjections.evaluate_profile expression
    (names.map InternedDepthFreeProjectionSource.literal) (InternedDepthFreeProjectionSource.literals_coherent names)
  have inputs : (names.map InternedDepthFreeProjectionSource.literal).map InternedDepthSemanticProjections.profile =
      (names.map (Value.reference (Symbol := Symbol) (Guard := Guard))).map InternedRootProfile.profile := by
    simp [List.map_map, InternedDepthFreeProjectionSource.literal, InternedDepthSemanticProjections.profile,
      InternedRootProfile.profile]
  rw [inputs] at pure
  rw [← InternedRootProfileNode.isEmpty_profile value after afterContext.normal.proper (verified.result _ _ done),
    InternedProfileComposition.isEmpty_same actual, ← pure]
  exact InternedDepthSemanticProjections.profile_empty _

/-- A completed raw body observation determines its normalized callback depth and deep-name response. -/
theorem callback_checked [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (names : List Reference) (argument : Reference) (state : State Symbol Guard)
    (context : Context state (names.map Value.reference)) (argumentAvailable : Available state (.reference argument))
    (checked : InternedFreshOrdinaryDepthRequest.Checked
      (InternedFreshOrdinaryConstruction.build body ((argument :: names).map Value.reference) state)
      (fun value => Observed value (evaluate body ((argument :: names).map InternedDepthFreeProjectionSource.literal)))) :
    InternedFreshOrdinaryDepthRequest.Checked (InternedFreshOrdinaryFacts.callback body (names.map Value.reference) argument state)
      (fun value => value.depth = (InternedDepthFreeProjectionCallback.symbolic body names).depth ∧
        InternedFreshOrdinaryDepthHeap.Observed (InternedDepthFreeProjectionCallback.captured body names)
          (InternedDepthFreeProjectionCallback.uses body names) argument value) := by
  have localContext := context.local argument argumentAvailable
  have verified := InternedFreshOrdinaryFacts.build_verified body _ state localContext.normal.facts localContext.inputs
  unfold InternedFreshOrdinaryFacts.callback
  apply InternedFreshOrdinaryDepthRequest.bind_checked _ _ _ _ checked
  intro value after returned heap observed
  simp only [List.map_cons] at returned
  have afterContext : Context after ((argument :: names).map Value.reference) := by
    simpa only [returned, Outcome.state, List.map_cons] using localContext.build body
  have available := verified.result _ _ returned
  apply InternedFreshOrdinaryDepthRequest.done_checked
  · exact InternedFreshOrdinaryDepthHeap.preserve after _ heap (InternedStoredMuOrigins.filter_noNewMu argument value after)
  · constructor
    · have pure := congrArg Shape.depth (InternedDepthFreeProjectionCallback.evaluate_supplied body names argument)
      exact (filter_depth argument value after afterContext.normal.facts.coherent afterContext.normal.facts.cached
        afterContext.normal.facts.linked afterContext.normal.live available).trans (observed.depth.trans pure)
    · intro name
      exact (InternedDeepFreeNormalization.filter_deep argument name value after afterContext.normal available).trans
        ((observed.deep name).trans (InternedDepthFreeProjectionCallback.deep_form body names argument name))

/-- Removing the symbolic local retains exactly its fixed captures. -/
theorem lower_captures (names : List (Sum Unit Reference)) :
    InternedFreeNameSemantics.lower names = InternedProfileCallbackForm.captures names := by
  unfold InternedFreeNameSemantics.lower InternedProfileCallbackForm.captures
  congr 1
  funext name
  cases name <;> rfl

/-- Both pure local tests select the same symbolic local occurrences. -/
theorem hasLocal_uses (names : List (Sum Unit Reference)) :
    hasLocal names = InternedProfileCallbackForm.usesArgument names := by
  unfold hasLocal InternedProfileCallbackForm.usesArgument
  congr 1
  funext name
  cases name <;> rfl

/-- Fixed free captures in the richer shape agree with the existing independent free-name interpreter. -/
theorem captures_free (body : Syntax Symbol Guard) (names : List Reference) (name : Reference) :
    name ∈ InternedProfileCallbackForm.captures (InternedDepthFreeProjectionCallback.symbolic body names).free ↔
      name ∈ InternedProfileCallbackForm.captures (InternedFreeNameForm.symbolic body
        ((names.map (Value.reference (Symbol := Symbol) (Guard := Guard))).map InternedRootProfile.profile)
        ((names.map (Value.reference (Symbol := Symbol) (Guard := Guard))).map Value.free)) := by
  have projected := InternedDepthFreeProjection.evaluate_member (.binder true body)
    (names.map InternedDepthFreeProjectionSource.literal) (InternedDepthFreeProjectionSource.literals_coherent names) name
  rw [evaluate, InternedDepthFreeProjection.binder_free, InternedFreeNameForm.binder_captures] at projected
  rw [lower_captures] at projected
  simpa only [InternedDepthFreeProjectionCallback.symbolic, InternedDepthFreeProjectionSource.literal,
    List.map_map, Function.comp_def, InternedDepthSemanticProjections.profile, InternedRootProfile.profile,
    Bool.false_eq_true, ↓reduceIte, Shape.free, List.append_nil, Value.free] using projected

/-- An actual normalized callback retains exactly its richer shape's fixed free captures away from its argument. -/
theorem callback_free [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (names : List Reference) (argument : Reference) (state : State Symbol Guard)
    (context : Context state (names.map Value.reference)) (argumentAvailable : Available state (.reference argument))
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : InternedFreshOrdinaryFacts.callback body (names.map Value.reference) argument state = .done value after)
    (name : Reference) (different : name ≠ argument) :
    name ∈ value.free ↔ name ∈ InternedProfileCallbackForm.captures (InternedDepthFreeProjectionCallback.symbolic body names).free :=
  (InternedFreshOrdinarySourceFreeNames.callback_other body _ argument state context.normal
    (context.local argument argumentAvailable).inputs context.freeNames context.profiles value after done name different).trans
      (captures_free body names name).symm

/-- Both actual probes determine the binder observations for any supplied symbolic body shape. -/
theorem binder_shape [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (bodyShape : Shape (Sum Unit Reference))
    (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state depth)
    (depthExpected : depth.depth = bodyShape.depth)
    (depthDeep : InternedFreshOrdinaryDepthHeap.Observed (InternedProfileCallbackForm.captures bodyShape.deep)
      (InternedProfileCallbackForm.usesArgument bodyShape.deep) .depth depth)
    (ordinaryDeep : InternedFreshOrdinaryDepthHeap.Observed (InternedProfileCallbackForm.captures bodyShape.deep)
      (InternedProfileCallbackForm.usesArgument bodyShape.deep) (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) ordinary)
    (depthFree : ∀ name, name ≠ .depth → (name ∈ depth.free ↔ name ∈
      InternedProfileCallbackForm.captures bodyShape.free))
    (ordinaryFree : ∀ name, name ≠ .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth) → (name ∈ ordinary.free ↔ name ∈
      InternedProfileCallbackForm.captures bodyShape.free)) :
    InternedFreshOrdinaryDepthHeap.decodedDepth smart depth ordinary =
      (InternedDepthSemantics.binder smart bodyShape).depth ∧
    ∀ name, name ∈ InternedFreshOrdinaryDepthHeap.decodedDeep smart depth ordinary ↔
      name ∈ (InternedDepthSemantics.binder smart bodyShape).deep := by
  have fresh : .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth) ∉ InternedProfileCallbackForm.captures bodyShape.deep := by
    intro included
    have deep := (InternedFreshOrdinaryDepthHeap.observed_other _ _ .depth depth depthDeep _ (by intro impossible; cases impossible)).mpr included
    exact InternedFreshOrdinaryConstruction.ordinary_fresh depth
      (InternedDeepFreeNormalization.deep_free depth state coherent available _ deep)
  have uses : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = InternedProfileCallbackForm.usesArgument bodyShape.deep := by
    apply Bool.eq_iff_iff.mpr
    simpa only [InternedFreshOrdinaryDepthHeap.usesLocal, decide_eq_true_eq] using
      InternedFreshOrdinaryDepthHeap.observed_own _ _ _ ordinary ordinaryDeep fresh
  have freeDecoded := InternedFreeNameDecoder.decode_observed _ depth.free ordinary.free
    .depth (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) (by intro impossible; cases impossible) depthFree ordinaryFree
  have deepDecoded := InternedFreeNameDecoder.decode_observed _ (deepNames depth) (deepNames ordinary)
    .depth (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) (by intro impossible; cases impossible)
    (InternedFreshOrdinaryDepthHeap.observed_other _ _ .depth depth depthDeep)
    (InternedFreshOrdinaryDepthHeap.observed_other _ _ _ ordinary ordinaryDeep)
  change InternedFreshOrdinaryDepthHeap.decodedDepth smart depth ordinary =
    (InternedDepthSemantics.binder smart bodyShape).depth ∧ _
  constructor
  · simp only [InternedFreshOrdinaryDepthHeap.decodedDepth, uses, depthExpected, InternedDepthSemantics.binder,
      hasLocal_uses]
    split <;> simp_all
  · intro name
    change name ∈ InternedFreshOrdinaryDepthHeap.decodedDeep smart depth ordinary ↔
      name ∈ (InternedDepthSemantics.binder smart bodyShape).deep
    simp only [InternedFreshOrdinaryDepthHeap.decodedDeep, uses, InternedDepthSemantics.binder,
      hasLocal_uses]
    split
    · simpa only [↓reduceIte, InternedDepthSemantics.lower, lower_captures] using freeDecoded name
    · simpa only [↓reduceIte, InternedDepthSemantics.lower, lower_captures] using deepDecoded name

/-- Both actual probes determine the richer interpreter's complete binder depth and deep names. -/
theorem binder_decoded [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (names : List Reference) (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state (names.map Value.reference)) (available : Available state depth)
    (depthExpected : depth.depth = (InternedDepthFreeProjectionCallback.symbolic body names).depth)
    (depthDeep : InternedFreshOrdinaryDepthHeap.Observed (InternedDepthFreeProjectionCallback.captured body names)
      (InternedDepthFreeProjectionCallback.uses body names) .depth depth)
    (ordinaryDeep : InternedFreshOrdinaryDepthHeap.Observed (InternedDepthFreeProjectionCallback.captured body names)
      (InternedDepthFreeProjectionCallback.uses body names) (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) ordinary)
    (depthFree : ∀ name, name ≠ .depth → (name ∈ depth.free ↔ name ∈
      InternedProfileCallbackForm.captures (InternedDepthFreeProjectionCallback.symbolic body names).free))
    (ordinaryFree : ∀ name, name ≠ .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth) → (name ∈ ordinary.free ↔ name ∈
      InternedProfileCallbackForm.captures (InternedDepthFreeProjectionCallback.symbolic body names).free)) :
    InternedFreshOrdinaryDepthHeap.decodedDepth smart depth ordinary =
      (evaluate (.binder smart body) (names.map InternedDepthFreeProjectionSource.literal)).depth ∧
    ∀ name, name ∈ InternedFreshOrdinaryDepthHeap.decodedDeep smart depth ordinary ↔
      name ∈ (evaluate (.binder smart body) (names.map InternedDepthFreeProjectionSource.literal)).deep := by
  rw [evaluate]
  exact binder_shape smart (InternedDepthFreeProjectionCallback.symbolic body names) depth ordinary state
    context.normal.facts.coherent available depthExpected depthDeep ordinaryDeep depthFree ordinaryFree

end MicroCFTA.InternedFreshOrdinaryDepthComposition
