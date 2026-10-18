import MicroCFTA.SourceCurrentNativeNormalizedComparison
import MicroCFTA.SourceCurrentNativeMuPublicationCallbacks
import MicroCFTA.SourceCurrentPublicationBareParity

/-!
# Live alias information at actual source publications

The Depth anchor retains aliases with captured Depth references. Fresh
ordinary and reserved arguments extend the same captured environment.
These input facts do not assert a reconstruction relation for returned Mu
records. No injectivity of the varying lexical labels is required.
-/
namespace MicroCFTA.SourceCurrentUsedBinderAliasTransport
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryLiveInputs (input liftInput local_inputs)
open InternedFreshOrdinaryLiveInputs (liftName)
open SourceCurrentNativeNormalizationInputs (support actual_free)
open SourceCurrentNativeMuPublication (Publication History)
open InternedBinderProtocol (Reference)
variable {Atom : Type}

/-- Live names include a fixed Depth anchor, even when Depth is not a source capture. -/
def Scope (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom)) :
    List (Sum Reference Atom) := .inl .depth :: support expression inputs

/-- Both assignments preserve exactly the equalities between live names and Depth. -/
def Aliases (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) : Prop :=
  ∀ first ∈ Scope expression inputs, ∀ second ∈ Scope expression inputs,
    Sum.elim id firstNames first = Sum.elim id firstNames second ↔
      Sum.elim id secondNames first = Sum.elim id secondNames second

private theorem scope_body (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (label : Sum Reference (Sum Unit Atom))
    (member : label ∈ Scope body (.inr (.inl ()) :: inputs.map liftInput)) :
    label = .inr (.inl ()) ∨ ∃ old ∈ Scope (.binder true body) inputs, label = liftName (.inr old) := by
  rcases List.mem_cons.mp member with rfl | member
  · exact Or.inr ⟨.inl .depth, List.mem_cons_self, rfl⟩
  · cases label with
    | inl name =>
        exact Or.inr ⟨.inl name, List.mem_cons_of_mem _
          ((SourceCurrentNativeNormalizedComparison.capture_support body inputs (.inl name)).mp member), rfl⟩
    | inr selected =>
        cases selected with
        | inl token => cases token; exact Or.inl rfl
        | inr atom =>
            exact Or.inr ⟨.inr atom, List.mem_cons_of_mem _
              ((SourceCurrentNativeNormalizedComparison.capture_support body inputs (.inr atom)).mp member), rfl⟩

private theorem supplied_lift (names : Atom → Reference) (argument : Reference)
    (label : Sum Reference Atom) :
    Sum.elim id (Sum.elim (fun _ : Unit => argument) names) (liftName (.inr label)) =
      Sum.elim id names label := by
  cases label <;> rfl

/-- Entering a binder needs only the exact local-to-capture alias equivalence. -/
theorem extend (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (firstArgument secondArgument : Reference)
    (aliases : Aliases (.binder true body) inputs firstNames secondNames)
    (localAliases : ∀ label ∈ Scope (.binder true body) inputs,
      Sum.elim id firstNames label = firstArgument ↔ Sum.elim id secondNames label = secondArgument) :
    Aliases body (.inr (.inl ()) :: inputs.map liftInput)
      (Sum.elim (fun _ : Unit => firstArgument) firstNames)
      (Sum.elim (fun _ : Unit => secondArgument) secondNames) := by
  intro first firstMember second secondMember
  rcases scope_body body inputs first firstMember with rfl | ⟨left, leftMember, rfl⟩
  · rcases scope_body body inputs second secondMember with rfl | ⟨right, rightMember, rfl⟩
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · simpa only [Sum.elim_inr, Sum.elim_inl, supplied_lift, eq_comm] using localAliases right rightMember
  · rcases scope_body body inputs second secondMember with rfl | ⟨right, rightMember, rfl⟩
    · simpa only [Sum.elim_inr, Sum.elim_inl, supplied_lift] using localAliases left leftMember
    · simpa only [supplied_lift] using aliases left leftMember right rightMember

/-- A Depth callback preserves Depth aliases instead of requiring Depth freshness. -/
theorem extend_depth (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference)
    (aliases : Aliases (.binder true body) inputs firstNames secondNames) :
    Aliases body (.inr (.inl ()) :: inputs.map liftInput)
      (Sum.elim (fun _ : Unit => .depth) firstNames)
      (Sum.elim (fun _ : Unit => .depth) secondNames) := by
  apply extend body inputs firstNames secondNames .depth .depth aliases
  intro label member
  exact aliases label member (.inl .depth) List.mem_cons_self

/-- Two fresh arguments preserve all old alias classes and create one local class. -/
theorem extend_fresh (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (firstArgument secondArgument : Reference)
    (aliases : Aliases (.binder true body) inputs firstNames secondNames)
    (firstFresh : firstArgument ∉ (Scope (.binder true body) inputs).map (Sum.elim id firstNames))
    (secondFresh : secondArgument ∉ (Scope (.binder true body) inputs).map (Sum.elim id secondNames)) :
    Aliases body (.inr (.inl ()) :: inputs.map liftInput)
      (Sum.elim (fun _ : Unit => firstArgument) firstNames)
      (Sum.elim (fun _ : Unit => secondArgument) secondNames) := by
  apply extend body inputs firstNames secondNames firstArgument secondArgument aliases
  intro label member
  constructor
  · intro same
    exact False.elim (firstFresh (List.mem_map.mpr ⟨label, member, same⟩))
  · intro same
    exact False.elim (secondFresh (List.mem_map.mpr ⟨label, member, same⟩))

/-- The two local references correspond; every other live reference remains literal. -/
def NamePair (firstOwn secondOwn first second : Reference) : Prop :=
  (first = firstOwn ∧ second = secondOwn) ∨
    (first = second ∧ first ≠ firstOwn ∧ second ≠ secondOwn)

private def captures [DecidableEq (EdgeKey Symbol Guard)] (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    List (Sum (Value Symbol Guard) Unit) := event.environment.map Sum.inl

private def fixedNames : Unit → Reference := fun _ => .depth

private theorem fixed_inputs [DecidableEq (EdgeKey Symbol Guard)] (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    (captures event).map (input fixedNames) = event.environment := by
  simp [captures, input, List.map_map, Function.comp_def]

private theorem actual_fresh [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    .uninterned (ordinaryLevel event.depth) ∉
        (Scope (.binder true event.expression) (captures event)).map (Sum.elim id fixedNames) ∧
      .interned event.entry.identity ∉
        (Scope (.binder true event.expression) (captures event)).map (Sum.elim id fixedNames) := by
  have ordinaryFresh := SourceCurrentNativeNormalizationFreshness.ordinary event.expression (captures event)
    fixedNames event.before event.afterDepth (by simpa only [fixed_inputs] using event.context.base)
    event.depth (by simpa only [fixed_inputs] using event.depthDone)
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have reservedFresh := SourceCurrentNativeNormalizationFreshness.reserved (.binder true event.expression)
    (captures event) fixedNames event.cut (by simpa only [fixed_inputs] using cutContext.base) event.key event.missing
  constructor
  · simpa only [Scope, List.map_cons, Sum.elim_inl, id_eq, List.mem_cons, reduceCtorEq, false_or] using ordinaryFresh
  · simpa only [Scope, List.map_cons, Sum.elim_inl, id_eq, List.mem_cons, reduceCtorEq, false_or,
      Publication.entry] using reservedFresh

/-- Actual ordinary and reserved callback inputs have the same live alias pattern. -/
theorem publication [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    Aliases event.expression
      (.inr (.inl ()) :: (event.environment.map (fun value => (Sum.inl value : Sum (Value Symbol Guard) Unit))).map liftInput)
      (Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) (fun _ : Unit => .depth))
      (Sum.elim (fun _ : Unit => .interned event.entry.identity) (fun _ : Unit => .depth)) := by
  exact extend_fresh event.expression (captures event) fixedNames fixedNames _ _
    (fun _ _ _ _ => Iff.rfl) (actual_fresh event).1 (actual_fresh event).2

private theorem support_pair (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (firstOwn secondOwn : Reference)
    (firstFresh : firstOwn ∉ (Scope (.binder true body) inputs).map (Sum.elim id names))
    (secondFresh : secondOwn ∉ (Scope (.binder true body) inputs).map (Sum.elim id names))
    (label : Sum Reference (Sum Unit Atom))
    (member : label ∈ support body (.inr (.inl ()) :: inputs.map liftInput)) :
    NamePair firstOwn secondOwn
      (Sum.elim id (Sum.elim (fun _ : Unit => firstOwn) names) label)
      (Sum.elim id (Sum.elim (fun _ : Unit => secondOwn) names) label) := by
  rcases scope_body body inputs label (List.mem_cons_of_mem _ member) with rfl | ⟨old, present, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · rw [supplied_lift, supplied_lift]
    exact Or.inr ⟨rfl, fun same => firstFresh (List.mem_map.mpr ⟨old, present, same⟩),
      fun same => secondFresh (List.mem_map.mpr ⟨old, present, same⟩)⟩

private theorem raw_pair [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (rawOrdinary rawBody : Value Symbol Guard) (afterOrdinary afterBody : State Symbol Guard)
    (firstDone : build event.expression (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
      event.afterDepth = .done rawOrdinary afterOrdinary)
    (secondDone : build event.expression (.reference (.interned event.entry.identity) :: event.environment)
      event.allocated = .done rawBody afterBody) :
    (∀ name ∈ rawOrdinary.free, ∃ other ∈ rawBody.free,
      NamePair (.uninterned (ordinaryLevel event.depth)) (.interned event.entry.identity) name other) ∧
    (∀ other ∈ rawBody.free, ∃ name ∈ rawOrdinary.free,
      NamePair (.uninterned (ordinaryLevel event.depth)) (.interned event.entry.identity) name other) := by
  let inputs := .inr (.inl ()) :: (captures event).map liftInput
  let firstNames := Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) fixedNames
  let secondNames := Sum.elim (fun _ : Unit => .interned event.entry.identity) fixedNames
  have localInputs (own : Reference) :
      inputs.map (input (Sum.elim (fun _ : Unit => own) fixedNames)) = .reference own :: event.environment := by
    rw [local_inputs, fixed_inputs]
  obtain ⟨depthContext, cutContext, bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have firstContext := depthContext.base.local (.uninterned (ordinaryLevel event.depth))
    (InternedNestedProvenance.ordinary_available _ _)
  have bodyAvailable : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have secondContext := bodyContext.base.local (.interned event.entry.identity) bodyAvailable
  have firstFree (name : Reference) : name ∈ rawOrdinary.free ↔
      name ∈ (support event.expression inputs).map (Sum.elim id firstNames) :=
    actual_free event.expression inputs firstNames event.afterDepth afterOrdinary
      (by simpa only [firstNames, localInputs] using firstContext) rawOrdinary
      (by simpa only [firstNames, localInputs] using firstDone) name
  have secondFree (name : Reference) : name ∈ rawBody.free ↔
      name ∈ (support event.expression inputs).map (Sum.elim id secondNames) :=
    actual_free event.expression inputs secondNames event.allocated afterBody
      (by simpa only [secondNames, localInputs] using secondContext) rawBody
      (by simpa only [secondNames, localInputs] using secondDone) name
  constructor
  · intro name member
    obtain ⟨label, present, same⟩ := List.mem_map.mp ((firstFree name).mp member)
    refine ⟨Sum.elim id secondNames label, (secondFree _).mpr (List.mem_map.mpr ⟨label, present, rfl⟩), ?_⟩
    rw [← same]
    exact support_pair event.expression (captures event) fixedNames _ _
      (actual_fresh event).1 (actual_fresh event).2 label present
  · intro name member
    obtain ⟨label, present, same⟩ := List.mem_map.mp ((secondFree name).mp member)
    refine ⟨Sum.elim id firstNames label, (firstFree _).mpr (List.mem_map.mpr ⟨label, present, rfl⟩), ?_⟩
    rw [← same]
    exact support_pair event.expression (captures event) fixedNames _ _
      (actual_fresh event).1 (actual_fresh event).2 label present

/-- Both actual raw callbacks retain precisely paired local names and unchanged other names. -/
theorem publication_raw [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    ∃ rawOrdinary afterRawOrdinary rawBody afterRawBody,
      build event.expression (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
        event.afterDepth = .done rawOrdinary afterRawOrdinary ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel event.depth)) rawOrdinary) afterRawOrdinary =
        (event.ordinary, event.cut) ∧
      build event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done rawBody afterRawBody ∧
      run (withoutSelfReference (.interned event.entry.identity) rawBody) afterRawBody =
        (event.body, event.afterBody) ∧
      Grows afterRawOrdinary event.afterBody ∧ Grows afterRawBody event.afterBody ∧
      (∀ name ∈ rawOrdinary.free, ∃ other ∈ rawBody.free,
        NamePair (.uninterned (ordinaryLevel event.depth)) (.interned event.entry.identity) name other) ∧
      (∀ other ∈ rawBody.free, ∃ name ∈ rawOrdinary.free,
        NamePair (.uninterned (ordinaryLevel event.depth)) (.interned event.entry.identity) name other) := by
  obtain ⟨first, middle, second, final, firstDone, firstFilter, secondDone, secondFilter,
    firstGrowth, secondGrowth, _, _⟩ := SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
  exact ⟨first, middle, second, final, firstDone, firstFilter, secondDone, secondFilter,
    firstGrowth, secondGrowth, raw_pair event first second middle final firstDone secondDone⟩

end MicroCFTA.SourceCurrentUsedBinderAliasTransport
