import MicroCFTA.SourceCurrentStoredMuProfileContract
import MicroCFTA.SourceCurrentUsedBinderAliasTransport

/-!
# Profile assignments on live source support

Only live fixed names and varying labels constrain the assignments.
Binder extension uses the same local profile and exact live alias tests.
Actual publications supply freshness on this support. Unused captures
and dead source rows require no freshness. Aliases and scoped self tests
remain separate structural conditions.
-/
namespace MicroCFTA.SourceCurrentScopedProfileInputs
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedFreshOrdinaryLiveInputs (input inputProfile liftInput)
open SourceCurrentNativeNormalizationInputs (support inputNames)
open SourceCurrentStoredMuProfileContract (shadow)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceCurrentNativeMuPublication (Publication)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile)

variable {Atom : Type}

/-- Live fixed names agree literally, and live varying names have equal assigned profiles. -/
def Compatible (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Reference → Profile) : Prop :=
  (∀ name, .inl name ∈ support expression inputs → first name = second name) ∧
    ∀ atom, .inr atom ∈ support expression inputs → first (firstNames atom) = second (secondNames atom)

/-- An actual selected variable constrains exactly its fixed names or its varying label. -/
theorem variable_input (index : Nat) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Reference → Profile)
    (compatible : Compatible (.var index) inputs firstNames secondNames first second)
    (selected : Sum (Value Symbol Guard) Atom) (found : inputs[index]? = some selected) :
    match selected with
    | .inl value => ∀ name ∈ value.free, first name = second name
    | .inr atom => first (firstNames atom) = second (secondNames atom) := by
  cases selected with
  | inl value =>
      intro name member
      apply compatible.1 name
      simpa only [support,InternedFreeNameSemantics.evaluate,List.getElem?_map,found,
        Option.map_some,Option.getD_some,inputNames] using List.mem_map.mpr ⟨name,member,rfl⟩
  | inr atom =>
      apply compatible.2 atom
      simp only [support,InternedFreeNameSemantics.evaluate,List.getElem?_map,found,
        Option.map_some,Option.getD_some,inputNames,List.mem_singleton]

/-- Every original union member inherits the parent's live profile condition. -/
theorem union_member (members : List (Syntax Symbol Guard)) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Reference → Profile)
    (compatible : Compatible (.union members) inputs firstNames secondNames first second)
    (member : Syntax Symbol Guard) (present : member ∈ members) :
    Compatible member inputs firstNames secondNames first second := by
  have included (label : Sum Reference Atom) (live : label ∈ support member inputs) :
      label ∈ support (.union members) inputs := by
    unfold support at live ⊢
    rw [InternedFreeNameSemantics.evaluate]
    exact (InternedFreeNameSemantics.evaluateMany_member members (inputs.map inputProfile)
      (inputs.map inputNames) label).mpr ⟨member,present,live⟩
  exact ⟨fun name live => compatible.1 name (included _ live),
    fun atom live => compatible.2 atom (included _ live)⟩

/-- A child of an original live node row inherits the parent's profile condition. -/
theorem node_child (rows : List (EdgeSyntax Symbol Guard)) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Reference → Profile)
    (compatible : Compatible (.node rows) inputs firstNames secondNames first second)
    (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (row : EdgeSyntax.mk symbol guard children ∈ rows)
    (live : (InternedProfileSemantics.evaluateMany children (inputs.map inputProfile)).all
      (fun child => !InternedProfileSemantics.isEmpty child) = true)
    (child : Syntax Symbol Guard) (present : child ∈ children) :
    Compatible child inputs firstNames secondNames first second := by
  have included (label : Sum Reference Atom) (member : label ∈ support child inputs) :
      label ∈ support (.node rows) inputs := by
    unfold support at member ⊢
    rw [InternedFreeNameSemantics.evaluate]
    exact (InternedFreeNameSemantics.evaluateEdges_member rows (inputs.map inputProfile)
      (inputs.map inputNames) label).mpr ⟨symbol,guard,children,row,live,child,present,member⟩
  exact ⟨fun name member => compatible.1 name (included _ member),
    fun atom member => compatible.2 atom (included _ member)⟩

/-- Synchronized live aliases permit one common profile to shadow the two local names. -/
theorem extend (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Reference → Profile)
    (compatible : Compatible (.binder true body) inputs firstNames secondNames first second)
    (firstArgument secondArgument : Reference) (replacement : Profile)
    (aliases : ∀ label ∈ support (.binder true body) inputs,
      Sum.elim id firstNames label = firstArgument ↔ Sum.elim id secondNames label = secondArgument) :
    Compatible body (.inr (.inl ()) :: inputs.map liftInput)
      (Sum.elim (fun _ => firstArgument) firstNames) (Sum.elim (fun _ => secondArgument) secondNames)
      (shadow firstArgument replacement first) (shadow secondArgument replacement second) := by
  constructor
  · intro name member
    have captured := (SourceCurrentNativeNormalizedComparison.capture_support body inputs (.inl name)).mp member
    have alias := aliases (.inl name) captured
    change name = firstArgument ↔ name = secondArgument at alias
    by_cases left : name = firstArgument
    · have right := alias.mp left
      unfold shadow
      rw [if_pos left,if_pos right]
    · have right : name ≠ secondArgument := fun same => left (alias.mpr same)
      simp only [shadow,left,right,ite_false,compatible.1 name captured]
  · intro atom member
    cases atom with
    | inl token => simp only [Sum.elim_inl,shadow,ite_true]
    | inr atom =>
        have captured := (SourceCurrentNativeNormalizedComparison.capture_support body inputs (.inr atom)).mp member
        have alias := aliases (.inr atom) captured
        change firstNames atom = firstArgument ↔ secondNames atom = secondArgument at alias
        by_cases left : firstNames atom = firstArgument
        · have right := alias.mp left
          simp only [Sum.elim_inr,shadow,left,right,ite_true]
        · have right : secondNames atom ≠ secondArgument := fun same => left (alias.mpr same)
          simpa only [Sum.elim_inr,shadow,left,right,ite_false] using compatible.2 atom captured

/-- A Depth callback uses the existing Depth alias class instead of a freshness condition. -/
theorem extend_depth (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Reference → Profile)
    (compatible : Compatible (.binder true body) inputs firstNames secondNames first second)
    (aliases : Aliases (.binder true body) inputs firstNames secondNames) (replacement : Profile) :
    Compatible body (.inr (.inl ()) :: inputs.map liftInput)
      (Sum.elim (fun _ => .depth) firstNames) (Sum.elim (fun _ => .depth) secondNames)
      (shadow .depth replacement first) (shadow .depth replacement second) := by
  apply extend body inputs firstNames secondNames first second compatible .depth .depth replacement
  intro label member
  exact aliases label (List.mem_cons_of_mem _ member) (.inl .depth) List.mem_cons_self

/-- Two actual Depth callbacks supply live freshness for their ordinary profile extensions. -/
theorem publication_ordinary [DecidableEq (EdgeKey Symbol Guard)]
    (firstEvent secondEvent : Publication (Symbol := Symbol) (Guard := Guard))
    (sameBody : secondEvent.expression = firstEvent.expression)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (firstInputs : inputs.map (input firstNames) = firstEvent.environment)
    (secondInputs : inputs.map (input secondNames) = secondEvent.environment)
    (first second : Reference → Profile)
    (compatible : Compatible (.binder true firstEvent.expression) inputs firstNames secondNames first second)
    (replacement : Profile) :
    Compatible firstEvent.expression (.inr (.inl ()) :: inputs.map liftInput)
      (Sum.elim (fun _ => .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel firstEvent.depth)) firstNames)
      (Sum.elim (fun _ => .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel secondEvent.depth)) secondNames)
      (shadow (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel firstEvent.depth)) replacement first)
      (shadow (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel secondEvent.depth)) replacement second) := by
  have firstFresh := SourceCurrentNativeNormalizationFreshness.ordinary firstEvent.expression inputs firstNames
    firstEvent.before firstEvent.afterDepth (firstInputs ▸ firstEvent.context.base) firstEvent.depth
    (firstInputs ▸ firstEvent.depthDone)
  have secondFresh := SourceCurrentNativeNormalizationFreshness.ordinary firstEvent.expression inputs secondNames
    secondEvent.before secondEvent.afterDepth (secondInputs ▸ secondEvent.context.base) secondEvent.depth
    (by rw [← sameBody,secondInputs]; exact secondEvent.depthDone)
  apply extend firstEvent.expression inputs firstNames secondNames first second compatible _ _ replacement
  intro label member
  constructor
  · intro same
    exact False.elim (firstFresh (List.mem_map.mpr ⟨label,member,same⟩))
  · intro same
    exact False.elim (secondFresh (List.mem_map.mpr ⟨label,member,same⟩))

/-- One actual publication extends any outer assignment at its reserved and ordinary names. -/
theorem publication [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference)
    (presented : inputs.map (input names) = event.environment)
    (assignment : Reference → Profile) (replacement : Profile) :
    Compatible event.expression (.inr (.inl ()) :: inputs.map liftInput)
      (Sum.elim (fun _ => .interned event.entry.identity) names)
      (Sum.elim (fun _ => .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel event.depth)) names)
      (shadow (.interned event.entry.identity) replacement assignment)
      (shadow (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel event.depth)) replacement assignment) := by
  have ordinaryFresh := SourceCurrentNativeNormalizationFreshness.ordinary event.expression inputs names
    event.before event.afterDepth (presented ▸ event.context.base) event.depth (presented ▸ event.depthDone)
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have reservedFresh := SourceCurrentNativeNormalizationFreshness.reserved (.binder true event.expression)
    inputs names event.cut (presented ▸ cutContext.base) event.key event.missing
  apply extend event.expression inputs names names assignment assignment
    ⟨fun _ _ => rfl,fun _ _ => rfl⟩ _ _ replacement
  intro label member
  constructor
  · intro same
    apply False.elim
    apply reservedFresh
    exact List.mem_map.mpr ⟨label,member,by simpa only [SourceCurrentNativeMuPublication.Publication.entry] using same⟩
  · intro same
    exact False.elim (ordinaryFresh (List.mem_map.mpr ⟨label,member,same⟩))

end MicroCFTA.SourceCurrentScopedProfileInputs
