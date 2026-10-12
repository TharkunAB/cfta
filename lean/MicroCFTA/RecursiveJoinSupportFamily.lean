import MicroCFTA.RecursiveJoinSupportBody

/-!
# Actual shared support binders for typed mutual join families

One binder contains every keyed Family edge. Each recursive occurrence and
public member uses the source AtKey restriction. Least-language reasoning
and finite source derivations establish both directions of correspondence.
-/
namespace MicroCFTA.RecursiveJoinSupportFamily
open Language GeneratorCombinators BinderLanguage SupportGraph
open RecursiveCallbackTermination (EngineTerm)
open RecursiveJoinSupportSemantics RecursiveJoinSupportBody

/-- Forget support fields after each source constructor has proved its local correspondence. -/
def lower (program : Key → Body Key Root Symbol Root) : Key → RecursiveJoinComposition.Body Key Root Symbol Root :=
  fun key => (program key).checked.body

/-- Each key has an independent private term recipe with the complete source member boundary. -/
def termProgram (code : Key → Nat) (program : Key → Body Key Root Symbol Root) :=
  RecursiveJoinFamily.termProgram code (lower program)

/-- Every supplied key contributes its own complete open body support. -/
def keyed (token : Nat) (code : Key → Nat) (keys : List Key) (program : Key → Body Key Root Symbol Root) :
    List (Nat × Support Symbol) :=
  keys.map fun key => (code key, ((program key).support token code).graph)

/-- The source ties the complete keyed family with one shared recursive binder. -/
def graph (token : Nat) (code : Key → Nat) (keys : List Key) (program : Key → Body Key Root Symbol Root) : Support Symbol :=
  .binder token (family (keyed token code keys program))

/-- The public support of one key retains the same AtKey equality as every recursive occurrence. -/
def memberGraph (token : Nat) (code : Key → Nat) (keys : List Key) (program : Key → Body Key Root Symbol Root) (key : Key) : Support Symbol :=
  restrictKey (code key) (graph token code keys program)

/-- A complete source family term retains a finite derivation of its own body. -/
def familyLanguage (code : Key → Nat) (program : Key → Body Key Root Symbol Root) (term : EngineTerm Symbol) : Prop :=
  ∃ key body size, KeyedSource.Derives (termProgram code program) (program key).checked.body.term body size ∧
    term = familyTerm (code key) body

/-- An open occurrence over finite family derivations is exactly the selected source key language. -/
theorem root_members (token : Nat) (code : Key → Nat) (injective : Function.Injective code)
    (program : Key → Body Key Root Symbol Root) (environment : Env (Label Symbol)) (key : Key) (term : EngineTerm Symbol) :
    rootLanguage token code (bind environment token (familyLanguage code program)) key term ↔
      members (termProgram code program) key term := by
  rw [rootLanguage, restrict_exact]
  simp only [meaning, BinderLanguage.bind, ite_true]
  constructor
  · rintro ⟨child, ⟨other, body, size, derived, rfl⟩, keyFound, rfl⟩
    have same : code other = code key := by simpa [familyTerm, Term.atPath] using keyFound
    have keySame := injective same
    subst other
    exact ⟨size, .map (KeyedTermBoundary.atKeyTerm (code key)) (program key).checked.body.term body size derived⟩
  · rintro ⟨size, derived⟩
    change KeyedSource.Derives (termProgram code program)
      (.map (KeyedTermBoundary.atKeyTerm (code key)) (program key).checked.body.term) term size at derived
    cases derived with
    | map transform inner body size child =>
        exact ⟨familyTerm (code key) body, ⟨key, body, size, child, rfl⟩, by simp [familyTerm, Term.atPath], rfl⟩

/-- Finite source derivations form a closed candidate for the actual shared support binder. -/
theorem family_closed (token : Nat) (code : Key → Nat) (injective : Function.Injective code)
    (keys : List Key) (program : Key → Body Key Root Symbol Root) (environment : Env (Label Symbol)) :
    Included (meaning (bind environment token (familyLanguage code program)) (family (keyed token code keys program)))
      (familyLanguage code program) := by
  intro term accepted
  obtain ⟨index, support, present, body, bodyAccepted, rfl⟩ := (family_exact _ _ term).mp accepted
  obtain ⟨key, _, same⟩ := List.mem_map.mp present
  cases same
  have denoted := ((program key).exact token code _ body).mp bodyAccepted
  have member := (denotes_congr (program key).checked.body.term _ _
    (root_members token code injective program environment) body).mp denoted
  obtain ⟨size, derived⟩ := denotes_derives (termProgram code program) _ body member
  exact ⟨key, body, size, derived, rfl⟩

/-- The actual support binder cannot add a family member without a finite typed derivation. -/
theorem graph_sound (token : Nat) (code : Key → Nat) (injective : Function.Injective code)
    (keys : List Key) (program : Key → Body Key Root Symbol Root) (environment : Env (Label Symbol))
    (term : EngineTerm Symbol) (accepted : meaning environment (graph token code keys program) term) :
    familyLanguage code program term := by
  simp only [graph, meaning] at accepted
  exact least_le _ (familyLanguage code program)
    (family_closed token code injective keys program environment) term accepted

/-- Rebinding the shared reference to the tied graph gives its exact member support language. -/
theorem roots_tied (token : Nat) (code : Key → Nat) (keys : List Key)
    (program : Key → Body Key Root Symbol Root) (environment : Env (Label Symbol)) (key : Key) (term : EngineTerm Symbol) :
    rootLanguage token code (bind environment token (meaning environment (graph token code keys program))) key term ↔
      meaning environment (memberGraph token code keys program key) term := by
  simp [rootLanguage, memberGraph, restrict_exact, meaning, BinderLanguage.bind]

/-- The source member supports are closed under the full independently compiled body recipes. -/
theorem members_closed (token : Nat) (code : Key → Nat) (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Body Key Root Symbol Root) (environment : Env (Label Symbol)) (key : Key) (term : EngineTerm Symbol) :
    denotes (termProgram code program key) (fun key => meaning environment (memberGraph token code keys program key)) term →
      meaning environment (memberGraph token code keys program key) term := by
  rintro ⟨body, bodyAccepted, rfl⟩
  have denoted := (denotes_congr (program key).checked.body.term _ _ (roots_tied token code keys program environment) body).mpr bodyAccepted
  have supportAccepted := ((program key).exact token code _ body).mpr denoted
  have familyAccepted : meaning environment (graph token code keys program) (familyTerm (code key) body) := by
    apply (binder_unfold environment token _ _).mpr
    apply (family_exact _ _ _).mpr
    exact ⟨code key, _, List.mem_map.mpr ⟨key, complete key, rfl⟩, body, supportAccepted, rfl⟩
  apply (restrict_exact environment (code key) _ _).mpr
  exact ⟨familyTerm (code key) body, familyAccepted, by simp [familyTerm, Term.atPath], rfl⟩

/-- Every finite typed derivation belongs to the actual shared-binder member graph. -/
theorem member_complete (token : Nat) (code : Key → Nat) (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Body Key Root Symbol Root) (environment : Env (Label Symbol)) (key : Key)
    (term : EngineTerm Symbol) (derived : members (termProgram code program) key term) :
    meaning environment (memberGraph token code keys program key) term := by
  obtain ⟨size, derivation⟩ := derived
  exact members_closed token code keys complete program environment key term
    (derives_closed (termProgram code program) _ (members_closed token code keys complete program environment)
      _ term size derivation)

/-- The actual constrained member graph accepts exactly the key's finite typed derivations. -/
theorem member_exact (token : Nat) (code : Key → Nat) (injective : Function.Injective code)
    (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Body Key Root Symbol Root)
    (environment : Env (Label Symbol)) (key : Key) (term : EngineTerm Symbol) :
    meaning environment (memberGraph token code keys program key) term ↔ members (termProgram code program) key term := by
  constructor
  · intro accepted
    obtain ⟨child, acceptedChild, keyFound, same⟩ := (restrict_exact _ _ _ _).mp accepted
    have candidate := graph_sound token code injective keys program environment child acceptedChild
    apply (root_members token code injective program environment key term).mp
    apply (restrict_exact _ _ _ _).mpr
    exact ⟨child, by simpa [meaning, BinderLanguage.bind] using candidate, keyFound, same⟩
  · exact member_complete token code keys complete program environment key term

/-- Guarded independent term classes enumerate exactly the whole source member support. -/
theorem family_exact (token : Nat) (code : Key → Nat) (injective : Function.Injective code)
    (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Body Key Root Symbol Root)
    (accepted : ∀ key, KeyedSource.guarded (RecursiveJoinFamily.valueProgram (lower program) key)
      (KeyedSource.minima keys complete (RecursiveJoinFamily.valueProgram (lower program))) = true)
    (environment : Env (Label Symbol)) (key : Key) (term : EngineTerm Symbol) :
    meaning environment (memberGraph token code keys program key) term ↔
      ∃ size, term ∈ Decoder.values (KeyedSource.family (termProgram code program) size key).members.plan := by
  rw [member_exact token code injective keys complete program environment key term]
  simp only [members, KeyedSource.family_exact keys complete (termProgram code program)
    (RecursiveJoinFamily.family_guards keys complete code (lower program) accepted).2]

/-- Every independently selected private term is accepted by its actual source support. -/
theorem selected_accepted (token : Nat) (code : Key → Nat) (injective : Function.Injective code)
    (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Body Key Root Symbol Root)
    (accepted : ∀ key, KeyedSource.guarded (RecursiveJoinFamily.valueProgram (lower program) key)
      (KeyedSource.minima keys complete (RecursiveJoinFamily.valueProgram (lower program))) = true)
    (environment : Env (Label Symbol)) (key : Key) (size rank : Nat) (term : EngineTerm Symbol)
    (selected : Decoder.decode (KeyedSource.family (termProgram code program) size key).members.plan rank = some term) :
    meaning environment (memberGraph token code keys program key) term := by
  apply (family_exact token code injective keys complete program accepted environment key term).mpr
  rw [Decoder.decode_correct] at selected
  exact ⟨size, List.mem_of_getElem? selected⟩

end MicroCFTA.RecursiveJoinSupportFamily
