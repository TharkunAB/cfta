import MicroCFTA.InternedGuardedSyntax
import MicroCFTA.InternedGuardedLanguageSupport
import MicroCFTA.InternedStoredSubstitutionScope
import MicroCFTA.InternedStoredLeafShape

/-!
# Independent guarded language of the actual stored-plan compiler

Closed records are captured as exact canonical values. Local names read the
nearest lexical slot. Open Mu records compile to lexical least-language
binders. These laws concern the actual compiler, before source execution.
-/
namespace MicroCFTA.InternedGuardedStoredPlan
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedStoredSubstitution InternedStoredSubstitutionScope
open InternedBinderProtocol Language
open BinderLanguage (Lang)
open InternedGuardedLanguage (Env meaning)

/-- Local lexical languages shadow the external meaning at the nearest matching name. -/
def resolve (locals : List Reference) (localLanguages : List (Lang Symbol)) (environment : Env Symbol) : Env Symbol :=
  fun name => match locals.findIdx? (· == name) with
    | some index => localLanguages[index]?.getD (fun _ => False)
    | none => environment name

/-- An empty lexical scope reads the original ambient reference languages. -/
theorem resolve_nil (environment : Env Symbol) : resolve [] [] environment = environment := by
  funext name
  simp [resolve]

/-- A new lexical binder overrides exactly its own actual original name. -/
theorem resolve_cons (locals : List Reference) (localLanguages : List (Lang Symbol)) (environment : Env Symbol)
    (bound : Reference) (language : Lang Symbol) :
    resolve (bound :: locals) (language :: localLanguages) environment =
      InternedGuardedLanguage.bind (resolve locals localLanguages environment) bound language := by
  funext name
  by_cases same : bound = name
  · subst name
    simp [resolve, List.findIdx?_cons, InternedGuardedLanguage.bind]
  · simp only [resolve, List.findIdx?_cons, beq_eq_false_iff_ne.mpr same, ite_false,
      InternedGuardedLanguage.bind, Ne.symm same]
    cases locals.findIdx? (· == name) <;> rfl

/-- Canonical global slot lookup reads the independent meaning of the complete original record. -/
theorem global_lookup (holds : Guard → Term Symbol → Bool) (context : List (Value Symbol Guard)) (locals : List Reference)
    (localLanguages : List (Lang Symbol)) (environment : Env Symbol) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Values state context)
    (member : value ∈ context) (length : localLanguages.length = locals.length) :
    (localLanguages ++ context.map (meaning holds environment))[locals.length + slot context value]? =
      some (meaning holds environment value) := by
  rw [List.getElem?_append_right (by omega), length, Nat.add_sub_cancel_left, List.getElem?_map,
    slot_lookup context value state coherent available member]
  rfl

/-- Subtype witnesses and ordinary membership witnesses describe the same selected language. -/
theorem exists_member (values : List A) (predicate : A → Prop) :
    (∃ value : {value // value ∈ values}, predicate value.val) ↔ ∃ value ∈ values, predicate value := by
  constructor
  · rintro ⟨⟨value, member⟩, accepted⟩
    exact ⟨value, member, accepted⟩
  · rintro ⟨value, member, accepted⟩
    exact ⟨⟨value, member⟩, accepted⟩

mutual
/-- The actual stored compiler retains complete independent guarded meaning at every lexical scope. -/
theorem encode_language (holds : Guard → Term Symbol → Bool) (context : List (Value Symbol Guard))
    (locals : List Reference) (localLanguages : List (Lang Symbol)) (environment : Env Symbol) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (contextAvailable : Values state context)
    (available : Available state value) (covered : ∀ leaf ∈ leaves value, leaf ∈ context)
    (length : localLanguages.length = locals.length) :
    InternedGuardedSyntax.evaluate holds (localLanguages ++ context.map (meaning holds environment)) (encode context locals value) =
      meaning holds (resolve locals localLanguages environment) value := by
  rw [encode.eq_def]
  split
  · rename_i closed
    have member : value ∈ context := covered value (by rw [leaves.eq_def]; simp only [closed, ↓reduceIte, List.mem_singleton])
    rw [InternedGuardedSyntax.evaluate, global_lookup holds context locals localLanguages environment value state coherent contextAvailable member length]
    exact InternedGuardedLanguage.closed_meaning holds value state coherent available (List.isEmpty_iff.mp closed)
      environment (resolve locals localLanguages environment)
  · rename_i opened
    rw [leaves.eq_def] at covered
    simp only [opened, Bool.false_eq_true, ↓reduceIte] at covered
    cases value with
    | empty => simp [Value.free] at opened
    | reference name =>
        have member : Value.reference name ∈ context := covered _ (by simp)
        cases found : locals.findIdx? (· == name) with
        | none =>
            simp only [found]
            rw [InternedGuardedSyntax.evaluate, global_lookup holds context locals localLanguages environment _ state coherent contextAvailable member length]
            simp only [meaning, resolve, found, Option.getD_some]
        | some index =>
            simp only [found]
            have bound : index < localLanguages.length := by
              rw [length]
              exact (List.findIdx?_eq_some_iff_findIdx_eq.mp found).1
            rw [InternedGuardedSyntax.evaluate, List.getElem?_append_left bound]
            simp only [meaning, resolve, found]
    | node entry edges depth free =>
        funext term
        simp only [InternedGuardedSyntax.evaluate, meaning]
        apply propext
        exact (exists_member (encodeEdges context locals edges) _).trans
          ((encodeEdges_language holds context locals localLanguages environment edges state coherent contextAvailable
            (fun edge selected child member => available.children child (List.mem_flatMap.mpr ⟨edge, selected, member⟩)) covered length term).trans
            (exists_member edges _).symm)
    | union entry members depth free =>
        funext term
        simp only [InternedGuardedSyntax.evaluate, meaning]
        apply propext
        exact (exists_member (encodeMany context locals members) _).trans
          ((encodeAlternatives_language holds context locals localLanguages environment members state coherent contextAvailable
            (fun member selected => available.children member selected) covered length term).trans
            (exists_member members _).symm)
    | mu entry body depth ordinary =>
        rw [InternedGuardedSyntax.evaluate, meaning]
        apply BinderLanguage.least_congr
        intro language term
        have compiled := encode_language holds context (.interned entry.identity :: locals) (language :: localLanguages) environment body
          state coherent contextAvailable (available.children body (by simp [children])) covered (by simp [length])
        simpa only [List.cons_append, resolve_cons] using iff_of_eq (congrFun compiled term)
termination_by sizeOf value
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega

/-- Compiling an ordered stored child forest retains all guarded child languages and their positions. -/
theorem encodeMany_language (holds : Guard → Term Symbol → Bool) (context : List (Value Symbol Guard))
    (locals : List Reference) (localLanguages : List (Lang Symbol)) (environment : Env Symbol) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (contextAvailable : Values state context)
    (available : Values state values) (covered : ∀ leaf ∈ manyLeaves values, leaf ∈ context)
    (length : localLanguages.length = locals.length) (terms : List (Term Symbol)) :
    InternedGuardedSyntax.forest holds (localLanguages ++ context.map (meaning holds environment)) (encodeMany context locals values) terms ↔
      InternedGuardedLanguage.forest holds (resolve locals localLanguages environment) values terms := by
  cases values with
  | nil => cases terms <;> simp only [encodeMany, InternedGuardedSyntax.forest, InternedGuardedLanguage.forest]
  | cons value rest =>
      rw [manyLeaves] at covered
      have own := available value List.mem_cons_self
      have tail : Values state rest := fun child member => available child (List.mem_cons_of_mem _ member)
      have ownCovered : ∀ leaf ∈ leaves value, leaf ∈ context := fun leaf member => covered leaf (List.mem_append_left _ member)
      have tailCovered : ∀ leaf ∈ manyLeaves rest, leaf ∈ context := fun leaf member => covered leaf (List.mem_append_right _ member)
      cases terms with
      | nil => simp only [encodeMany, InternedGuardedSyntax.forest, InternedGuardedLanguage.forest]
      | cons term terms =>
          rw [encodeMany, InternedGuardedSyntax.forest, InternedGuardedLanguage.forest]
          exact and_congr (iff_of_eq (congrFun (encode_language holds context locals localLanguages environment value state coherent
              contextAvailable own ownCovered length) term))
            (encodeMany_language holds context locals localLanguages environment rest state coherent contextAvailable tail tailCovered length terms)
termination_by sizeOf values
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega

/-- Compiling stored union alternatives retains precisely their original independent languages. -/
theorem encodeAlternatives_language (holds : Guard → Term Symbol → Bool) (context : List (Value Symbol Guard))
    (locals : List Reference) (localLanguages : List (Lang Symbol)) (environment : Env Symbol) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (contextAvailable : Values state context)
    (available : Values state values) (covered : ∀ leaf ∈ manyLeaves values, leaf ∈ context)
    (length : localLanguages.length = locals.length) (term : Term Symbol) :
    (∃ member ∈ encodeMany context locals values, InternedGuardedSyntax.evaluate holds
      (localLanguages ++ context.map (meaning holds environment)) member term) ↔
      ∃ member ∈ values, meaning holds (resolve locals localLanguages environment) member term := by
  cases values with
  | nil => simp only [encodeMany, List.not_mem_nil, false_and, exists_false]
  | cons value rest =>
      rw [manyLeaves] at covered
      have own := available value List.mem_cons_self
      have tail : Values state rest := fun child member => available child (List.mem_cons_of_mem _ member)
      have ownCovered : ∀ leaf ∈ leaves value, leaf ∈ context := fun leaf member => covered leaf (List.mem_append_left _ member)
      have tailCovered : ∀ leaf ∈ manyLeaves rest, leaf ∈ context := fun leaf member => covered leaf (List.mem_append_right _ member)
      rw [encodeMany]
      simp only [List.mem_cons, exists_eq_or_imp]
      exact or_congr (iff_of_eq (congrFun (encode_language holds context locals localLanguages environment value state coherent
          contextAvailable own ownCovered length) term))
        (encodeAlternatives_language holds context locals localLanguages environment rest state coherent contextAvailable tail tailCovered length term)
termination_by sizeOf values
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega

/-- Compiling complete stored edge lists retains full guards, symbols, and ordered child languages. -/
theorem encodeEdges_language (holds : Guard → Term Symbol → Bool) (context : List (Value Symbol Guard))
    (locals : List Reference) (localLanguages : List (Lang Symbol)) (environment : Env Symbol) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (contextAvailable : Values state context)
    (available : ∀ edge ∈ edges, Values state edge.children) (covered : ∀ leaf ∈ edgeLeaves edges, leaf ∈ context)
    (length : localLanguages.length = locals.length) (term : Term Symbol) :
    (∃ edge ∈ encodeEdges context locals edges, InternedGuardedSyntax.edgeMeaning holds
      (localLanguages ++ context.map (meaning holds environment)) edge term) ↔
      ∃ edge ∈ edges, InternedGuardedLanguage.edgeMeaning holds (resolve locals localLanguages environment) edge term := by
  cases edges with
  | nil => simp only [encodeEdges, List.not_mem_nil, false_and, exists_false]
  | cons edge rest =>
      cases edge with
      | mk entry children =>
          rw [edgeLeaves] at covered
          have own := available (.mk entry children) List.mem_cons_self
          have tail : ∀ edge ∈ rest, Values state edge.children := fun edge member => available edge (List.mem_cons_of_mem _ member)
          have ownCovered : ∀ leaf ∈ manyLeaves children, leaf ∈ context := fun leaf member => covered leaf (List.mem_append_left _ member)
          have tailCovered : ∀ leaf ∈ edgeLeaves rest, leaf ∈ context := fun leaf member => covered leaf (List.mem_append_right _ member)
          have head : InternedGuardedSyntax.edgeMeaning holds (localLanguages ++ context.map (meaning holds environment))
              (.mk entry.key.symbol entry.key.constraint (encodeMany context locals children)) term ↔
              InternedGuardedLanguage.edgeMeaning holds (resolve locals localLanguages environment) (.mk entry children) term := by
            simp only [InternedGuardedSyntax.edgeMeaning, InternedGuardedLanguage.edgeMeaning]
            exact exists_congr (fun terms => and_congr Iff.rfl (and_congr
              (encodeMany_language holds context locals localLanguages environment children state coherent contextAvailable own ownCovered length terms) Iff.rfl))
          rw [encodeEdges]
          simp only [List.mem_cons, exists_eq_or_imp]
          exact or_congr head (encodeEdges_language holds context locals localLanguages environment rest state coherent contextAvailable tail tailCovered length term)
termination_by sizeOf edges
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega
end

/-- Simultaneous substitution gives each original free name the ambient meaning of its actual replacement. -/
def replacementEnv (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (replacements : Environment Symbol Guard) : Env Symbol :=
  fun name => meaning holds environment ((replacements name).getD (.reference name))

/-- The actual stored substitution plan has precisely the intended capture-free simultaneous-substitution language. -/
theorem execute_plan_language (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (value : Value Symbol Guard) (replacements : Environment Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) :
    InternedGuardedSyntax.evaluate holds
      ((leaves value).map (fun leaf => meaning holds environment (input replacements leaf))) (encode (leaves value) [] value) =
      meaning holds (replacementEnv holds environment replacements) value := by
  have leavesAvailable := leaves_available value state available
  have inputs : (leaves value).map (fun leaf => meaning holds environment (input replacements leaf)) =
      (leaves value).map (meaning holds (replacementEnv holds environment replacements)) := by
    apply List.map_congr_left
    intro leaf member
    rcases InternedStoredLeafShape.leaves_shape value leaf member with closed | ⟨name, rfl⟩
    · rw [input_closed leaf replacements closed]
      exact InternedGuardedLanguage.closed_meaning holds leaf state coherent (leavesAvailable leaf member) closed _ _
    · simp only [input, meaning, replacementEnv]
  rw [inputs]
  simpa only [List.nil_append, resolve_nil] using
    encode_language holds (leaves value) [] [] (replacementEnv holds environment replacements) value state coherent
      leavesAvailable available (fun _ member => member) rfl

/-- The actual outer-Mu unfolding plan has exactly the independent least-language meaning of that Mu. -/
theorem unfold_plan_language (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state body) :
    InternedGuardedSyntax.evaluate holds
      ((leaves body).map (fun leaf => meaning holds environment
        (input (fun name => if name = .interned entry.identity then some (.mu entry body depth ordinary) else none) leaf)))
      (encode (leaves body) [] body) = meaning holds environment (.mu entry body depth ordinary) := by
  rw [execute_plan_language holds environment body _ state coherent available]
  have same : replacementEnv holds environment
      (fun name => if name = .interned entry.identity then some (.mu entry body depth ordinary) else none) =
      InternedGuardedLanguage.bind environment (.interned entry.identity) (meaning holds environment (.mu entry body depth ordinary)) := by
    funext name
    by_cases equal : name = .interned entry.identity
    · simp only [replacementEnv, equal, ↓reduceIte, Option.getD_some, InternedGuardedLanguage.bind]
    · simp only [replacementEnv, equal, ↓reduceIte, Option.getD_none, meaning, InternedGuardedLanguage.bind]
  rw [same]
  funext term
  exact propext (InternedGuardedLanguage.mu_unfold holds environment entry body depth ordinary term).symm

end MicroCFTA.InternedGuardedStoredPlan
