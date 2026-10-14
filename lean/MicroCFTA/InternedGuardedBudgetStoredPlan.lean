import MicroCFTA.InternedGuardedBudgetSyntax
import MicroCFTA.InternedGuardedBudgetSupport
import MicroCFTA.InternedStoredSubstitutionScope
import MicroCFTA.InternedStoredLeafShape
import MicroCFTA.InternedGuardedStoredPlan

/-!
# Raw unfolding budgets of the actual stored-plan compiler

Closed records retain their complete budget languages. Local names read the
nearest lexical slot. Open Mu records compile to raw step-counted binders.
These laws describe the actual compiler before smart source execution.
-/
namespace MicroCFTA.InternedGuardedBudgetStoredPlan
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedStoredSubstitution InternedStoredSubstitutionScope
open InternedBinderProtocol Language
open BinderBudgetLanguage (Lang)
open InternedGuardedBudget (Env meaning)
open InternedGuardedStoredPlan (exists_member)

/-- Local lexical languages shadow the external meaning at the nearest matching name. -/
def resolve (locals : List Reference) (localLanguages : List (Lang Symbol)) (environment : Env Symbol) : Env Symbol :=
  fun name => match locals.findIdx? (· == name) with
    | some index => localLanguages[index]?.getD (fun _ _ => False)
    | none => environment name

/-- An empty lexical scope reads the original ambient reference languages. -/
theorem resolve_nil (environment : Env Symbol) : resolve [] [] environment = environment := by
  funext name
  simp [resolve]

/-- A new lexical binder overrides exactly its own actual original name. -/
theorem resolve_cons (locals : List Reference) (localLanguages : List (Lang Symbol)) (environment : Env Symbol)
    (bound : Reference) (language : Lang Symbol) :
    resolve (bound :: locals) (language :: localLanguages) environment =
      InternedGuardedBudget.bind (resolve locals localLanguages environment) bound language := by
  funext name
  by_cases same : bound = name
  · subst name
    simp [resolve, List.findIdx?_cons, InternedGuardedBudget.bind]
  · simp only [resolve, List.findIdx?_cons, beq_eq_false_iff_ne.mpr same, ite_false,
      InternedGuardedBudget.bind, Ne.symm same]
    cases locals.findIdx? (· == name) <;> rfl

/-- Canonical global slot lookup retains the original record at every budget. -/
theorem global_lookup (holds : Guard → Term Symbol → Bool) (context : List (Value Symbol Guard)) (locals : List Reference)
    (localLanguages : List (Lang Symbol)) (environment : Env Symbol) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Values state context)
    (member : value ∈ context) (length : localLanguages.length = locals.length) :
    (localLanguages ++ context.map (meaning holds environment))[locals.length + slot context value]? =
      some (meaning holds environment value) := by
  rw [List.getElem?_append_right (by omega), length, Nat.add_sub_cancel_left, List.getElem?_map,
    slot_lookup context value state coherent available member]
  rfl

mutual
/-- The actual stored compiler retains each raw unfolding budget at every lexical scope. -/
theorem encode_language (holds : Guard → Term Symbol → Bool) (context : List (Value Symbol Guard))
    (locals : List Reference) (localLanguages : List (Lang Symbol)) (environment : Env Symbol) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (contextAvailable : Values state context)
    (available : Available state value) (covered : ∀ leaf ∈ leaves value, leaf ∈ context)
    (length : localLanguages.length = locals.length) :
    InternedGuardedBudgetSyntax.evaluate holds (localLanguages ++ context.map (meaning holds environment)) (encode context locals value) =
      meaning holds (resolve locals localLanguages environment) value := by
  rw [encode.eq_def]
  split
  · rename_i closed
    have member : value ∈ context := covered value (by rw [leaves.eq_def]; simp only [closed, ↓reduceIte, List.mem_singleton])
    rw [InternedGuardedBudgetSyntax.evaluate, global_lookup holds context locals localLanguages environment value state coherent contextAvailable member length]
    exact InternedGuardedBudget.closed_meaning holds value state coherent available (List.isEmpty_iff.mp closed)
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
            rw [InternedGuardedBudgetSyntax.evaluate, global_lookup holds context locals localLanguages environment _ state coherent contextAvailable member length]
            simp only [meaning, resolve, found, Option.getD_some]
        | some index =>
            simp only [found]
            have bound : index < localLanguages.length := by
              rw [length]
              exact (List.findIdx?_eq_some_iff_findIdx_eq.mp found).1
            rw [InternedGuardedBudgetSyntax.evaluate, List.getElem?_append_left bound]
            simp only [meaning, resolve, found]
    | node entry edges depth free =>
        funext budget term
        simp only [InternedGuardedBudgetSyntax.evaluate, meaning]
        apply propext
        exact (exists_member (encodeEdges context locals edges) _).trans
          ((encodeEdges_language holds context locals localLanguages environment edges state coherent contextAvailable
            (fun edge selected child member => available.children child (List.mem_flatMap.mpr ⟨edge, selected, member⟩)) covered length budget term).trans
            (exists_member edges _).symm)
    | union entry members depth free =>
        funext budget term
        simp only [InternedGuardedBudgetSyntax.evaluate, meaning]
        apply propext
        exact (exists_member (encodeMany context locals members) _).trans
          ((encodeAlternatives_language holds context locals localLanguages environment members state coherent contextAvailable
            (fun member selected => available.children member selected) covered length budget term).trans
            (exists_member members _).symm)
    | mu entry body depth ordinary =>
        rw [InternedGuardedBudgetSyntax.evaluate, meaning]
        apply congrArg BinderBudgetLanguage.mu
        funext language
        have compiled := encode_language holds context (.interned entry.identity :: locals) (language :: localLanguages) environment body
          state coherent contextAvailable (available.children body (by simp [children])) covered (by simp [length])
        simpa only [List.cons_append, resolve_cons] using compiled
termination_by sizeOf value
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega

/-- Compiling ordered children retains their guards, positions, and common budget. -/
theorem encodeMany_language (holds : Guard → Term Symbol → Bool) (context : List (Value Symbol Guard))
    (locals : List Reference) (localLanguages : List (Lang Symbol)) (environment : Env Symbol) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (contextAvailable : Values state context)
    (available : Values state values) (covered : ∀ leaf ∈ manyLeaves values, leaf ∈ context)
    (length : localLanguages.length = locals.length) (budget : Nat) (terms : List (Term Symbol)) :
    InternedGuardedBudgetSyntax.forest holds (localLanguages ++ context.map (meaning holds environment)) budget (encodeMany context locals values) terms ↔
      InternedGuardedBudget.forest holds (resolve locals localLanguages environment) budget values terms := by
  cases values with
  | nil => cases terms <;> simp only [encodeMany, InternedGuardedBudgetSyntax.forest, InternedGuardedBudget.forest]
  | cons value rest =>
      rw [manyLeaves] at covered
      have own := available value List.mem_cons_self
      have tail : Values state rest := fun child member => available child (List.mem_cons_of_mem _ member)
      have ownCovered : ∀ leaf ∈ leaves value, leaf ∈ context := fun leaf member => covered leaf (List.mem_append_left _ member)
      have tailCovered : ∀ leaf ∈ manyLeaves rest, leaf ∈ context := fun leaf member => covered leaf (List.mem_append_right _ member)
      cases terms with
      | nil => simp only [encodeMany, InternedGuardedBudgetSyntax.forest, InternedGuardedBudget.forest]
      | cons term terms =>
          rw [encodeMany, InternedGuardedBudgetSyntax.forest, InternedGuardedBudget.forest]
          exact and_congr (iff_of_eq (congrFun (congrFun (encode_language holds context locals localLanguages environment value state coherent
              contextAvailable own ownCovered length) budget) term))
            (encodeMany_language holds context locals localLanguages environment rest state coherent contextAvailable tail tailCovered length budget terms)
termination_by sizeOf values
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega

/-- Compiling stored union alternatives retains their languages at the same bound. -/
theorem encodeAlternatives_language (holds : Guard → Term Symbol → Bool) (context : List (Value Symbol Guard))
    (locals : List Reference) (localLanguages : List (Lang Symbol)) (environment : Env Symbol) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (contextAvailable : Values state context)
    (available : Values state values) (covered : ∀ leaf ∈ manyLeaves values, leaf ∈ context)
    (length : localLanguages.length = locals.length) (budget : Nat) (term : Term Symbol) :
    (∃ member ∈ encodeMany context locals values, InternedGuardedBudgetSyntax.evaluate holds
      (localLanguages ++ context.map (meaning holds environment)) member budget term) ↔
      ∃ member ∈ values, meaning holds (resolve locals localLanguages environment) member budget term := by
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
      exact or_congr (iff_of_eq (congrFun (congrFun (encode_language holds context locals localLanguages environment value state coherent
          contextAvailable own ownCovered length) budget) term))
        (encodeAlternatives_language holds context locals localLanguages environment rest state coherent contextAvailable tail tailCovered length budget term)
termination_by sizeOf values
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega

/-- Compiling complete stored edges retains guards, symbols, and ordered child budgets. -/
theorem encodeEdges_language (holds : Guard → Term Symbol → Bool) (context : List (Value Symbol Guard))
    (locals : List Reference) (localLanguages : List (Lang Symbol)) (environment : Env Symbol) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (contextAvailable : Values state context)
    (available : ∀ edge ∈ edges, Values state edge.children) (covered : ∀ leaf ∈ edgeLeaves edges, leaf ∈ context)
    (length : localLanguages.length = locals.length) (budget : Nat) (term : Term Symbol) :
    (∃ edge ∈ encodeEdges context locals edges, InternedGuardedBudgetSyntax.edgeMeaning holds
      (localLanguages ++ context.map (meaning holds environment)) edge budget term) ↔
      ∃ edge ∈ edges, InternedGuardedBudget.edgeMeaning holds (resolve locals localLanguages environment) edge budget term := by
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
          have head : InternedGuardedBudgetSyntax.edgeMeaning holds (localLanguages ++ context.map (meaning holds environment))
              (.mk entry.key.symbol entry.key.constraint (encodeMany context locals children)) budget term ↔
              InternedGuardedBudget.edgeMeaning holds (resolve locals localLanguages environment) (.mk entry children) budget term := by
            simp only [InternedGuardedBudgetSyntax.edgeMeaning, InternedGuardedBudget.edgeMeaning]
            exact exists_congr (fun terms => and_congr Iff.rfl (and_congr
              (encodeMany_language holds context locals localLanguages environment children state coherent contextAvailable own ownCovered length budget terms) Iff.rfl))
          rw [encodeEdges]
          simp only [List.mem_cons, exists_eq_or_imp]
          exact or_congr head (encodeEdges_language holds context locals localLanguages environment rest state coherent contextAvailable tail tailCovered length budget term)
termination_by sizeOf edges
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega
end

/-- Simultaneous substitution gives each original free name the ambient meaning of its actual replacement. -/
def replacementEnv (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (replacements : Environment Symbol Guard) : Env Symbol :=
  fun name => meaning holds environment ((replacements name).getD (.reference name))

/-- The actual simultaneous-substitution plan retains the raw replacement budget languages. -/
theorem execute_plan_language (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (value : Value Symbol Guard) (replacements : Environment Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) :
    InternedGuardedBudgetSyntax.evaluate holds
      ((leaves value).map (fun leaf => meaning holds environment (input replacements leaf))) (encode (leaves value) [] value) =
      meaning holds (replacementEnv holds environment replacements) value := by
  have leavesAvailable := leaves_available value state available
  have inputs : (leaves value).map (fun leaf => meaning holds environment (input replacements leaf)) =
      (leaves value).map (meaning holds (replacementEnv holds environment replacements)) := by
    apply List.map_congr_left
    intro leaf member
    rcases InternedStoredLeafShape.leaves_shape value leaf member with closed | ⟨name, rfl⟩
    · rw [input_closed leaf replacements closed]
      exact InternedGuardedBudget.closed_meaning holds leaf state coherent (leavesAvailable leaf member) closed _ _
    · simp only [input, meaning, replacementEnv]
  rw [inputs]
  simpa only [List.nil_append, resolve_nil] using
    encode_language holds (leaves value) [] [] (replacementEnv holds environment replacements) value state coherent
      leavesAvailable available (fun _ member => member) rfl

/-- Adding one raw Mu step to the actual outer-unfolding plan gives the original budget language. -/
theorem unfold_plan_shift (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state body) :
    BinderBudgetLanguage.shift (InternedGuardedBudgetSyntax.evaluate holds
      ((leaves body).map (fun leaf => meaning holds environment
        (input (fun name => if name = .interned entry.identity then some (.mu entry body depth ordinary) else none) leaf)))
      (encode (leaves body) [] body)) = meaning holds environment (.mu entry body depth ordinary) := by
  rw [execute_plan_language holds environment body _ state coherent available]
  have same : replacementEnv holds environment
      (fun name => if name = .interned entry.identity then some (.mu entry body depth ordinary) else none) =
      InternedGuardedBudget.bind environment (.interned entry.identity) (meaning holds environment (.mu entry body depth ordinary)) := by
    funext name
    by_cases equal : name = .interned entry.identity
    · simp only [replacementEnv, equal, ↓reduceIte, Option.getD_some, InternedGuardedBudget.bind]
    · simp only [replacementEnv, equal, ↓reduceIte, Option.getD_none, meaning, InternedGuardedBudget.bind]
  rw [same]
  funext budget term
  exact propext (InternedGuardedBudget.mu_unfold holds environment entry body depth ordinary budget term).symm

/-- Every accepted actual Mu has an exact compiled unfolding plan at a strictly smaller bound. -/
theorem unfold_plan_lower (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state body) (budget : Nat) (term : Term Symbol)
    (accepted : meaning holds environment (.mu entry body depth ordinary) budget term) :
    ∃ smaller, smaller < budget ∧ InternedGuardedBudgetSyntax.evaluate holds
      ((leaves body).map (fun leaf => meaning holds environment
        (input (fun name => if name = .interned entry.identity then some (.mu entry body depth ordinary) else none) leaf)))
      (encode (leaves body) [] body) smaller term := by
  change BinderBudgetLanguage.shift _ budget term
  rw [unfold_plan_shift holds environment entry body depth ordinary state coherent available]
  exact accepted

end MicroCFTA.InternedGuardedBudgetStoredPlan
