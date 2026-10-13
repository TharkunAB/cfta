import MicroCFTA.SourceSubstitutionPrecedence

/-!
# Forward environments through accepted identity quotients

A quotient may identify fresh actual names and remove identity replacements.
The proof uses the source's two scope checks and first non-identity lookup.
It does not require an injective name map or reverse environment transport.
-/
namespace MicroCFTA.SourceQuotientEnvironment
open FullSyntax FormulaSubstitution SourceFormula SourceScopeEnvironment
open SourceGuards (Resolved)
abbrev Scope := List (Resolved Formula)

/-- Local record invariants for the two allocations of one source actual. -/
structure Pair (ambient : List Name) (old new : Resolved Formula) : Prop where
  symbols : new.symbolReplacement = old.symbolReplacement
  oldFormal : old.replacement.1 = old.symbolReplacement.1
  newFormal : new.replacement.1 = old.symbolReplacement.1
  formalLive : old.symbolReplacement.1 ∈ ambient
  actualLive : old.symbolReplacement.2 ∈ ambient
  oldShape : old.replacement.2 = old.symbolReplacement.2 ∨ old.replacement.2 ∉ ambient
  newShape : new.replacement.2 = old.symbolReplacement.2 ∨ new.replacement.2 ∉ ambient
  retained : old.replacement.2 = old.symbolReplacement.2 → new.replacement.2 = old.symbolReplacement.2
  becomesOriginal : old.replacement.2 ≠ old.symbolReplacement.2 →
    new.replacement.2 = old.symbolReplacement.2 → old.identityKnown = false

/-- An identity source entry remains an identity after the quotient. -/
theorem identity_forward (paired : Pair ambient old new)
    (identity : old.replacement.1 = old.replacement.2) : new.replacement.1 = new.replacement.2 := by
  have live : old.replacement.2 ∈ ambient := identity ▸ (paired.oldFormal ▸ paired.formalLive)
  have original := paired.oldShape.resolve_right (fun outside => outside live)
  rw [paired.newFormal, paired.retained original, ← original, ← identity, paired.oldFormal]

/-- A newly removed identity has exactly the literal shape inspected by the source check. -/
theorem identity_changed (paired : Pair ambient old new)
    (active : old.replacement.1 ≠ old.replacement.2)
    (identity : new.replacement.1 = new.replacement.2) :
    old.identityKnown = false ∧ old.symbolReplacement.1 = old.symbolReplacement.2 := by
  have live : new.replacement.2 ∈ ambient := identity ▸ (paired.newFormal ▸ paired.formalLive)
  have original := paired.newShape.resolve_right (fun outside => outside live)
  have literal : old.symbolReplacement.1 = old.symbolReplacement.2 :=
    paired.newFormal.symm.trans (identity.trans original)
  exact ⟨paired.becomesOriginal (fun same => active (paired.oldFormal.trans (literal.trans same.symm))) original, literal⟩

/-- A name absent from all formal entries keeps its original environment value. -/
theorem environment_absent (model : Interpretation Value) (env : Name → Value)
    (entries : List (Name × Name)) (name : Name)
    (absent : ∀ entry ∈ entries, entry.1 ≠ name) :
    renamedEnvironment model env entries name = env name := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rw [environment_cons]
      have different := absent entry (by simp)
      have tail := ih (fun row member => absent row (by simp [member]))
      by_cases identity : entry.1 = entry.2 <;> simp [identity, Ne.symm different, tail]

/-- A removed entry can expose only literal identities at the same formal. -/
theorem later_formal_identity (ambient : List Name) (old new : Resolved Formula) (rest : Scope)
    (paired : Pair ambient old new)
    (accepted : SourceSubstitutionPrecedence.ambiguousIdentityPrecedence (old :: rest) = false)
    (active : old.replacement.1 ≠ old.replacement.2)
    (identity : new.replacement.1 = new.replacement.2) :
    ∀ later ∈ rest, later.symbolReplacement.1 ≠ old.replacement.1 ∨
      later.symbolReplacement.2 = later.symbolReplacement.1 := by
  have changed := identity_changed paired active identity
  have pairs := (SourceSubstitutionPrecedence.precedence_false_iff (old :: rest)).mp accepted
  have first := (List.pairwise_cons.mp pairs).1
  intro later member
  have alternatives := first later member
  rcases alternatives with known | nonidentity | distinct
  · simp [changed.1] at known
  · exact False.elim (nonidentity changed.2)
  · simpa [paired.oldFormal] using distinct

/-- Paired resolution preserves formal names and their order. -/
theorem paired_formals (paired : Language.All₂ (Pair ambient) old new) :
    new.map (fun entry => entry.replacement.1) = old.map (fun entry => entry.symbolReplacement.1) := by
  induction paired with
  | nil => rfl
  | cons head tail ih => simp [head.newFormal, ih]

/-- Ordered paired lists provide a corresponding right member for every left member. -/
theorem member_left {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (paired : Language.All₂ relation left right) (entry : α) (member : entry ∈ left) :
    ∃ other ∈ right, relation entry other := by
  induction paired with
  | nil => simp at member
  | @cons a b as bs head tail ih =>
      rcases List.mem_cons.mp member with rfl | remaining
      · exact ⟨b, by simp, head⟩
      · obtain ⟨other, present, related⟩ := ih remaining
        exact ⟨other, by simp [present], related⟩

/-- Ordered paired lists provide a corresponding left member for every right member. -/
theorem member_right {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (paired : Language.All₂ relation left right) (entry : β) (member : entry ∈ right) :
    ∃ other ∈ left, relation other entry := by
  induction paired with
  | nil => simp at member
  | @cons a b as bs head tail ih =>
      rcases List.mem_cons.mp member with rfl | remaining
      · exact ⟨a, by simp, head⟩
      · obtain ⟨other, present, related⟩ := ih remaining
        exact ⟨other, by simp [present], related⟩

/-- The allocator retains an original name for all actuals with that name or for none. -/
def Coherent (scope : Scope) : Prop :=
  ∀ first ∈ scope, ∀ second ∈ scope,
    first.replacement.2 = first.symbolReplacement.2 →
    first.symbolReplacement.2 = second.symbolReplacement.2 →
    second.replacement.2 = second.symbolReplacement.2

/-- Restricting a scope retains the allocation invariant. -/
theorem coherent_subset (coherent : Coherent scope) (subset : smaller ⊆ scope) : Coherent smaller := by
  intro first fm second sm original same
  exact coherent first (subset fm) second (subset sm) original same

/-- Entries at the queried formal are inert when all their replacements are identities. -/
theorem environment_neutral (model : Interpretation Value) (env : Name → Value)
    (entries : List (Name × Name)) (name : Name)
    (neutral : ∀ entry ∈ entries, entry.1 = name → entry.2 = name) :
    renamedEnvironment model env entries name = env name := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rw [environment_cons]
      have tail := ih (fun row member => neutral row (by simp [member]))
      by_cases same : entry.1 = name
      · have identity := same.trans (neutral entry (by simp) same).symm
        simp [identity, tail]
      · simp [Ne.symm same, tail]

/-- One accepted simultaneous scope preserves every ambient value under related actual values. -/
theorem scope_environment (model : Interpretation Value) (ambient : List Name)
    (first second : Name → Value) (old new : Scope)
    (paired : Language.All₂ (Pair ambient) old new)
    (coherent : Coherent new)
    (accepted : SourceSubstitutionPrecedence.ambiguousIdentityPrecedence old = false)
    (base : FormulaSemantics.Agree ambient first second)
    (actuals : Language.All₂ (fun a b => first a.replacement.2 = second b.replacement.2) old new)
    (name : Name) (live : name ∈ ambient) :
    renamedEnvironment model first (old.map Resolved.replacement) name =
      renamedEnvironment model second (new.map Resolved.replacement) name := by
  induction paired with
  | nil => exact base name live
  | @cons old new oldRest newRest head tail ih =>
      cases actuals with
      | cons values restValues =>
          have safeRest : SourceSubstitutionPrecedence.ambiguousIdentityPrecedence oldRest = false := by
            simpa only [SourceSubstitutionPrecedence.ambiguousIdentityPrecedence, Bool.or_eq_false_iff] using
              (show _ ∧ _ from Bool.or_eq_false_iff.mp accepted).2
          have tailCoherent := coherent_subset coherent (fun _ member => List.mem_cons_of_mem _ member)
          have tailEqual := ih tailCoherent safeRest restValues
          change renamedEnvironment model first
            ((old.replacement.1, old.replacement.2) :: oldRest.map Resolved.replacement) name =
            renamedEnvironment model second
            ((new.replacement.1, new.replacement.2) :: newRest.map Resolved.replacement) name
          rw [environment_cons, environment_cons]
          by_cases oldIdentity : old.replacement.1 = old.replacement.2
          · have newIdentity := identity_forward head oldIdentity
            simp only [oldIdentity, newIdentity, ↓reduceIte]
            exact tailEqual
          · by_cases newIdentity : new.replacement.1 = new.replacement.2
            · have laterIdentity := later_formal_identity ambient old new oldRest head accepted oldIdentity newIdentity
              have newNeutral : ∀ entry ∈ newRest.map Resolved.replacement,
                  entry.1 = old.replacement.1 → entry.2 = old.replacement.1 := by
                intro entry member same
                obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
                obtain ⟨source, present, pair⟩ := member_right tail row rowMember
                have formal : source.symbolReplacement.1 = old.replacement.1 := pair.newFormal.symm.trans same
                have literal := (laterIdentity source present).resolve_left (fun different => different formal)
                have original : new.replacement.2 = new.symbolReplacement.2 := by
                  rw [head.symbols, ← newIdentity, head.newFormal, (identity_changed head oldIdentity newIdentity).2]
                have sameName : new.symbolReplacement.2 = row.symbolReplacement.2 := by
                  rw [head.symbols, pair.symbols, literal, formal, head.oldFormal,
                    (identity_changed head oldIdentity newIdentity).2]
                have rowOriginal := coherent new (by simp) row (by simp [rowMember]) original sameName
                rw [rowOriginal, pair.symbols, literal, formal]
              simp only [oldIdentity, newIdentity, ↓reduceIte]
              by_cases matching : name = old.replacement.1
              · subst name
                rw [ite_eq_left rfl, environment_neutral model second _ _ newNeutral]
                simpa [← newIdentity, head.oldFormal, head.newFormal] using values
              · simp only [matching, ↓reduceIte]
                exact tailEqual
            · have formals : new.replacement.1 = old.replacement.1 := head.newFormal.trans head.oldFormal.symm
              have newActive : old.replacement.1 ≠ new.replacement.2 := fun equal => newIdentity (formals.trans equal)
              simp only [oldIdentity, formals, newActive, ↓reduceIte]
              by_cases matching : name = old.replacement.1
              · simp only [matching, ↓reduceIte]
                exact values
              · simp only [matching, ↓reduceIte]
                exact tailEqual

/-- Each nested source scope passes both checks against its enclosing scopes. -/
def Accepted : List Scope → Prop
  | [] => True
  | scope :: outer =>
      SourceSubstitutionPrecedence.ambiguousIdentityPrecedence scope = false ∧
      scope.any (SourceEnclosingRenames.renamedByEnclosing outer) = false ∧ Accepted outer

/-- A name absent from the complete scope stack remains ambient. -/
theorem scopes_absent (model : Interpretation Value) (env : Name → Value) (scopes : List Scope)
    (name : Name) (absent : ∀ scope ∈ scopes, ∀ entry ∈ scope, entry.replacement.1 ≠ name) :
    scopeEnvironment model env scopes name = env name := by
  induction scopes with
  | nil => rfl
  | cons scope outer ih =>
      simp only [scopeEnvironment, List.foldr_cons]
      rw [environment_absent]
      · exact ih (fun entries member => absent entries (by simp [member]))
      · intro pair member
        obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
        exact absent scope (by simp) entry present

/-- Two ordered relations combine at each corresponding list position. -/
theorem combine_relations (paired : Language.All₂ first left right) (related : Language.All₂ second left right) :
    Language.All₂ (fun a b => first a b ∧ second a b) left right := by
  induction paired with
  | nil => exact .nil
  | cons head tail ih => cases related with | cons other rest => exact .cons ⟨head, other⟩ (ih rest)

/-- An ordered relation can use membership in the complete lists at each position. -/
theorem map_relation {α β : Type} {first second : α → β → Prop} {left : List α} {right : List β}
    (paired : Language.All₂ first left right)
    (transform : ∀ a ∈ left, ∀ b ∈ right, first a b → second a b) : Language.All₂ second left right := by
  induction paired with
  | nil => exact .nil
  | @cons a b as bs head tail ih =>
      exact .cons (transform a (by simp) b (by simp) head)
        (ih (fun x hx y hy => transform x (by simp [hx]) y (by simp [hy])))

/-- Fresh actual values survive outer scopes; an actual that becomes ambient is protected by the source test. -/
theorem actual_after_outer (model : Interpretation Value) (ambient : List Name)
    (first second : Name → Value) (outer other : List Scope)
    (paired : Language.All₂ (Language.All₂ (Pair ambient)) outer other)
    (ambientValues : FormulaSemantics.Agree ambient (scopeEnvironment model first outer) (scopeEnvironment model second other))
    (old new : Resolved Formula) (row : Pair ambient old new)
    (values : first old.replacement.2 = second new.replacement.2)
    (accepted : SourceEnclosingRenames.renamedByEnclosing outer old = false) :
    scopeEnvironment model first outer old.replacement.2 = scopeEnvironment model second other new.replacement.2 := by
  by_cases original : old.replacement.2 = old.symbolReplacement.2
  · rw [original, row.retained original]
    exact ambientValues _ row.actualLive
  · have sourceFresh := row.oldShape.resolve_left original
    have sourceUnchanged : scopeEnvironment model first outer old.replacement.2 = first old.replacement.2 := by
      apply scopes_absent
      intro scope member entry present equal
      obtain ⟨otherScope, _, scopesPaired⟩ := member_left paired scope member
      obtain ⟨otherEntry, _, entryPaired⟩ := member_left scopesPaired entry present
      exact sourceFresh (equal ▸ (entryPaired.oldFormal ▸ entryPaired.formalLive))
    rw [sourceUnchanged]
    have targetUnchanged : scopeEnvironment model second other new.replacement.2 = second new.replacement.2 := by
      apply scopes_absent
      intro scope member entry present equal
      obtain ⟨oldScope, oldMember, scopesPaired⟩ := member_right paired scope member
      obtain ⟨oldEntry, oldPresent, entryPaired⟩ := member_right scopesPaired entry present
      rcases row.newShape with becameOriginal | targetFresh
      · have unknown := row.becomesOriginal original becameOriginal
        have avoided : old.symbolReplacement.2 ∉ SourceEnclosingRenames.enclosingFormals outer := by
          simpa [SourceEnclosingRenames.renamedByEnclosing, unknown] using accepted
        apply avoided
        apply List.mem_flatMap.mpr
        refine ⟨oldScope, oldMember, ?_⟩
        apply List.mem_map.mpr
        exact ⟨oldEntry, oldPresent, entryPaired.newFormal.symm.trans (equal.trans becameOriginal)⟩
      · exact targetFresh (equal ▸ (entryPaired.newFormal ▸ entryPaired.formalLive))
    rw [targetUnchanged]
    exact values

/-- Every accepted nested scope preserves ambient meanings under a possibly non-injective identity quotient. -/
theorem scopes_environment (model : Interpretation Value) (ambient : List Name)
    (first second : Name → Value) (old new : List Scope)
    (paired : Language.All₂ (Language.All₂ (Pair ambient)) old new)
    (coherent : ∀ scope ∈ new, Coherent scope)
    (accepted : Accepted old) (base : FormulaSemantics.Agree ambient first second)
    (actuals : Language.All₂ (Language.All₂ (fun a b => first a.replacement.2 = second b.replacement.2)) old new) :
    FormulaSemantics.Agree ambient (scopeEnvironment model first old) (scopeEnvironment model second new) := by
  induction paired with
  | nil => exact base
  | @cons old new outer other head tail ih =>
      cases actuals with
      | cons values restValues =>
          have outerValues := ih (fun scope member => coherent scope (by simp [member])) accepted.2.2 restValues
          have rowValues : Language.All₂ (fun a b =>
              scopeEnvironment model first outer a.replacement.2 = scopeEnvironment model second other b.replacement.2) old new := by
            have together := combine_relations head values
            apply map_relation together
            intro a member b otherMember pair
            apply actual_after_outer model ambient first second outer other tail outerValues a b pair.1 pair.2
            have no := (List.any_eq_false.mp accepted.2.1) a member
            simpa using no
          intro name member
          simp only [scopeEnvironment, List.foldr_cons]
          exact scope_environment model ambient _ _ old new head (coherent _ (by simp)) accepted.1 outerValues rowValues name member

/-- Source formula semantics carries the derived forward scope relation through every constructor. -/
theorem scoped_formula (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (ambient : List Name) (first second : Name → Value) (old new : List Scope)
    (paired : Language.All₂ (Language.All₂ (Pair ambient)) old new)
    (coherent : ∀ scope ∈ new, Coherent scope)
    (accepted : Accepted old) (base : FormulaSemantics.Agree ambient first second)
    (actuals : Language.All₂ (Language.All₂ (fun a b => first a.replacement.2 = second b.replacement.2)) old new)
    (formula : Formula) (names : ∀ name ∈ formulaNames formula, name ∈ ambient) :
    Holds model first (SourceGuards.applySubstitutions operations old formula) ↔
      Holds model second (SourceGuards.applySubstitutions operations new formula) := by
  rw [scopes_semantics model nullary, scopes_semantics model nullary]
  apply FormulaSemantics.formula_ext
  intro name member
  exact scopes_environment model ambient first second old new paired coherent accepted base actuals name (names name member)

end MicroCFTA.SourceQuotientEnvironment
