import MicroCFTA.SourceScopeQueries

/-!+# Source fresh declarations retain their original sort domains

The declaration pair contains a fresh logical name and its original sort
name. Only the logical name changes between read-equivalent cells. The proof
includes nested scope collection and the source duplicate removal.
-/
namespace MicroCFTA.SourceSortedQueries
open FullSyntax FormulaSubstitution SourceFormula SourceScopeStack SourceScopeQueries

/-- The exact declarations passed to the source solver by Entails and Satisfies. -/
def declarations (scopes : List Scope) : List (Name × Name) :=
  (scopes.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups

/-- Each generated value has the domain of its original ambient name. -/
def Domain (sortDomain : Name → Value → Prop) (scopes : List Scope) (env : Name → Value) : Prop :=
  ∀ binding ∈ declarations scopes, sortDomain binding.2 (env binding.1)

theorem domain_iff (sortDomain : Name → Value → Prop) (scopes : List Scope) (env : Name → Value) :
    Domain sortDomain scopes env ↔
      ∀ scope ∈ scopes, ∀ entry ∈ scope, ∀ binding, entry.declaration = some binding → sortDomain binding.2 (env binding.1) := by
  simp only [Domain, declarations, List.mem_eraseDups, List.mem_filterMap, List.mem_flatten]
  constructor
  · intro all scope member entry present binding found
    exact all binding ⟨entry, ⟨scope, member, present⟩, found⟩
  · rintro all binding ⟨entry, ⟨scope, member, present⟩, found⟩
    exact all scope member entry present binding found

private theorem declaration_replacement (observed : SourceGuards.Observations Formula)
    (fresh : List (SourceGuards.Path × (Name × Name))) (unknown : List SourceGuards.Path)
    (entry : SourceGuards.Substitution) (resolved : SourceGuards.Resolved Formula)
    (found : SourceGuards.resolve operations observed fresh unknown entry = some resolved)
    (binding : Name × Name) (declared : resolved.declaration = some binding) : binding.1 = resolved.replacement.2 := by
  obtain ⟨actual, formal, atActual, atFormal⟩ := SourceActuals.resolve_exists operations observed fresh unknown entry resolved found
  simp only [SourceGuards.resolve, atActual, atFormal, Option.map] at found
  have same := Option.some.inj found
  subst resolved
  simp only at declared ⊢
  rw [declared]
  rfl

private theorem resolved_pair (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (entry : SourceGuards.Substitution)
    (positions : entry.actual ∈ SourceGuards.sensitive guard ∧ entry.formal ∈ SourceGuards.sensitive guard)
    (old new : SourceGuards.Resolved Formula)
    (oldFound : SourceGuards.resolve operations first
      (SourceGuards.substitutionValues operations first (SourceObservations.sameShape operations first []) guard).1
      (SourceGuards.substitutionValues operations first (SourceObservations.sameShape operations first []) guard).2 entry = some old)
    (newFound : SourceGuards.resolve operations second
      (SourceGuards.substitutionValues operations second (SourceObservations.sameShape operations second []) guard).1
      (SourceGuards.substitutionValues operations second (SourceObservations.sameShape operations second []) guard).2 entry = some new) :
    SourceResolvedTables.Aligned (SourceFreshTables.tableRenaming operations guard first second) old new := by
  have paired := SourceResolvedTables.resolve_aligned operations guard first second reads entry positions.1 positions.2
  simpa [oldFound, newFound, SourceResolvedTables.OptionRel] using paired

/-- Sort-domain membership of one actual source declaration is unchanged. -/
theorem entry_domain_related (sortDomain : Name → Value → Prop)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (entry : SourceGuards.Substitution)
    (positions : entry.actual ∈ SourceGuards.sensitive guard ∧ entry.formal ∈ SourceGuards.sensitive guard)
    (firstEnv secondEnv : Name → Value)
    (related : SourceScopeEnvironment.Related (SourceFreshTables.tableRenaming operations guard first second)
      (SourceSemanticNames.live operations first guard) firstEnv secondEnv)
    (old new : SourceGuards.Resolved Formula)
    (oldFound : SourceGuards.resolve operations first
      (SourceGuards.substitutionValues operations first (SourceObservations.sameShape operations first []) guard).1
      (SourceGuards.substitutionValues operations first (SourceObservations.sameShape operations first []) guard).2 entry = some old)
    (newFound : SourceGuards.resolve operations second
      (SourceGuards.substitutionValues operations second (SourceObservations.sameShape operations second []) guard).1
      (SourceGuards.substitutionValues operations second (SourceObservations.sameShape operations second []) guard).2 entry = some new) :
    (∀ binding, old.declaration = some binding → sortDomain binding.2 (firstEnv binding.1)) ↔
      ∀ binding, new.declaration = some binding → sortDomain binding.2 (secondEnv binding.1) := by
  have aligned := resolved_pair guard first second reads entry positions old new oldFound newFound
  rw [aligned.2.2.1]
  cases declared : old.declaration with
  | none => simp
  | some binding =>
      have live := SourceSemanticNames.resolve_live operations guard first second entry old positions.1 positions.2 oldFound
      have bound := declaration_replacement first _ _ entry old oldFound binding declared
      have agrees := related binding.1 (bound ▸ live.2.1)
      simp [agrees]

private theorem resolveMany_rel (first second : SourceGuards.Observations Formula)
    (firstFresh secondFresh : List (SourceGuards.Path × (Name × Name)))
    (firstUnknown secondUnknown : List SourceGuards.Path)
    (relation : SourceGuards.Resolved Formula → SourceGuards.Resolved Formula → Prop)
    (recipe : Recipe)
    (each : ∀ entry ∈ recipe, ∀ old new,
      SourceGuards.resolve operations first firstFresh firstUnknown entry = some old →
      SourceGuards.resolve operations second secondFresh secondUnknown entry = some new → relation old new)
    (scope other : Scope)
    (oldFound : SourceGuards.resolveMany operations first firstFresh firstUnknown recipe = some scope)
    (newFound : SourceGuards.resolveMany operations second secondFresh secondUnknown recipe = some other) :
    Language.All₂ relation scope other := by
  induction recipe generalizing scope other with
  | nil => simp [SourceGuards.resolveMany] at oldFound newFound; subst scope; subst other; exact .nil
  | cons entry rest ih =>
      cases a : SourceGuards.resolve operations first firstFresh firstUnknown entry <;>
        cases b : SourceGuards.resolve operations second secondFresh secondUnknown entry <;>
        cases c : SourceGuards.resolveMany operations first firstFresh firstUnknown rest <;>
        cases d : SourceGuards.resolveMany operations second secondFresh secondUnknown rest <;>
        simp [SourceGuards.resolveMany, a, b, c, d] at oldFound newFound
      subst scope; subst other
      exact .cons (each entry (by simp) _ _ a b)
        (ih (fun value member => each value (by simp [member])) _ _ c d)

private theorem all₂_forall {Left Right : Type} (left : List Left) (right : List Right)
    (first : Left → Prop) (second : Right → Prop)
    (paired : Language.All₂ (fun a b => first a ↔ second b) left right) :
    (∀ a ∈ left, first a) ↔ ∀ b ∈ right, second b := by
  induction paired with
  | nil => simp
  | cons head tail ih => simpa only [List.forall_mem_cons] using and_congr head ih

/-- The complete source collection and duplicate removal preserve every generated sort restriction. -/
theorem domain_related (sortDomain : Name → Value → Prop)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (firstEnv secondEnv : Name → Value)
    (related : SourceScopeEnvironment.Related (SourceFreshTables.tableRenaming operations guard first second)
      (SourceSemanticNames.live operations first guard) firstEnv secondEnv) :
    Domain sortDomain scopes firstEnv ↔ Domain sortDomain other secondEnv := by
  rw [domain_iff, domain_iff]
  apply all₂_forall
  induction resolved generalizing other with
  | nil => cases otherResolved; exact .nil
  | @cons recipe scope recipes scopes head tail ih =>
      cases otherResolved with
      | @cons _ otherScope _ otherRest otherHead otherTail =>
          refine .cons ?_ (ih _ otherTail)
          apply all₂_forall
          apply resolveMany_rel first second _ _ _ _ _ recipe _ scope otherScope head.1 otherHead.1
          intro entry member old new oldFound newFound
          exact entry_domain_related sortDomain guard first second reads entry (head.2 entry member)
            firstEnv secondEnv related old new oldFound newFound

/-- The complete nested query preserves entailment with every source fresh sort declaration. -/
theorem sorted_query_iff (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (antecedent consequent : Formula)
    (leftNames : ∀ name ∈ formulaNames antecedent, name ∈ SourceSemanticNames.ambient operations first guard)
    (rightNames : ∀ name ∈ formulaNames consequent, name ∈ SourceSemanticNames.ambient operations first guard) :
    SourceEntailment.Entails model (Domain sortDomain scopes)
      (SourceGuards.withActualAssumptions operations scopes (SourceGuards.applySubstitutions operations scopes antecedent))
      (SourceGuards.applySubstitutions operations scopes consequent) ↔
    SourceEntailment.Entails model (Domain sortDomain other)
      (SourceGuards.withActualAssumptions operations other (SourceGuards.applySubstitutions operations other antecedent))
      (SourceGuards.applySubstitutions operations other consequent) := by
  constructor
  · intro proved env allowed assumed
    have related := forward_related model guard first second env
    exact (formula_related model nullary guard first second reads recipes scopes other resolved otherResolved
      _ env related consequent rightNames).mp
      (proved _ ((domain_related sortDomain guard first second reads recipes scopes other resolved otherResolved _ env related).mpr allowed)
        ((antecedent_related model nullary laws guard first second reads recipes scopes other
          resolved otherResolved _ env related antecedent leftNames).mpr assumed))
  · intro proved env allowed assumed
    have unique := SourceFreshTables.renaming_unique operations guard first second
    have related := SourceScopeEnvironment.lift_related model _ _ unique.1 unique.2
      (SourceSemanticNames.live_avoid operations guard first second reads) env
    exact (formula_related model nullary guard first second reads recipes scopes other resolved otherResolved
      env _ related consequent rightNames).mpr
      (proved _ ((domain_related sortDomain guard first second reads recipes scopes other resolved otherResolved env _ related).mp allowed)
        ((antecedent_related model nullary laws guard first second reads recipes scopes other
          resolved otherResolved env _ related antecedent leftNames).mp assumed))

end MicroCFTA.SourceSortedQueries
