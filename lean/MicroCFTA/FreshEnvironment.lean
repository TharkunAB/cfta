import MicroCFTA.SourceAliasTransport

/-!
# Construct environments for source fresh-name changes

The source fresh streams provide injective finite name tables. Their reverse
tables construct the environment lifts required by entailment transport.
Identity replacement filtering is included in this proof.
-/
namespace MicroCFTA.FreshEnvironment
open FullSyntax FormulaSubstitution SourceFormula SourceAliasTransport

/-- The actual checked API removes literal identity name pairs. -/
def clean (renamed : List (Name × Name)) : List (Name × Name) :=
  renamed.filter (fun entry => !identityReplacement (entry.1, .var entry.2))

theorem clean_replacements (renamed : List (Name × Name)) :
    (replacements renamed).filter (fun entry => !identityReplacement entry) = replacements (clean renamed) := by
  simp [replacements, clean, List.filter_map, Function.comp_def]

/-- Filtering entries cannot introduce a name in the table domain. -/
theorem clean_absent (renamed : List (Name × Name)) (name : Name)
    (absent : name ∉ renamed.map Prod.fst) : name ∉ (clean renamed).map Prod.fst := by
  rintro member
  obtain ⟨entry, present, equal⟩ := List.mem_map.mp member
  exact absent (List.mem_map.mpr ⟨entry, (List.mem_filter.mp present).1, equal⟩)

/-- Identity filtering preserves an injective-domain name table's total lookup. -/
theorem clean_rename (renamed : List (Name × Name)) (unique : (renamed.map Prod.fst).Nodup) (name : Name) :
    renameName (clean renamed) name = renameName renamed name := by
  induction renamed with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨old, target⟩
      simp only [List.map_cons, List.nodup_cons] at unique
      by_cases identity : old = target
      · subst target
        by_cases same : name = old
        · subst name
          simp only [clean, List.filter_cons, identityReplacement, beq_self_eq_true, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte, renameName]
          simpa [clean, identityReplacement] using FormulaBinders.rename_absent (clean rest) old (clean_absent rest old unique.1)
        · simpa [clean, identityReplacement, renameName, same] using ih unique.2
      · by_cases same : name = old
        · simp [clean, identityReplacement, renameName, identity, same]
        · simpa [clean, identityReplacement, renameName, identity, same] using ih unique.2

/-- Raw name substitution reads the environment at the selected renamed name. -/
theorem assignment_names (model : Interpretation Value) (env : Name → Value)
    (renamed : List (Name × Name)) (name : Name) :
    assignment model env (replacements renamed) name = env (renameName renamed name) := by
  unfold assignment
  have lookupNames := FormulaBinders.lookup_renaming renamed name
  change FullSyntax.lookup name (replacements renamed) = _ at lookupNames
  rw [lookupNames]
  by_cases present : name ∈ renamed.map Prod.fst
  · simp [present, evaluateTerm]
  · simp [present, FormulaBinders.rename_absent renamed name present]

/-- The repaired checked API has the direct lookup meaning for an injective-domain name table. -/
theorem environment_names (model : Interpretation Value) (env : Name → Value)
    (renamed : List (Name × Name)) (unique : (renamed.map Prod.fst).Nodup) (name : Name) :
    renamedEnvironment model env renamed name = env (renameName renamed name) := by
  unfold renamedEnvironment
  rw [clean_replacements, assignment_names, clean_rename renamed unique name]

/-- A table with unique keys selects the value of every member pair. -/
theorem rename_of_member (renamed : List (Name × Name)) (unique : (renamed.map Prod.fst).Nodup)
    (old target : Name) (member : (old, target) ∈ renamed) : renameName renamed old = target := by
  have selected := FormulaBinders.rename_member renamed old (List.mem_map.mpr ⟨(old, target), member, rfl⟩)
  apply FormulaBinders.target_injective (renamed.map Prod.swap) (by simpa [List.map_map, Function.comp_def] using unique) _ _ old
  · exact List.mem_map.mpr ⟨(old, renameName renamed old), selected, rfl⟩
  · exact List.mem_map.mpr ⟨(old, target), member, rfl⟩

/-- Read renamed values through the reverse finite name table. -/
def liftEnvironment (renamed : List (Name × Name)) (original : Name → Value) : Name → Value :=
  fun name => original (renameName (renamed.map Prod.swap) name)

/-- The explicit reverse table lifts every relevant name when new targets avoid unmapped relevant names. -/
theorem lift_agree (model : Interpretation Value) (renamed : List (Name × Name)) (live : List Name)
    (keys : (renamed.map Prod.fst).Nodup) (targets : (renamed.map Prod.snd).Nodup)
    (avoid : ∀ name ∈ live, name ∉ renamed.map Prod.fst → name ∉ renamed.map Prod.snd)
    (original : Name → Value) :
    FormulaSemantics.Agree live (renamedEnvironment model (liftEnvironment renamed original) renamed) original := by
  intro name member
  rw [environment_names model _ renamed keys name]
  unfold liftEnvironment
  by_cases present : name ∈ renamed.map Prod.fst
  · have selected := FormulaBinders.rename_member renamed name present
    have inverse := rename_of_member (renamed.map Prod.swap) (by simpa [List.map_map, Function.comp_def] using targets)
      (renameName renamed name) name (List.mem_map.mpr ⟨_, selected, rfl⟩)
    rw [inverse]
  · rw [FormulaBinders.rename_absent renamed name present,
      FormulaBinders.rename_absent (renamed.map Prod.swap) name (by simpa [List.map_map, Function.comp_def] using avoid name member present)]

/-- Pair corresponding positions of the two executed source fresh-name streams. -/
def freshRenaming (firstAvoid secondAvoid : List Name) (count : Nat) : List (Name × Name) :=
  (SourceGuards.freshNames firstAvoid count).zip (SourceGuards.freshNames secondAvoid count)

theorem fresh_keys (firstAvoid secondAvoid : List Name) (count : Nat) :
    (freshRenaming firstAvoid secondAvoid count).map Prod.fst = SourceGuards.freshNames firstAvoid count := by
  apply List.map_fst_zip
  simp [SourceActuals.fresh_length]

theorem fresh_targets (firstAvoid secondAvoid : List Name) (count : Nat) :
    (freshRenaming firstAvoid secondAvoid count).map Prod.snd = SourceGuards.freshNames secondAvoid count := by
  apply List.map_snd_zip
  simp [SourceActuals.fresh_length]

/-- The source streams construct the environment-lifting premise for unrestricted query domains. -/
theorem fresh_lifts (model : Interpretation Value) (firstAvoid secondAvoid ambient : List Name) (count : Nat)
    (ambientAvoided : ∀ name ∈ ambient, name ∈ secondAvoid) (antecedent consequent : Formula)
    (names : ∀ name ∈ formulaNames antecedent ++ formulaNames consequent,
      name ∈ ambient ++ SourceGuards.freshNames firstAvoid count) :
    Lifts model (fun _ => True) (fun _ => True) (freshRenaming firstAvoid secondAvoid count) antecedent consequent := by
  intro original _
  refine ⟨liftEnvironment (freshRenaming firstAvoid secondAvoid count) original, True.intro, ?_⟩
  apply lift_agree model _ _
  · rw [fresh_keys]
    exact SourceActuals.fresh_nodup _ _
  · rw [fresh_targets]
    exact SourceActuals.fresh_nodup _ _
  · intro name member outside
    rw [fresh_keys] at outside
    rw [fresh_targets]
    have ambientMember : name ∈ ambient := (List.mem_append.mp (names name member)).resolve_right outside
    exact fun fresh => SourceActuals.fresh_avoids secondAvoid count name fresh (ambientAvoided name ambientMember)

/-- The explicit table maps each executed old stream position to the corresponding new position. -/
theorem fresh_map_stream (firstAvoid secondAvoid : List Name) (count : Nat) :
    (SourceGuards.freshNames firstAvoid count).map (renameName (freshRenaming firstAvoid secondAvoid count)) =
      SourceGuards.freshNames secondAvoid count := by
  rw [← fresh_keys firstAvoid secondAvoid count, List.map_map]
  calc
    _ = (freshRenaming firstAvoid secondAvoid count).map Prod.snd := by
      apply List.map_congr_left
      intro entry member
      exact rename_of_member _ (by rw [fresh_keys]; exact SourceActuals.fresh_nodup _ _) entry.1 entry.2 member
    _ = _ := fresh_targets firstAvoid secondAvoid count

/-- Source fresh spelling changes preserve unrestricted mathematical entailment once query names are bounded. -/
theorem fresh_entails_iff (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (firstAvoid secondAvoid ambient : List Name) (count : Nat)
    (ambientAvoided : ∀ name ∈ ambient, name ∈ secondAvoid) (antecedent consequent : Formula)
    (names : ∀ name ∈ formulaNames antecedent ++ formulaNames consequent,
      name ∈ ambient ++ SourceGuards.freshNames firstAvoid count) :
    SourceEntailment.Entails model (fun _ => True)
      (substitute (freshRenaming firstAvoid secondAvoid count) antecedent)
      (substitute (freshRenaming firstAvoid secondAvoid count) consequent) ↔
    SourceEntailment.Entails model (fun _ => True) antecedent consequent :=
  SourceEntailment.rename_iff model nullary _ _ _ antecedent consequent (fun _ _ => True.intro)
    (fresh_lifts model firstAvoid secondAvoid ambient count ambientAvoided antecedent consequent names)

end MicroCFTA.FreshEnvironment
