import MicroCFTA.FormulaSubstitution

/-!
# Fresh binder transport

The lemmas derive the properties of the actual fresh-name preparation. They
connect simultaneous substitution to sorted binder semantics.
-/

namespace MicroCFTA.FormulaBinders

open FullSyntax FormulaSubstitution

/-- The names mentioned by replacements that remain active below these binders. -/
def captured (active : List (Name × Term)) (bound : List (Name × ValueSort)) : List Name :=
  (without bound active).flatMap fun entry => termNames entry.2

/-- The source's forbidden names for this binder block. -/
def avoided (active : List (Name × Term)) (bound : List (Name × ValueSort)) (body : List Name) : List Name :=
  captured active bound ++ body ++ bound.map Prod.fst ++ (without bound active).map Prod.fst

/-- The finite old-name to fresh-name table constructed by the source. -/
def renamings (active : List (Name × Term)) (bound : List (Name × ValueSort)) (body : List Name) : List (Name × Name) :=
  let names := (uniqueNames (bound.map Prod.fst)).filter (captured active bound).contains
  names.zip (freshNames (avoided active bound body) names.length)

/-- The source's prepared active substitution. -/
def nested (active : List (Name × Term)) (bound : List (Name × ValueSort)) (body : List Name) : List (Name × Term) :=
  (renamings active bound body).map (fun (old, fresh) => (old, Term.var fresh)) ++ without bound active

theorem prepare_eq (active : List (Name × Term)) (bound : List (Name × ValueSort)) (body : List Name) :
    prepare active bound body =
      (bound.map (fun (name, sort) => (renameName (renamings active bound body) name, sort)),
        nested active bound body) := rfl

/-- A captured binder name occurs in the renaming table, and no other name does. -/
theorem renamings_domain (active : List (Name × Term)) (bound : List (Name × ValueSort))
    (body : List Name) (name : Name) :
    name ∈ (renamings active bound body).map Prod.fst ↔
      name ∈ bound.map Prod.fst ∧ name ∈ captured active bound := by
  unfold renamings
  rw [List.map_fst_zip (by simp [freshNames_length])]
  simp [uniqueNames_mem]

/-- Every replacement target avoids replacement free names, body free names, binder names, and active keys. -/
theorem renamings_avoid (active : List (Name × Term)) (bound : List (Name × ValueSort))
    (body : List Name) (old fresh : Name) (member : (old, fresh) ∈ renamings active bound body) :
    fresh ∉ avoided active bound body := by
  exact freshNames_avoids _ _ fresh (List.of_mem_zip member).2

/-- Each fresh target appears only once in the renaming table. -/
theorem renamings_unique_targets (active : List (Name × Term)) (bound : List (Name × ValueSort))
    (body : List Name) : ((renamings active bound body).map Prod.snd).Nodup := by
  unfold renamings
  rw [List.map_snd_zip (by simp [freshNames_length])]
  exact freshNames_nodup _ _

/-- A name outside a renaming table's domain retains its name. -/
theorem rename_absent (renamed : List (Name × Name)) (name : Name)
    (absent : name ∉ renamed.map Prod.fst) : renameName renamed name = name := by
  induction renamed with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨old, fresh⟩
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      simp [renameName, absent.1, ih absent.2]

/-- A name inside a renaming table maps to one of its entries. -/
theorem rename_member (renamed : List (Name × Name)) (name : Name)
    (present : name ∈ renamed.map Prod.fst) : (name, renameName renamed name) ∈ renamed := by
  induction renamed with
  | nil => simp at present
  | cons entry rest ih =>
      rcases entry with ⟨old, fresh⟩
      by_cases same : name = old
      · subst name; simp [renameName]
      · simp [renameName, same]
        exact ih (by simpa [same] using present)

/-- A renaming either preserves a name or selects one table entry. -/
theorem rename_cases (renamed : List (Name × Name)) (name : Name) :
    renameName renamed name = name ∨ (name, renameName renamed name) ∈ renamed := by
  by_cases member : name ∈ renamed.map Prod.fst
  · exact Or.inr (rename_member renamed name member)
  · exact Or.inl (rename_absent renamed name member)

/-- Distinct old names cannot share a unique target. -/
theorem target_injective (renamed : List (Name × Name)) (unique : (renamed.map Prod.snd).Nodup)
    (left right target : Name) (hl : (left, target) ∈ renamed) (hr : (right, target) ∈ renamed) : left = right := by
  induction renamed with
  | nil => simp at hl
  | cons entry rest ih =>
      rcases entry with ⟨old, fresh⟩
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp hl with equal | hleftTail
      · cases equal
        rcases List.mem_cons.mp hr with equal | hrightTail
        · cases equal; rfl
        · exact False.elim (unique.1 (List.mem_map.mpr ⟨(right, target), hrightTail, rfl⟩))
      · rcases List.mem_cons.mp hr with equal | hrightTail
        · cases equal
          exact False.elim (unique.1 (List.mem_map.mpr ⟨(left, target), hleftTail, rfl⟩))
        · exact ih unique.2 hleftTail hrightTail

/-- Fresh renaming is injective on the original body and binder names. -/
theorem renamings_injective (active : List (Name × Term)) (bound : List (Name × ValueSort))
    (body : List Name) (left right : Name)
    (hl : left ∈ body ++ bound.map Prod.fst) (hr : right ∈ body ++ bound.map Prod.fst)
    (equal : renameName (renamings active bound body) left = renameName (renamings active bound body) right) :
    left = right := by
  rcases rename_cases (renamings active bound body) left with leftFixed | leftMember
  · rcases rename_cases (renamings active bound body) right with rightFixed | rightMember
    · simpa [leftFixed, rightFixed] using equal
    · have absent := renamings_avoid active bound body right _ rightMember
      have target : renameName (renamings active bound body) right = left := equal.symm.trans leftFixed
      rw [target] at absent
      exact False.elim (absent (by simp [avoided, List.mem_append] at *; grind))
  · rcases rename_cases (renamings active bound body) right with rightFixed | rightMember
    · have absent := renamings_avoid active bound body left _ leftMember
      have target : renameName (renamings active bound body) left = right := equal.trans rightFixed
      rw [target] at absent
      exact False.elim (absent (by simp [avoided, List.mem_append] at *; grind))
    · rw [equal] at leftMember
      exact target_injective _ (renamings_unique_targets active bound body) left right _ leftMember rightMember

/-- Every prepared binder name avoids the free names of the retained replacement terms. -/
theorem renamed_avoids_captured (active : List (Name × Term)) (bound : List (Name × ValueSort))
    (body : List Name) (name : Name) (member : name ∈ bound.map Prod.fst) :
    renameName (renamings active bound body) name ∉ captured active bound := by
  intro capturedName
  rcases rename_cases (renamings active bound body) name with fixed | renamed
  · rw [fixed] at capturedName
    have present := (renamings_domain active bound body name).mpr ⟨member, capturedName⟩
    have inTable := rename_member _ name present
    have absent := renamings_avoid active bound body name _ inTable
    exact absent (by simp [avoided, capturedName, fixed])
  · have absent := renamings_avoid active bound body name _ renamed
    exact absent (by simp [avoided, capturedName])

/-- The term table for a name renaming agrees with the name lookup. -/
theorem lookup_renaming (renamed : List (Name × Name)) (name : Name) :
    lookup name (renamed.map fun (old, fresh) => (old, Term.var fresh)) =
      if name ∈ renamed.map Prod.fst then some (.var (renameName renamed name)) else none := by
  induction renamed with
  | nil => simp [lookup]
  | cons entry rest ih =>
      rcases entry with ⟨old, fresh⟩
      by_cases same : name = old <;> simp [lookup, renameName, same, ih]
      by_cases member : name ∈ rest.map Prod.fst <;> simp [member, same]

/-- Lookup in an appended simultaneous substitution prefers the first table. -/
theorem lookup_append (left right : List (Name × Term)) (name : Name) :
    lookup name (left ++ right) = (lookup name left).or (lookup name right) := by
  induction left with
  | nil => simp [lookup]
  | cons entry rest ih =>
      rcases entry with ⟨old, value⟩
      by_cases same : name = old <;> simp [lookup, same, ih]

/-- Prepared substitution assigns a bound name through its renamed binder. -/
theorem nested_bound (model : Interpretation Value) (env : Name → Value) (active : List (Name × Term))
    (bound : List (Name × ValueSort)) (body : List Name) (name : Name)
    (member : name ∈ bound.map Prod.fst) :
    assignment model env (nested active bound body) name = env (renameName (renamings active bound body) name) := by
  simp only [assignment, nested, lookup_append, lookup_renaming, lookup_without]
  by_cases renamed : name ∈ (renamings active bound body).map Prod.fst
  · simp [renamed, evaluateTerm]
  · simp [renamed, member, rename_absent _ _ renamed]

/-- Prepared substitution agrees with the original active substitution on unbound names. -/
theorem nested_free (model : Interpretation Value) (env : Name → Value) (active : List (Name × Term))
    (bound : List (Name × ValueSort)) (body : List Name) (name : Name)
    (member : name ∉ bound.map Prod.fst) :
    assignment model env (nested active bound body) name = assignment model env (without bound active) name := by
  have absent : name ∉ (renamings active bound body).map Prod.fst := by simp [renamings_domain, member]
  simp [assignment, nested, lookup_append, lookup_renaming, absent]

/-- Assigning a fresh binder has exactly the effect of assigning its original name in the substituted body. -/
theorem nested_update (model : Interpretation Value) (env : Name → Value) (active : List (Name × Term))
    (bound : List (Name × ValueSort)) (body : List Name) (name : Name) (value : Value)
    (member : name ∈ bound.map Prod.fst) :
    FormulaSemantics.Agree body
      (assignment model (update env (renameName (renamings active bound body) name) value) (nested active bound body))
      (update (assignment model env (nested active bound body)) name value) := by
  intro other present
  by_cases boundOther : other ∈ bound.map Prod.fst
  · rw [nested_bound model _ active bound body other boundOther]
    by_cases same : other = name
    · subst other
      simp [update]
    · have different : renameName (renamings active bound body) other ≠
          renameName (renamings active bound body) name := by
        intro equal
        exact same (renamings_injective active bound body other name
          (by simp [present]) (by simp [member]) equal)
      simp [update, same, different, nested_bound model env active bound body other boundOther]
  · have different : other ≠ name := by intro equal; subst other; exact boundOther member
    have absentRename : other ∉ (renamings active bound body).map Prod.fst := by
      simp [renamings_domain, boundOther]
    have freshDifferent : other ≠ renameName (renamings active bound body) name := by
      intro equal
      apply different
      exact renamings_injective active bound body other name (by simp [present]) (by simp [member])
        ((rename_absent _ _ absentRename).trans equal)
    simp only [update, different, ↓reduceIte]
    rw [nested_free model _ active bound body other boundOther, nested_free model env active bound body other boundOther]
    cases found : lookup other (without bound active) with
    | none => simp [assignment, found, update, freshDifferent]
    | some replacement =>
        simp only [assignment, found]
        apply FormulaSemantics.term_ext
        intro free inReplacement
        have avoids := renamed_avoids_captured active bound body name member
        have unequal : free ≠ renameName (renamings active bound body) name := by
          intro same
          apply avoids
          exact List.mem_flatMap.mpr ⟨(other, replacement), lookup_member _ _ _ found, same ▸ inReplacement⟩
        simp [update, unequal]

/-- Universal traversal transports a substitution through a finite renamed binder block. -/
theorem allBound_rename_map (model : Interpretation Value) (bound : List (Name × ValueSort))
    (rename : Name → Name) (names : List Name) (env : Name → Value)
    (transform : (Name → Value) → Name → Value) (body : (Name → Value) → Prop)
    (congruent : ∀ left right, FormulaSemantics.Agree names left right → (body left ↔ body right))
    (commutes : ∀ name ∈ bound.map Prod.fst, ∀ assigned value,
      FormulaSemantics.Agree names (transform (update assigned (rename name) value))
        (update (transform assigned) name value)) :
    allBound model (bound.map fun (name, sort) => (rename name, sort)) env
        (fun assigned => body (transform assigned)) ↔
      allBound model bound (transform env) body := by
  induction bound generalizing env with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨name, sort⟩
      simp only [List.map_cons, allBound]
      apply forall_congr'
      intro value
      apply imp_congr_right
      intro _
      apply Iff.trans (ih (update env (rename name) value) (fun n hn => commutes n (by simp [hn])))
      exact FormulaSemantics.allBound_congr model rest names _ _ body body congruent
        (fun n hn _ => commutes name (by simp) env value n hn)

/-- Existential traversal transports a substitution through the same renamed binder block. -/
theorem someBound_rename_map (model : Interpretation Value) (bound : List (Name × ValueSort))
    (rename : Name → Name) (names : List Name) (env : Name → Value)
    (transform : (Name → Value) → Name → Value) (body : (Name → Value) → Prop)
    (congruent : ∀ left right, FormulaSemantics.Agree names left right → (body left ↔ body right))
    (commutes : ∀ name ∈ bound.map Prod.fst, ∀ assigned value,
      FormulaSemantics.Agree names (transform (update assigned (rename name) value))
        (update (transform assigned) name value)) :
    someBound model (bound.map fun (name, sort) => (rename name, sort)) env
        (fun assigned => body (transform assigned)) ↔
      someBound model bound (transform env) body := by
  induction bound generalizing env with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨name, sort⟩
      simp only [List.map_cons, someBound]
      apply exists_congr
      intro value
      apply and_congr_right
      intro _
      apply Iff.trans (ih (update env (rename name) value) (fun n hn => commutes n (by simp [hn])))
      exact FormulaSemantics.someBound_congr model rest names _ _ body body congruent
        (fun n hn _ => commutes name (by simp) env value n hn)

/-- Actual source binder preparation preserves universal semantics once the recursive body is substituted. -/
theorem prepared_all (model : Interpretation Value) (env : Name → Value) (active : List (Name × Term))
    (bound : List (Name × ValueSort)) (p result : Formula)
    (body : ∀ assigned, Holds model assigned result ↔
      Holds model (assignment model assigned (prepare active bound (formulaNames p)).2) p) :
    Holds model env (.forall (prepare active bound (formulaNames p)).1 result) ↔
      Holds model (assignment model env active) (.forall bound p) := by
  simp only [prepare_eq] at body
  simp only [prepare_eq, Holds]
  have pointwise : (fun assigned => Holds model assigned result) =
      (fun assigned => Holds model (assignment model assigned (nested active bound (formulaNames p))) p) :=
    funext (fun assigned => propext (body assigned))
  rw [pointwise]
  apply Iff.trans (allBound_rename_map model bound (renameName (renamings active bound (formulaNames p)))
    (formulaNames p) env (fun assigned => assignment model assigned (nested active bound (formulaNames p)))
    (fun assigned => Holds model assigned p)
    (fun a b h => FormulaSemantics.formula_ext model p a b h)
    (fun name member assigned value => nested_update model assigned active bound (formulaNames p) name value member))
  exact FormulaSemantics.allBound_congr model bound (formulaNames p) _ _ _ _
    (fun a b h => FormulaSemantics.formula_ext model p a b h)
    (fun name _ absent => (nested_free model env active bound (formulaNames p) name absent).trans
      (assignment_without model env active bound name absent))

/-- Actual source binder preparation preserves existential semantics once the recursive body is substituted. -/
theorem prepared_exists (model : Interpretation Value) (env : Name → Value) (active : List (Name × Term))
    (bound : List (Name × ValueSort)) (p result : Formula)
    (body : ∀ assigned, Holds model assigned result ↔
      Holds model (assignment model assigned (prepare active bound (formulaNames p)).2) p) :
    Holds model env (.exists (prepare active bound (formulaNames p)).1 result) ↔
      Holds model (assignment model env active) (.exists bound p) := by
  simp only [prepare_eq] at body
  simp only [prepare_eq, Holds]
  have pointwise : (fun assigned => Holds model assigned result) =
      (fun assigned => Holds model (assignment model assigned (nested active bound (formulaNames p))) p) :=
    funext (fun assigned => propext (body assigned))
  rw [pointwise]
  apply Iff.trans (someBound_rename_map model bound (renameName (renamings active bound (formulaNames p)))
    (formulaNames p) env (fun assigned => assignment model assigned (nested active bound (formulaNames p)))
    (fun assigned => Holds model assigned p)
    (fun a b h => FormulaSemantics.formula_ext model p a b h)
    (fun name member assigned value => nested_update model assigned active bound (formulaNames p) name value member))
  exact FormulaSemantics.someBound_congr model bound (formulaNames p) _ _ _ _
    (fun a b h => FormulaSemantics.formula_ext model p a b h)
    (fun name _ absent => (nested_free model env active bound (formulaNames p) name absent).trans
      (assignment_without model env active bound name absent))

end MicroCFTA.FormulaBinders
