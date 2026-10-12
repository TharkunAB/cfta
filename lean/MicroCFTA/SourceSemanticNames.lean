import MicroCFTA.SourceScopeEnvironment

/-!
# Semantic ambient names of the complete source guard

Formula free names and symbol-sensitive constructor names have the same
meaning across a source signature. Names at refinement-only constructors are
excluded. Both allocation passes avoid every name in this semantic set.
-/
namespace MicroCFTA.SourceSemanticNames
open SourceGuards SourceObservations SourceReadAgreement SourceFreshTables SourceResolvedTables
open FormulaSubstitution FreshEnvironment

/-- Collect free formula names from the observed refinements at all guard paths. -/
def refinementNames (formulas : Formulas Formula) (observed : Observations Formula) (guard : Guard Formula) : List Name :=
  (orderedPaths (paths guard)).flatMap (fun target =>
    match observed target with | none => [] | some value => formulas.freeNames value.refinement)

/-- Only structurally read constructor names belong to the formula environment. -/
def symbolNames (observed : Observations Formula) (guard : Guard Formula) : List Name :=
  (orderedPaths (sensitive guard)).filterMap (fun target => (observed target).map Observed.name)

/-- The semantic ambient name set before source-generated actual and contract names. -/
def ambient (formulas : Formulas Formula) (observed : Observations Formula) (guard : Guard Formula) : List Name :=
  refinementNames formulas observed guard ++ (requirements guard).flatMap formulas.freeNames ++ symbolNames observed guard

/-- Every observed formula free name is forbidden to the actual allocator. -/
theorem free_used (formulas : Formulas Formula) (observed : Observations Formula) (guard : Guard Formula)
    (path : Path) (value : Observed Formula) (name : Name) (requested : path ∈ paths guard)
    (found : observed path = some value) (free : name ∈ formulas.freeNames value.refinement) :
    name ∈ usedNames formulas observed guard := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨path, by simpa [orderedPaths] using requested, ?_⟩
  simp [found, free]

/-- All semantic ambient names occur in the actual source avoid list. -/
theorem ambient_used (formulas : Formulas Formula) (observed : Observations Formula) (guard : Guard Formula)
    (name : Name) (member : name ∈ ambient formulas observed guard) : name ∈ usedNames formulas observed guard := by
  simp only [ambient, List.mem_append] at member
  rcases member with (refinement | requirement) | symbol
  · obtain ⟨target, requested, free⟩ := List.mem_flatMap.mp refinement
    cases found : observed target with
    | none => simp [found] at free
    | some value =>
        exact free_used formulas observed guard target value name
          (by simpa [orderedPaths] using requested) found (by simpa [found] using free)
  · exact List.mem_append_right _ requirement
  · obtain ⟨target, requested, found⟩ := List.mem_filterMap.mp symbol
    cases observedAt : observed target with
    | none => simp [observedAt] at found
    | some value =>
        have same : value.name = name := by simpa [observedAt] using found
        subst name
        exact used_at formulas observed guard target value
          (sensitive_requested guard target (by simpa [orderedPaths] using requested)) observedAt

private theorem filterMap_congr (items : List α) (first second : α → Option β)
    (same : ∀ item ∈ items, first item = second item) : items.filterMap first = items.filterMap second := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.filterMap_cons, same item (by simp),
      ih (fun value member => same value (by simp [member]))]

/-- Semantic ambient names are exactly equal across read-equivalent source cells. -/
theorem ambient_reads (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (reads : Reads guard first second) :
    ambient formulas first guard = ambient formulas second guard := by
  have refinements : refinementNames formulas first guard = refinementNames formulas second guard := by
    unfold refinementNames
    apply congrArg List.flatten
    apply List.map_congr_left
    intro target member
    have same := reads.refinements target (by simpa [orderedPaths] using member)
    cases a : first target <;> cases b : second target <;> simp_all
  have symbols : symbolNames first guard = symbolNames second guard := by
    unfold symbolNames
    apply filterMap_congr
    intro target member
    rw [reads.symbols target (by simpa [orderedPaths] using member)]
  simp only [ambient, refinements, symbols]

/-- A structurally observed constructor name is in the semantic ambient set. -/
theorem symbol_ambient (formulas : Formulas Formula) (observed : Observations Formula) (guard : Guard Formula)
    (path : Path) (value : Observed Formula) (requested : path ∈ sensitive guard)
    (found : observed path = some value) : value.name ∈ ambient formulas observed guard := by
  apply List.mem_append_right
  apply List.mem_filterMap.mpr
  exact ⟨path, by simpa [orderedPaths] using requested, by simp [found]⟩

/-- Every refinement read contributes all its free names to the semantic ambient set. -/
theorem refinement_ambient (formulas : Formulas Formula) (observed : Observations Formula) (guard : Guard Formula)
    (path : Path) (value : Observed Formula) (name : Name) (requested : path ∈ paths guard)
    (found : observed path = some value) (free : name ∈ formulas.freeNames value.refinement) :
    name ∈ ambient formulas observed guard := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨path, by simpa [orderedPaths] using requested, by simpa [found] using free⟩

/-- Track all original semantic values and the first pass's allocated values. -/
def live [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula) (guard : Guard Formula) : List Name :=
  ambient formulas observed guard ++ freshNames (usedNames formulas observed guard)
    (conflicts observed (sameShape formulas observed []) guard).length

/-- The constructed fresh map avoids every unmapped tracked name in both source cells. -/
theorem live_avoid [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (reads : Reads guard first second)
    (name : Name) (member : name ∈ live formulas first guard)
    (unmapped : name ∉ (tableRenaming formulas guard first second).map Prod.fst) :
    name ∉ (tableRenaming formulas guard first second).map Prod.snd := by
  unfold tableRenaming at unmapped ⊢
  rw [fresh_keys] at unmapped
  rw [fresh_targets]
  have oldAmbient : name ∈ ambient formulas first guard := (List.mem_append.mp member).resolve_right unmapped
  have newAmbient : name ∈ ambient formulas second guard := ambient_reads formulas guard first second reads ▸ oldAmbient
  exact fun fresh => SourceActuals.fresh_avoids _ _ name fresh (ambient_used formulas second guard name newAmbient)

/-- The actual source spelling map is injective on the derived semantic live set. -/
theorem live_injective [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (reads : Reads guard first second) :
    ∀ left ∈ live formulas first guard, ∀ right ∈ live formulas first guard,
      renameName (tableRenaming formulas guard first second) left =
        renameName (tableRenaming formulas guard first second) right → left = right :=
  SourceScopeEnvironment.injective_live _ _ (renaming_unique formulas guard first second).2
    (live_avoid formulas guard first second reads)

/-- Every semantic ambient name is fixed by the constructed source name map. -/
theorem ambient_fixed [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (name : Name) (member : name ∈ ambient formulas first guard) :
    renameName (tableRenaming formulas guard first second) name = name :=
  fixed_used formulas guard first second name (ambient_used formulas first guard name member)

private theorem lookup_member {α β : Type} [BEq α] [LawfulBEq α]
    (entries : List (α × β)) (key : α) (value : β) (found : entries.lookup key = some value) :
    (key, value) ∈ entries := by
  obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp found
  rw [same]
  simp

/-- Every allocated row contains a name from the executed source fresh stream. -/
theorem allocated_fresh [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (guard : Guard Formula) (path : Path) (fresh original : Name)
    (member : (path, fresh, original) ∈ allocated formulas observed (sameShape formulas observed []) guard) :
    fresh ∈ freshNames (usedNames formulas observed guard) (conflicts observed (sameShape formulas observed []) guard).length := by
  obtain ⟨pair, present, same⟩ := List.mem_map.mp member
  have value := (List.of_mem_zip present).2
  have equal : pair.2 = fresh := congrArg (fun entry : Path × (Name × Name) => entry.2.1) same
  exact equal ▸ value

/-- Per-path declaration copying introduces no fresh name outside its executed allocation stream. -/
theorem declaration_fresh [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (guard : Guard Formula) (path : Path) (fresh original : Name)
    (member : (path, fresh, original) ∈ (substitutionValues formulas observed (sameShape formulas observed []) guard).1) :
    fresh ∈ freshNames (usedNames formulas observed guard) (conflicts observed (sameShape formulas observed []) guard).length := by
  obtain ⟨actual, _, found⟩ := List.mem_filterMap.mp member
  cases copied : (allocated formulas observed (sameShape formulas observed []) guard).lookup
      (representative observed (sameShape formulas observed []) (actuals observed guard) actual) with
  | none => simp [copied] at found
  | some binding =>
      simp only [copied, Option.map_some, Option.some.injEq] at found
      have chosen := allocated_fresh formulas observed guard _ binding.1 binding.2 (lookup_member _ _ _ copied)
      have equal : binding.1 = fresh := congrArg (fun entry : Path × (Name × Name) => entry.2.1) found
      exact equal ▸ chosen

/-- Every actual source resolved record closes over the derived live-name set and fixes its formal. -/
theorem resolve_live [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (substitution : Substitution) (resolved : Resolved Formula)
    (actualRead : substitution.actual ∈ sensitive guard) (formalRead : substitution.formal ∈ sensitive guard)
    (success : resolve formulas first (substitutionValues formulas first (sameShape formulas first []) guard).1
      (substitutionValues formulas first (sameShape formulas first []) guard).2 substitution = some resolved) :
    resolved.replacement.1 ∈ live formulas first guard ∧ resolved.replacement.2 ∈ live formulas first guard ∧
      renameName (tableRenaming formulas guard first second) resolved.replacement.1 = resolved.replacement.1 := by
  obtain ⟨actual, formal, atActual, atFormal⟩ := SourceActuals.resolve_exists formulas first _ _ substitution resolved success
  have actualName := symbol_ambient formulas first guard _ actual actualRead atActual
  have formalName := symbol_ambient formulas first guard _ formal formalRead atFormal
  simp [resolve, atActual, atFormal] at success
  subst resolved
  refine ⟨List.mem_append_left _ formalName, ?_, ambient_fixed formulas guard first second formal.name formalName⟩
  cases declaration : (substitutionValues formulas first (sameShape formulas first []) guard).1.lookup substitution.actual with
  | none =>
      simpa [declaration, live] using List.mem_append_left
        (freshNames (usedNames formulas first guard) (conflicts first (sameShape formulas first []) guard).length) actualName
  | some binding =>
      have fresh := declaration_fresh formulas first guard substitution.actual binding.1 binding.2
        (lookup_member _ _ _ declaration)
      simpa [declaration, live] using List.mem_append_right (ambient formulas first guard) fresh

/-- Every successful source scope satisfies the finite name invariant used by nested scope transport. -/
theorem resolveMany_live [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (additions : List Substitution) (resolved : List (Resolved Formula))
    (requested : ∀ entry ∈ additions, entry.actual ∈ sensitive guard ∧ entry.formal ∈ sensitive guard)
    (success : resolveMany formulas first (substitutionValues formulas first (sameShape formulas first []) guard).1
      (substitutionValues formulas first (sameShape formulas first []) guard).2 additions = some resolved) :
    ∀ entry ∈ resolved, entry.replacement.1 ∈ live formulas first guard ∧ entry.replacement.2 ∈ live formulas first guard ∧
      renameName (tableRenaming formulas guard first second) entry.replacement.1 = entry.replacement.1 := by
  induction additions generalizing resolved with
  | nil => simp [resolveMany] at success; subst resolved; simp
  | cons addition rest ih =>
      cases head : resolve formulas first (substitutionValues formulas first (sameShape formulas first []) guard).1
          (substitutionValues formulas first (sameShape formulas first []) guard).2 addition with
      | none => simp [resolveMany, head] at success
      | some firstResolved =>
          cases tail : resolveMany formulas first (substitutionValues formulas first (sameShape formulas first []) guard).1
              (substitutionValues formulas first (sameShape formulas first []) guard).2 rest with
          | none => simp [resolveMany, head, tail] at success
          | some restResolved =>
              have same : firstResolved :: restResolved = resolved := by simpa [resolveMany, head, tail] using success
              subst resolved
              intro entry member
              rcases List.mem_cons.mp member with rfl | later
              · have positions := requested addition (by simp)
                exact resolve_live formulas guard first second addition entry positions.1 positions.2 head
              · exact ih restResolved (fun item member => requested item (by simp [member])) tail entry later

end MicroCFTA.SourceSemanticNames
