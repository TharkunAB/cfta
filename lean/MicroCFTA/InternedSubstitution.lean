import MicroCFTA.InternedBinderRebuild

/-!
# Recursive binder reconstruction with a finite fresh-name supply

The worker follows the prepared substitution branches, including the closed
shortcut, ordered children, restricted binder environments, and cleanup.
Its explicit name supply is an alpha-renaming witness. Runtime hash-consing
and the two-probe identity key retain their separate representation boundary.
-/
namespace MicroCFTA.InternedSubstitution
open Language Binding BinderLanguage EnumerationBinderExposure LexicalBinderClosure
open InternedBinderRebuild

/-- Read free names only from replacements that the current shape can use. -/
def replacementNames (environment : Environment Item) (names : List Nat) : List Nat :=
  names.flatMap fun name => match environment name with
    | none => []
    | some replacement => free replacement

/-- Each relevant replacement contributes every one of its free names. -/
theorem replacementNames_member (environment : Environment Item) (names : List Nat)
    (name : Nat) (replacement : Shape Item) (relevant : name ∈ names)
    (found : environment name = some replacement) (reference : Nat) (member : reference ∈ free replacement) :
    reference ∈ replacementNames environment names := by
  apply List.mem_flatMap.mpr
  exact ⟨name, relevant, by simp [found, member]⟩

/-- Skip all names in the body and its relevant replacements before allocating a binder. -/
def allocate (next name : Nat) (body : Shape Item) (environment : Environment Item) : Nat :=
  max next (ceiling (name :: free body ++ bound body ++
    replacementNames environment (free (.binder name body))))

/-- A selected fresh name respects the incoming finite supply. -/
theorem allocate_lower (next name : Nat) (body : Shape Item) (environment : Environment Item) :
    next ≤ allocate next name body environment := Nat.le_max_left _ _

/-- The fresh name is absent from the body and every replacement that its external bindings can read. -/
theorem allocate_fresh (next name : Nat) (body : Shape Item) (environment : Environment Item) :
    allocate next name body environment ∉ free body ∧
      (∀ reference ∈ free (.binder name body), ∀ replacement,
        environment reference = some replacement → allocate next name body environment ∉ free replacement) := by
  have smaller : ∀ reference ∈ name :: free body ++ bound body ++
      replacementNames environment (free (.binder name body)), reference < allocate next name body environment := by
    intro reference member
    have below := below_ceiling _ reference member
    unfold allocate
    omega
  constructor
  · intro member
    exact Nat.lt_irrefl _ (smaller _ (by simp [member]))
  · intro reference relevant replacement found member
    have included := replacementNames_member environment _ reference replacement relevant found _ member
    exact Nat.lt_irrefl _ (smaller _ (by simp [included]))

/-- Local semantic binding commutes with every external replacement, including outer references. -/
theorem local_semantics (semantic : Env Symbol) (next name : Nat)
    (body : Shape (Payload Symbol)) (environment : Environment (Payload Symbol)) (value : Lang Symbol) :
    meaning (substitutedEnv (BinderLanguage.bind semantic (allocate next name body environment) value)
      (localBindings name (allocate next name body environment) body environment)) body =
      meaning (BinderLanguage.bind (substitutedEnv semantic environment) name value) body := by
  apply meaning_congr
  intro reference member
  by_cases hit : reference = name
  · simp [substitutedEnv, localBindings, hit, meaning, BinderLanguage.bind]
  · have relevant : reference ∈ free (.binder name body) := by simp [free, member, hit]
    have different : reference ≠ allocate next name body environment :=
      fun same => (allocate_fresh next name body environment).1 (same ▸ member)
    simp only [substitutedEnv, localBindings, hit, ↓reduceIte, restrict, relevant]
    cases found : environment reference with
    | none => simp [BinderLanguage.bind, hit, different, substitutedEnv, found]
    | some replacement =>
        simp only [BinderLanguage.bind, hit, ↓reduceIte, substitutedEnv, found]
        apply meaning_congr
        intro other present
        have absent := (allocate_fresh next name body environment).2 reference relevant replacement found
        have different : other ≠ allocate next name body environment := fun same => absent (same ▸ present)
        simp [BinderLanguage.bind, different]

mutual
/-- Apply a prepared shape while threading the finite binder-name supply. -/
def run (next : Nat) (environment : Environment (Payload Symbol))
    (shape : Shape (Payload Symbol)) : Shape (Payload Symbol) × Nat :=
  if (free shape).isEmpty then (shape, next) else
  match shape with
  | .empty => (.empty, next)
  | .ref name => ((environment name).getD (.ref name), next)
  | .branch payload children =>
      let result := runForest next environment children
      (.branch payload result.1, result.2)
  | .alternatives members =>
      let result := runForest next environment members
      (.alternatives result.1, result.2)
  | .binder name body =>
      let fresh := allocate next name body environment
      let result := run (fresh + 1) (localBindings name fresh body environment) body
      (cleanup (.binder fresh (BinderSelfUnion.withoutSelf fresh result.1)), result.2)
termination_by sizeOf shape

/-- Rebuild child plans in order and pass each resulting supply to the next child. -/
def runForest (next : Nat) (environment : Environment (Payload Symbol))
    (shapes : List (Shape (Payload Symbol))) : List (Shape (Payload Symbol)) × Nat :=
  match shapes with
  | [] => ([], next)
  | first :: rest =>
      let head := run next environment first
      let tail := runForest head.2 environment rest
      (head.1 :: tail.1, tail.2)
termination_by sizeOf shapes
end

/-- Closed input syntax ignores every external replacement in its semantic environment. -/
theorem closed_semantics (shape : Shape (Payload Symbol)) (semantic : Env Symbol)
    (environment : Environment (Payload Symbol)) (closed : free shape = []) :
    meaning semantic shape = meaning (substitutedEnv semantic environment) shape := by
  apply meaning_congr
  intro name member
  simp [closed] at member

/-- Pointwise child language equality preserves the complete ordered forest. -/
theorem forest_languages (left right : List (Shape (Payload Symbol))) (first second : Env Symbol)
    (related : All₂ (fun l r => meaning first l = meaning second r) left right)
    (terms : List (Term Symbol)) :
    BinderLanguage.forest first left terms ↔ BinderLanguage.forest second right terms := by
  induction related generalizing terms with
  | nil => cases terms <;> simp [BinderLanguage.forest]
  | cons head tail ih => cases terms <;> simp [BinderLanguage.forest, head, ih]

/-- The first alternative contributes exactly one disjunct. -/
theorem alternatives_cons (semantic : Env Symbol) (first : Shape (Payload Symbol))
    (rest : List (Shape (Payload Symbol))) (term : Term Symbol) :
    meaning semantic (.alternatives (first :: rest)) term ↔
      meaning semantic first term ∨ meaning semantic (.alternatives rest) term := by
  simp only [meaning]
  constructor
  · rintro ⟨⟨shape, member⟩, accepted⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl accepted
    · exact Or.inr ⟨⟨shape, member⟩, accepted⟩
  · rintro (accepted | ⟨⟨shape, member⟩, accepted⟩)
    · exact ⟨⟨first, by simp⟩, accepted⟩
    · exact ⟨⟨shape, by simp [member]⟩, accepted⟩

/-- Pointwise alternative equality preserves the entire union language. -/
theorem alternatives_languages (left right : List (Shape (Payload Symbol))) (first second : Env Symbol)
    (related : All₂ (fun l r => meaning first l = meaning second r) left right) :
    meaning first (.alternatives left) = meaning second (.alternatives right) := by
  funext term
  apply propext
  induction related with
  | nil => simp [meaning]
  | cons head tail ih => rw [alternatives_cons, alternatives_cons, head, ih]

/-- The complete recursive worker implements capture-avoiding semantic substitution. -/
theorem run_exact (shape : Shape (Payload Symbol)) (next : Nat) (semantic : Env Symbol)
    (environment : Environment (Payload Symbol)) :
    meaning semantic (run next environment shape).1 = meaning (substitutedEnv semantic environment) shape := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => ∀ next semantic environment,
      All₂ (fun result original => meaning semantic result = meaning (substitutedEnv semantic environment) original)
        (runForest next environment shapes).1 shapes)
    generalizing next semantic environment with
  | empty => simp [run, free, meaning]
  | ref name =>
      cases found : environment name <;> simp [run, free, found, meaning, substitutedEnv]
  | branch payload children ih =>
      by_cases closed : (freeList children).isEmpty = true
      · simpa only [run, free, closed, ↓reduceIte] using
          closed_semantics (.branch payload children) semantic environment (List.isEmpty_iff.mp closed)
      · simp only [run, free, closed, Bool.false_eq_true, ↓reduceIte, meaning]
        funext term
        apply propext
        simp only [forest_languages _ _ semantic (substitutedEnv semantic environment)
          (ih next semantic environment)]
  | alternatives members ih =>
      by_cases closed : (freeList members).isEmpty = true
      · simpa only [run, free, closed, ↓reduceIte] using
          closed_semantics (.alternatives members) semantic environment (List.isEmpty_iff.mp closed)
      · simpa only [run, free, closed, Bool.false_eq_true, ↓reduceIte] using
          alternatives_languages _ _ semantic _ (ih next semantic environment)
  | binder name body ih =>
      by_cases closed : (free (.binder name body)).isEmpty = true
      · simpa only [run, closed, ↓reduceIte] using
          closed_semantics (.binder name body) semantic environment (List.isEmpty_iff.mp closed)
      · simp only [run, closed, Bool.false_eq_true, ↓reduceIte]
        rw [BinderSelfUnion.cleanup_exact]
        simp only [meaning]
        apply least_congr
        intro value term
        rw [ih, local_semantics]
  | nil => simp only [runForest]; exact .nil
  | cons first rest ih ir =>
      rename_i next semantic environment
      simp only [runForest]
      apply All₂.cons
      · exact ih next semantic environment
      · exact ir _ semantic environment

/-- Every recursive application returns a supply at or above its input supply. -/
theorem run_supply (shape : Shape (Payload Symbol)) (next : Nat)
    (environment : Environment (Payload Symbol)) : next ≤ (run next environment shape).2 := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => ∀ next environment, next ≤ (runForest next environment shapes).2)
    generalizing next environment with
  | empty => simp [run, free]
  | ref name => simp [run, free]
  | branch payload children ih =>
      unfold run
      split
      · exact Nat.le_refl _
      · exact ih next environment
  | alternatives members ih =>
      unfold run
      split
      · exact Nat.le_refl _
      · exact ih next environment
  | binder name body ih =>
      unfold run
      split
      · exact Nat.le_refl _
      · have lower := allocate_lower next name body environment
        have progress := ih (allocate next name body environment + 1)
          (localBindings name (allocate next name body environment) body environment)
        dsimp only
        omega
  | nil => simp [runForest]
  | cons first rest ih ir =>
      rename_i next environment
      have head := ih next environment
      have tail := ir (run next environment first).2 environment
      simp only [runForest]
      omega

/-- Recursive rebuilding introduces no free name beyond the names in actual replacements. -/
theorem run_free (shape : Shape (Payload Symbol)) (next : Nat)
    (environment : Environment (Payload Symbol)) (allowed : Nat → Prop)
    (resolved : ∀ name ∈ free shape, match environment name with
      | none => allowed name
      | some replacement => ∀ reference ∈ free replacement, allowed reference) :
    ∀ reference ∈ free (run next environment shape).1, allowed reference := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => ∀ (next : Nat) (environment : Environment (Payload Symbol)) (allowed : Nat → Prop),
      (∀ name ∈ freeList shapes, match environment name with
        | none => allowed name
        | some replacement => ∀ reference ∈ free replacement, allowed reference) →
      ∀ reference ∈ freeList (runForest next environment shapes).1, allowed reference)
    generalizing next environment allowed with
  | empty => simp [run, free]
  | ref name =>
      have result := resolved name (by simp [free])
      cases found : environment name <;> simpa [run, free, found] using result
  | branch payload children ih =>
      by_cases closed : (freeList children).isEmpty = true
      · have empty := List.isEmpty_iff.mp closed
        simp [run, free, empty]
      · simp only [run, free, closed, Bool.false_eq_true, ↓reduceIte, free]
        exact ih next environment allowed resolved
  | alternatives members ih =>
      by_cases closed : (freeList members).isEmpty = true
      · have empty := List.isEmpty_iff.mp closed
        simp [run, free, empty]
      · simp only [run, free, closed, Bool.false_eq_true, ↓reduceIte, free]
        exact ih next environment allowed resolved
  | binder name body ih =>
      by_cases closed : (free (.binder name body)).isEmpty = true
      · have empty := List.isEmpty_iff.mp closed
        simp [run, empty]
      · intro reference member
        simp only [run, closed, Bool.false_eq_true, ↓reduceIte] at member
        have before := IntersectSchedule.cleanup_free _ reference member
        rw [BinderSelfUnion.binder_free_exact] at before
        have outside : reference ∈ free (run (allocate next name body environment + 1)
            (localBindings name (allocate next name body environment) body environment) body).1 ∧
            reference ≠ allocate next name body environment := by simpa [free] using before
        have result := ih (allocate next name body environment + 1)
          (localBindings name (allocate next name body environment) body environment)
          (fun other => other = allocate next name body environment ∨ allowed other) (by
            intro other present
            by_cases hit : other = name
            · simp [localBindings, hit, free]
            · have relevant : other ∈ free (.binder name body) := by simp [free, present, hit]
              have original := resolved other relevant
              cases found : environment other with
              | none => simpa [localBindings, hit, restrict, relevant, found] using Or.inr original
              | some replacement =>
                  simp only [localBindings, hit, ↓reduceIte, restrict, relevant, found]
                  simp only [found] at original
                  intro target targetMember
                  exact Or.inr (original target targetMember)) reference outside.1
        exact result.resolve_left outside.2
  | nil =>
      rename_i next environment allowed resolved reference member
      simp [runForest, freeList] at member
  | cons first rest ih ir =>
      rename_i next environment allowed resolved reference member
      simp only [runForest, freeList, List.mem_append] at member
      rcases member with head | tail
      · exact ih next environment allowed (fun name present => resolved name (by simp [freeList, present])) reference head
      · exact ir _ environment allowed (fun name present => resolved name (by simp [freeList, present])) reference tail

/-- Closed supplied values produce a closed result when they resolve all original free references. -/
theorem run_closed (shape : Shape (Payload Symbol)) (next : Nat)
    (environment : Environment (Payload Symbol)) (closed : ClosedEnvironment environment)
    (resolved : Resolved environment shape) : free (run next environment shape).1 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro reference member
  apply run_free shape next environment (fun _ => False) ?_ reference member
  intro name present
  obtain ⟨replacement, found⟩ := resolved name present
  simp [found, closed name replacement found]

/-- Closed external values connect the recursively rebuilt worker to lexical substitution. -/
theorem run_lexical (shape : Shape (Payload Symbol)) (next : Nat) (semantic : Env Symbol)
    (environment : Environment (Payload Symbol)) (closed : ClosedEnvironment environment) :
    meaning semantic (run next environment shape).1 = meaning semantic (substitute environment shape) := by
  rw [run_exact, substitution_exact shape semantic environment (by
    intro binder member name replacement found
    simp [closed name replacement found])]

/-- The starting allocation counter cannot affect any substituted term language. -/
theorem allocation_independent (shape : Shape (Payload Symbol)) (first second : Nat)
    (semantic : Env Symbol) (environment : Environment (Payload Symbol)) :
    meaning semantic (run first environment shape).1 = meaning semantic (run second environment shape).1 := by
  rw [run_exact, run_exact]

/-- Repeated nested reconstruction has the exact visited constructor-row language. -/
theorem run_exposed [DecidableEq (Shape (Payload Symbol))] (shape : Shape (Payload Symbol))
    (next : Nat) (semantic : Env Symbol) (environment : Environment (Payload Symbol))
    (closed : ClosedEnvironment environment) (resolved : Resolved environment shape) (term : Term Symbol) :
    rowsMeaning semantic (exposedRows (run next environment shape).1) term ↔
      meaning semantic (substitute environment shape) term := by
  rw [LexicalExposureLanguage.exposed_language semantic _ (run_closed shape next environment closed resolved),
    run_lexical shape next semantic environment closed]

/-- All later lexical requests from a closed rebuilt result avoid a raw reference. -/
theorem run_no_unexpected_reference (shape : Shape (Payload Symbol)) (next : Nat)
    (environment : Environment (Payload Symbol)) (closed : ClosedEnvironment environment)
    (resolved : Resolved environment shape) (reference : Nat) :
    ¬ Reachable (run next environment shape).1 (.ref reference) :=
  no_unexpected_reference (run_closed shape next environment closed resolved) reference

/-- Outer unfolding replaces the binder reference through the complete nested reconstruction worker. -/
def unfoldRebuilt (next name : Nat) (body : Shape (Payload Symbol)) : Shape (Payload Symbol) :=
  (run next (single name (.binder name body)) body).1

/-- Full nested binder rebuilding preserves the least language of an unfolded binder. -/
theorem unfoldRebuilt_exact (next name : Nat) (body : Shape (Payload Symbol)) (semantic : Env Symbol) :
    meaning semantic (unfoldRebuilt next name body) = meaning semantic (.binder name body) := by
  rw [unfoldRebuilt, run_exact, single_environment]
  funext term
  exact propext (binder_unfold semantic name body term).symm

/-- A closed outer binder supplies every free reference in its original body. -/
theorem unfoldRebuilt_closed (next name : Nat) (body : Shape (Payload Symbol))
    (closed : free (.binder name body) = []) : free (unfoldRebuilt next name body) = [] := by
  apply run_closed body next (single name (.binder name body))
  · intro reference replacement found
    by_cases hit : reference = name
    · have same : replacement = .binder name body := by simpa [single, hit] using found.symm
      simpa [same] using closed
    · simp [single, hit] at found
  · intro reference member
    have same := closed_body_reference name body closed reference member
    exact ⟨.binder name body, by simp [single, same]⟩

/-- The visited epsilon worker exposes the exact original language after every nested reconstruction. -/
theorem unfoldRebuilt_exposed [DecidableEq (Shape (Payload Symbol))] (next name : Nat)
    (body : Shape (Payload Symbol)) (semantic : Env Symbol)
    (closed : free (.binder name body) = []) (term : Term Symbol) :
    rowsMeaning semantic (exposedRows (unfoldRebuilt next name body)) term ↔
      meaning semantic (.binder name body) term := by
  rw [LexicalExposureLanguage.exposed_language semantic _ (unfoldRebuilt_closed next name body closed),
    unfoldRebuilt_exact]

/-- Constructor-depth bounds use the same language after nested reconstruction and epsilon exposure. -/
theorem unfoldRebuilt_bounded [DecidableEq (Shape (Payload Symbol))] (next name : Nat)
    (body : Shape (Payload Symbol)) (semantic : Env Symbol)
    (closed : free (.binder name body) = []) (height : Nat) (term : Term Symbol) :
    Accepts (BoundDepth.bound LexicalExposureLanguage.automaton)
        (height, unfoldRebuilt next name body) term ↔
      meaning semantic (.binder name body) term ∧ term.height ≤ height := by
  rw [LexicalExposureLanguage.bounded_exact semantic _ (unfoldRebuilt_closed next name body closed),
    unfoldRebuilt_exact]

/-- An ordered child traversal cannot move the name supply backward. -/
theorem runForest_supply (shapes : List (Shape (Payload Symbol))) (next : Nat)
    (environment : Environment (Payload Symbol)) : next ≤ (runForest next environment shapes).2 := by
  induction shapes generalizing next with
  | nil => simp [runForest]
  | cons first rest ih =>
      have head := run_supply first next environment
      have tail := ih (run next environment first).2
      simp only [runForest]
      omega

mutual
/-- Record exactly the names allocated by one execution of the recursive worker. -/
def issued (next : Nat) (environment : Environment (Payload Symbol))
    (shape : Shape (Payload Symbol)) : List Nat :=
  if (free shape).isEmpty then [] else
  match shape with
  | .empty | .ref _ => []
  | .branch _ children | .alternatives children => issuedForest next environment children
  | .binder name body =>
      let fresh := allocate next name body environment
      fresh :: issued (fresh + 1) (localBindings name fresh body environment) body
termination_by sizeOf shape

/-- The allocation trace follows the same child order and intermediate supplies as the worker. -/
def issuedForest (next : Nat) (environment : Environment (Payload Symbol))
    (shapes : List (Shape (Payload Symbol))) : List Nat :=
  match shapes with
  | [] => []
  | first :: rest => issued next environment first ++
      issuedForest (run next environment first).2 environment rest
termination_by sizeOf shapes
end

/-- Every allocation lies between the input supply and the returned supply. -/
theorem issued_range (shape : Shape (Payload Symbol)) (next : Nat)
    (environment : Environment (Payload Symbol)) (name : Nat) (member : name ∈ issued next environment shape) :
    next ≤ name ∧ name < (run next environment shape).2 := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => ∀ next environment name, name ∈ issuedForest next environment shapes →
      next ≤ name ∧ name < (runForest next environment shapes).2)
    generalizing next environment name with
  | empty | ref => simp [issued] at member
  | branch payload children ih =>
      unfold issued at member
      split at member
      · simp at member
      · next opened => simpa only [run, opened, Bool.false_eq_true, ↓reduceIte] using ih next environment name member
  | alternatives members ih =>
      unfold issued at member
      split at member
      · simp at member
      · next opened => simpa only [run, opened, Bool.false_eq_true, ↓reduceIte] using ih next environment name member
  | binder old body ih =>
      unfold issued at member
      split at member
      · simp at member
      · next opened =>
          simp only [run, opened, Bool.false_eq_true, ↓reduceIte]
          have lower := allocate_lower next old body environment
          rcases List.mem_cons.mp member with rfl | remaining
          · have higher := run_supply body (allocate next old body environment + 1)
              (localBindings old (allocate next old body environment) body environment)
            exact ⟨lower, by omega⟩
          · have bounds := ih _ _ name remaining
            exact ⟨by omega, bounds.2⟩
  | nil => rename_i next environment name member; simp [issuedForest] at member
  | cons first rest ih ir =>
      rename_i next environment name member
      simp only [issuedForest, List.mem_append] at member
      simp only [runForest]
      rcases member with head | tail
      · have bounds := ih next environment name head
        have supply := runForest_supply rest (run next environment first).2 environment
        exact ⟨bounds.1, by omega⟩
      · have bounds := ir _ environment name tail
        have supply := run_supply first next environment
        exact ⟨by omega, bounds.2⟩

/-- Every child-list allocation has the same finite supply bounds. -/
theorem issuedForest_range (shapes : List (Shape (Payload Symbol))) (next : Nat)
    (environment : Environment (Payload Symbol)) (name : Nat) (member : name ∈ issuedForest next environment shapes) :
    next ≤ name ∧ name < (runForest next environment shapes).2 := by
  induction shapes generalizing next with
  | nil => simp [issuedForest] at member
  | cons first rest ih =>
      simp only [issuedForest, List.mem_append] at member
      simp only [runForest]
      rcases member with head | tail
      · have bounds := issued_range first next environment name head
        have supply := runForest_supply rest (run next environment first).2 environment
        exact ⟨bounds.1, by omega⟩
      · have bounds := ih _ tail
        have supply := run_supply first next environment
        exact ⟨by omega, bounds.2⟩

/-- Nested binders and separate children never receive the same new identity in one execution. -/
theorem issued_distinct (shape : Shape (Payload Symbol)) (next : Nat)
    (environment : Environment (Payload Symbol)) : (issued next environment shape).Nodup := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => ∀ next environment, (issuedForest next environment shapes).Nodup)
    generalizing next environment with
  | empty | ref => simp [issued]
  | branch payload children ih =>
      unfold issued
      split
      · simp
      · exact ih next environment
  | alternatives members ih =>
      unfold issued
      split
      · simp
      · exact ih next environment
  | binder name body ih =>
      unfold issued
      split
      · simp
      · apply List.nodup_cons.mpr
        constructor
        · intro member
          have bounds := issued_range body _ _ _ member
          omega
        · exact ih _ _
  | nil => simp [issuedForest]
  | cons first rest ih ir =>
      rename_i next environment
      simp only [issuedForest]
      apply List.nodup_append.mpr
      refine ⟨ih next environment, ir _ environment, ?_⟩
      intro name head other tail same
      subst other
      have earlier := issued_range first next environment name head
      have later := issuedForest_range rest _ environment name tail
      omega

/-- An outer free reference remains free when a nested binder previously used the same name. -/
theorem open_replacement_not_captured :
    (run 0 (single 1 (.ref 0 : Shape (Payload Symbol))) (.binder 0 (.ref 1))).1 = .ref 0 := by
  simp [run, free, allocate, replacementNames, ceiling, bound, localBindings, restrict, single, BinderSelfUnion.withoutSelf, cleanup]

/-- Rebuilding an open binder removes its bare self alternative before unused-binder cleanup. -/
theorem root_self_removed (payload : Payload Symbol) :
    (run 0 (single 1 (.branch payload [])) (.binder 0 (.alternatives [.ref 0, .ref 1]))).1 =
      .alternatives [.branch payload []] := by
  simp [run, runForest, free, freeList, allocate, replacementNames, ceiling, bound, boundList,
    localBindings, restrict, single, BinderSelfUnion.withoutSelf, BinderSelfUnion.isSelf, cleanup]

end MicroCFTA.InternedSubstitution
