import MicroCFTA.SourceFiniteBackend
import MicroCFTA.SymbolicEqualityBridge
import MicroCFTA.EqualitySource

/-!
# Positive source guards and the direct-child parser

Positive equality extraction rejects reflexive Same guards. The raw classes
below retain the source traversal order. The existing normalization proof
connects these classes to a completed equality normalizer run.
-/
namespace MicroCFTA.SourceCompactGuards
open Language SourceGuards SourceObservations SourceSymbolicIndex
open CompactGroups CompactEdgeRanks SymbolicDriver

mutual
/-- The source positiveEqualities syntax test, before class normalization. -/
def positive : Guard Formula → Option (List (List Path))
  | .top => some []
  | .same left right => if left ≠ right then some [[left, right]] else none
  | .and parts => positiveList parts
  | _ => none

/-- Source right-fold extraction retains all positive operands. -/
def positiveList : List (Guard Formula) → Option (List (List Path))
  | [] => some []
  | first :: rest => do
      let initial ← positive first
      let remaining ← positiveList rest
      pure (initial ++ remaining)
end

mutual
/-- Extracted raw classes have exactly the current public guard semantics. -/
theorem positive_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (classes : List (List Path)) (extracted : positive guard = some classes)
    (term : Term (Label Formula)) :
    SourceBooleanEntry.evaluateGuard formulas solver guard term = .yes ↔ classes.all (classTest term) = true := by
  cases guard with
  | top =>
      have empty : classes = [] := by simpa [positive] using extracted.symm
      simp [empty, SourceBooleanEntry.evaluateGuard, SourceBooleanEntry.evaluateGuardWithSame,
        SourceBooleanEntry.evaluate, SourceBooleanEntry.scoped_eq, evaluateWith, polarize]
  | same left right =>
      simp only [positive] at extracted
      split at extracted
      · have same : classes = [[left, right]] := Option.some.inj extracted.symm
        subst classes
        unfold SourceBooleanEntry.evaluateGuard SourceBooleanEntry.evaluateGuardWithSame
        rw [SourceEqualityGuards.same_exact]
        simp only [List.all_cons, List.all_nil, Bool.and_true,
          SourceEqualityGuards.pair_class term (left, right)]
        cases SourceEqualityGuards.pairTest term (left, right) <;>
          simp [SourceEqualityGuards.signed, SourceEqualityGuards.verdict, polarize]
      · cases extracted
  | and parts =>
      unfold SourceBooleanEntry.evaluateGuard
      rw [SourceBooleanEntry.conjunction_yes]
      exact positiveList_exact formulas solver parts classes extracted term
  | bottom | entails _ _ | satisfies _ _ | holds _ _ | substitute _ _ | not _ | or _ =>
      cases extracted

/-- The extracted right fold has the same all-operands condition. -/
theorem positiveList_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guards : List (Guard Formula)) (classes : List (List Path)) (extracted : positiveList guards = some classes)
    (term : Term (Label Formula)) :
    (∀ guard ∈ guards, SourceBooleanEntry.evaluateGuard formulas solver guard term = .yes) ↔
      classes.all (classTest term) = true := by
  cases guards with
  | nil => have empty : classes = [] := by simpa [positiveList] using extracted.symm
           simp [empty]
  | cons first rest =>
      simp only [positiveList, Bind.bind, Pure.pure, Option.bind_eq_some_iff, Option.some.injEq] at extracted
      obtain ⟨initial, head, remaining, tail, same⟩ := extracted
      subst classes
      simp only [List.forall_mem_cons, List.all_append, Bool.and_eq_true]
      exact and_congr (positive_exact formulas solver first initial head term)
        (positiveList_exact formulas solver rest remaining tail term)
end

mutual
/-- Positive extraction only emits nontrivial pairs, so normalization cannot remove path existence. -/
theorem positive_active (guard : Guard Formula) (classes : List (List Path))
    (extracted : positive guard = some classes) : EqualityNormalize.Active classes := by
  cases guard with
  | top => have empty : classes = [] := by simpa [positive] using extracted.symm
           simp [empty, EqualityNormalize.Active]
  | same left right =>
      simp only [positive] at extracted
      split at extracted
      · rename_i different
        have same := Option.some.inj extracted
        subst classes
        intro paths member
        have same : paths = [left, right] := by simpa using member
        subst paths
        exact ⟨left, by simp, right, by simp, different⟩
      · cases extracted
  | and parts => exact positiveList_active parts classes extracted
  | bottom | entails _ _ | satisfies _ _ | holds _ _ | substitute _ _ | not _ | or _ => cases extracted

/-- Concatenating successful operands retains nontrivial classes. -/
theorem positiveList_active (guards : List (Guard Formula)) (classes : List (List Path))
    (extracted : positiveList guards = some classes) : EqualityNormalize.Active classes := by
  cases guards with
  | nil => have empty : classes = [] := by simpa [positiveList] using extracted.symm
           simp [empty, EqualityNormalize.Active]
  | cons first rest =>
      simp only [positiveList, Bind.bind, Pure.pure, Option.bind_eq_some_iff, Option.some.injEq] at extracted
      obtain ⟨initial, head, remaining, tail, same⟩ := extracted
      subst classes
      intro paths member
      rcases List.mem_append.mp member with member | member
      · exact positive_active first initial head paths member
      · exact positiveList_active rest remaining tail paths member
end

/-- A completed source equality normalization derives the entire compact guard law. -/
theorem normalized_guard [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (stored added : List (List Path)) (guard : Guard Formula) (fuel : Nat)
    (active : EqualityNormalize.Active stored) (extracted : positive guard = some added)
    (finished : EqualityNormalize.mkEqConstraints fuel (stored ++ added) ≠ .timeout)
    (term : Term (Label Formula)) :
    acceptsConstraint formulas solver ⟨some stored, guard⟩ term =
      ConstraintIndicators.equalityValue (classTest term)
        (SymbolicEqualityBridge.resultClasses (EqualityNormalize.mkEqConstraints fuel (stored ++ added))) := by
  have allActive : EqualityNormalize.Active (stored ++ added) := by
    intro paths member
    rcases List.mem_append.mp member with member | member
    · exact active paths member
    · exact positive_active guard added extracted paths member
  rw [SymbolicEqualityBridge.normalization_value term fuel (stored ++ added) allActive finished,
    List.all_append]
  apply Bool.eq_iff_iff.mpr
  simp only [acceptsConstraint, ConstraintIndicators.equalityValue, Bool.and_eq_true, decide_eq_true_eq]
  exact and_congr Iff.rfl (positive_exact formulas solver guard added extracted term)

/-- A contradictory cached equality field rejects every complete term. -/
theorem contradictory_guard [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (guard : Guard Formula) (term : Term (Label Formula)) :
    acceptsConstraint formulas solver ⟨none, guard⟩ term = false := by
  simp [acceptsConstraint, ConstraintIndicators.equalityValue]

/-- Natural-index view of the source's checked signed child path parser. -/
def child (arity : Nat) : Path → Option Nat
  | [index] => if index < arity then some index else none
  | _ => none

/-- Source signed parsing and the natural-path view agree for every represented path. -/
theorem child_signed (arity : Nat) (path : Path) :
    CompactGroups.childIndex arity (path.map Int.ofNat) = child arity path := by
  cases path with
  | nil => rfl
  | cons first rest => cases rest with
    | cons second rest => rfl
    | nil => simp [CompactGroups.childIndex, child]

/-- Parse one ordered equality class without losing any path. -/
def parseClass (arity : Nat) : List Path → Option (List Nat)
  | [] => some []
  | path :: rest => do
      let index ← child arity path
      let remaining ← parseClass arity rest
      pure (index :: remaining)

/-- Parse every normalized equality class in its source order. -/
def parse (arity : Nat) : List (List Path) → Option (List (List Nat))
  | [] => some []
  | paths :: rest => do
      let positions ← parseClass arity paths
      let remaining ← parse arity rest
      pure (positions :: remaining)

/-- One class uses exactly the already-proved signed source parser. -/
theorem parseClass_signed (arity : Nat) (paths : List Path) :
    CompactGroups.parseClass arity (paths.map (List.map Int.ofNat)) = parseClass arity paths := by
  induction paths with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, CompactGroups.parseClass, parseClass, child_signed, ih]

/-- The full parser is the source parser after the signed-path representation map. -/
theorem parse_signed (arity : Nat) (paths : List (List Path)) :
    CompactGroups.parseClasses arity (paths.map (List.map (List.map Int.ofNat))) = parse arity paths := by
  induction paths with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, CompactGroups.parseClasses, parse, parseClass_signed, ih]

/-- A successful parse proves the exact direct-child paths and their bounds. -/
theorem parseClass_exact (arity : Nat) (paths : List Path) (positions : List Nat) :
    parseClass arity paths = some positions ↔
      paths = positions.map (fun index => [index]) ∧ ∀ index ∈ positions, index < arity := by
  have source := CompactGroups.parseClass_exact arity (paths.map (List.map Int.ofNat)) positions
  rw [parseClass_signed] at source
  rw [source]
  have injective : Function.Injective (List.map (Int.ofNat : Nat → Int)) :=
    fun _ _ same => (List.map_inj_right (fun _ _ => Int.ofNat.inj)).mp same
  constructor
  · rintro ⟨shape, bounds⟩
    refine ⟨(List.map_inj_right (fun _ _ same => injective same)).mp ?_, bounds⟩
    simpa [List.map_map, Function.comp_def] using shape
  · rintro ⟨shape, bounds⟩
    subst paths
    exact ⟨by simp, bounds⟩

/-- Parsing retains the full equality-class structure. -/
theorem parse_exact (arity : Nat) (paths : List (List Path)) (classes : List (List Nat)) :
    parse arity paths = some classes ↔
      paths = classes.map (fun positions => positions.map (fun index => [index])) ∧ ValidClasses arity classes := by
  induction paths generalizing classes with
  | nil => cases classes <;> simp [parse, ValidClasses]
  | cons first rest ih =>
      cases classes with
      | nil =>
          simp only [parse, List.map_nil, reduceCtorEq, false_and]
          cases parseClass arity first <;> cases parse arity rest <;> simp
      | cons positions classes =>
          simp only [parse, Bind.bind, Pure.pure, Option.bind_eq_some_iff, Option.some.injEq, List.cons.injEq]
          constructor
          · rintro ⟨head, parsed, tail, remaining, sameHead, sameTail⟩
            subst head
            subst tail
            have firstFacts := (parseClass_exact arity first positions).mp parsed
            have restFacts := (ih classes).mp remaining
            exact ⟨by simp [firstFacts.1, restFacts.1], by
              intro group member
              rcases List.mem_cons.mp member with rfl | member
              · exact firstFacts.2
              · exact restFacts.2 group member⟩
          · rintro ⟨shape, valid⟩
            have pieces := List.cons.inj shape
            exact ⟨positions, (parseClass_exact arity first positions).mpr ⟨pieces.1, valid positions (by simp)⟩,
              classes, (ih classes).mpr ⟨pieces.2, fun group member => valid group (by simp [member])⟩, rfl, rfl⟩

/-- Every path in a satisfied class denotes the same existing subtree. -/
theorem satisfied_path (term : Term Symbol) (paths : List Path)
    (satisfied : Symbolic.ClassSatisfied term paths) (path : Path) (member : path ∈ paths) :
    ∃ value, term.atPath path = some value := by
  cases paths with
  | nil => cases member
  | cons first rest =>
      obtain ⟨value, head, tail⟩ := satisfied
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨value, head⟩
      · exact ⟨value, tail path member⟩

/-- Direct existing paths satisfy one parsed class exactly when its child values agree. -/
theorem direct_class (symbol : Symbol) (values : List (Term Symbol)) (positions : List Nat)
    (bounds : ∀ index ∈ positions, index < values.length) :
    Symbolic.ClassSatisfied (.node symbol values) (positions.map (fun index => [index])) ↔
      EqualAt (childValue (.node symbol []) values) positions := by
  have atIndex : ∀ index ∈ positions, (Term.node symbol values).atPath [index] =
      some (childValue (.node symbol []) values index) := by
    intro index member
    simp [Term.atPath, childValue, List.getElem?_eq_getElem (bounds index member)]
  cases positions with
  | nil => simp [Symbolic.ClassSatisfied, EqualAt]
  | cons first rest =>
      constructor
      · rintro ⟨common, head, tail⟩
        have all : ∀ index ∈ first :: rest, childValue (.node symbol []) values index = common := by
          intro index member
          apply Option.some.inj
          rw [← atIndex index member]
          rcases List.mem_cons.mp member with rfl | member
          · exact head
          · exact tail [index] (List.mem_map.mpr ⟨index, member, rfl⟩)
        intro left leftMember right rightMember
        exact (all left leftMember).trans (all right rightMember).symm
      · intro equal
        refine ⟨childValue (.node symbol []) values first, atIndex first (by simp), ?_⟩
        intro path member
        obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
        rw [atIndex index (by simp [present]), equal index (by simp [present]) first (by simp)]

/-- The direct-child parser supplies the compact edge's complete guard equivalence. -/
theorem parsed_guard (symbol : Symbol) (values : List (Term Symbol)) (paths : List (List Path))
    (classes : List (List Nat)) (parsed : parse values.length paths = some classes) :
    paths.all (classTest (.node symbol values)) = true ↔
      ∀ positions ∈ classes, EqualAt (childValue (.node symbol []) values) positions := by
  classical
  obtain ⟨rfl, valid⟩ := (parse_exact values.length paths classes).mp parsed
  simp only [List.all_eq_true, List.forall_mem_map, classTest, decide_eq_true_eq]
  exact ⟨fun accepted positions member => (direct_class symbol values positions (valid positions member)).mp (accepted positions member),
    fun accepted positions member => (direct_class symbol values positions (valid positions member)).mpr (accepted positions member)⟩

/-- The exact needsPathExpansion scan over the represented natural paths. -/
def deep (equalities : Option (List (List Path))) : Bool :=
  match equalities with
  | none => false
  | some classes => classes.any (fun paths => paths.any (fun path => path.length != 1))

/-- Every existing direct path passes the source range check. -/
theorem child_complete (symbol : Symbol) (values : List (Term Symbol)) (path : Path)
    (direct : path.length = 1) (located : ∃ value, (Term.node symbol values).atPath path = some value) :
    ∃ index, child values.length path = some index := by
  cases path with
  | nil => simp at direct
  | cons first rest =>
      have empty : rest = [] := by simpa using direct
      subst rest
      obtain ⟨value, found⟩ := located
      have within : first < values.length := by
        by_cases within : first < values.length
        · exact within
        · have missing : values[first]? = none := List.getElem?_eq_none (by omega)
          simp [Term.atPath, missing] at found
      exact ⟨first, by simp [child, within]⟩

/-- A satisfied class of direct paths cannot fail child parsing. -/
theorem parseClass_complete (symbol : Symbol) (values : List (Term Symbol)) (paths : List Path)
    (direct : ∀ path ∈ paths, path.length = 1)
    (located : ∀ path ∈ paths, ∃ value, (Term.node symbol values).atPath path = some value) :
    ∃ positions, parseClass values.length paths = some positions := by
  induction paths with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
      obtain ⟨index, head⟩ := child_complete symbol values first (direct first (by simp)) (located first (by simp))
      obtain ⟨positions, tail⟩ := ih (fun path member => direct path (by simp [member]))
        (fun path member => located path (by simp [member]))
      exact ⟨index :: positions, by simp [parseClass, head, tail]⟩

/-- The compact gate and a satisfied constraint imply a successful full child parse. -/
theorem parse_complete (symbol : Symbol) (values : List (Term Symbol)) (paths : List (List Path))
    (direct : deep (some paths) = false) (accepted : paths.all (classTest (.node symbol values)) = true) :
    ∃ classes, parse values.length paths = some classes := by
  classical
  have directPaths : ∀ group ∈ paths, ∀ path ∈ group, path.length = 1 := by
    simpa [deep, List.any_eq_false] using direct
  have satisfied : ∀ group ∈ paths, Symbolic.ClassSatisfied (.node symbol values) group := by
    simpa [List.all_eq_true, classTest] using accepted
  clear direct accepted
  induction paths with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
      obtain ⟨positions, head⟩ := parseClass_complete symbol values first (directPaths first (by simp))
        (satisfied_path (.node symbol values) first (satisfied first (by simp)))
      obtain ⟨classes, tail⟩ := ih (fun group member => directPaths group (by simp [member]))
        (fun group member => satisfied group (by simp [member]))
      exact ⟨positions :: classes, by simp [parse, head, tail]⟩

/-- Failed parsing under the compact gate denotes an empty edge, including out-of-range children. -/
theorem parse_failure (symbol : Symbol) (values : List (Term Symbol)) (paths : List (List Path))
    (direct : deep (some paths) = false) (failed : parse values.length paths = none) :
    paths.all (classTest (.node symbol values)) = false := by
  cases accepted : paths.all (classTest (.node symbol values)) with
  | false => rfl
  | true =>
      obtain ⟨classes, parsed⟩ := parse_complete symbol values paths direct accepted
      rw [failed] at parsed
      cases parsed

/-- Execute the source array normalizer at its proved iteration and work bounds. -/
noncomputable def arrayNormalize (paths : List (List Path)) : EqualityNormalize.RunResult :=
  EqualityIndex.normalizeArray (EqualityTermination.normalizationBound paths)
    (Classical.choose (EqualityIndex.normalizeArray_eventual (EqualityTermination.normalizationBound paths) paths)) paths

/-- The proved finite source array execution returns the reference normal form. -/
theorem arrayNormalize_eq (paths : List (List Path)) :
    arrayNormalize paths = EqualityNormalize.mkEqConstraints (EqualityTermination.normalizationBound paths) paths :=
  Classical.choose_spec (EqualityIndex.normalizeArray_eventual (EqualityTermination.normalizationBound paths) paths) _ (Nat.le_refl _)

/-- The source array normalizer never reaches its proof-port timeout at this bound. -/
theorem arrayNormalize_finished (paths : List (List Path)) : arrayNormalize paths ≠ .timeout := by
  rw [arrayNormalize_eq]
  exact EqualityTermination.mkEqConstraints_terminates paths

/-- The source EqConstraints view of a completed array run. -/
noncomputable def normalize (paths : List (List Path)) : Option (List (List Path)) :=
  SymbolicEqualityBridge.resultClasses (arrayNormalize paths)

/-- Canonical source equality classes are nontrivial. -/
def ActiveOption (equalities : Option (List (List Path))) : Prop :=
  ∀ paths, equalities = some paths → EqualityNormalize.Active paths

/-- Each completed array result establishes the cached-class invariant. -/
theorem normalize_active (paths : List (List Path)) : ActiveOption (normalize paths) := by
  intro output same
  unfold normalize at same
  rw [arrayNormalize_eq] at same
  cases result : EqualityNormalize.mkEqConstraints (EqualityTermination.normalizationBound paths) paths with
  | timeout | contradiction => simp [result, SymbolicEqualityBridge.resultClasses] at same
  | normalized classes =>
      have identical : classes = output := by simpa [result, SymbolicEqualityBridge.resultClasses] using same
      subst output
      exact (EqualityNormalize.mkEqConstraints_invariants _ _ _ result).1

/-- The actual completed array worker preserves existence-sensitive active classes. -/
theorem normalize_value (paths : List (List Path)) (active : EqualityNormalize.Active paths) (term : Term Symbol) :
    ConstraintIndicators.equalityValue (classTest term) (normalize paths) = paths.all (classTest term) := by
  unfold normalize
  rw [arrayNormalize_eq]
  exact SymbolicEqualityBridge.normalization_value term _ paths active (EqualityTermination.mkEqConstraints_terminates paths)

/-- The source combineEqConstraints cases, including both contradiction and empty shortcuts. -/
noncomputable def combineEqualities : Option (List (List Path)) → Option (List (List Path)) → Option (List (List Path))
  | none, _ | _, none => none
  | some [], some [] => some []
  | some first, some second => normalize (first ++ second)

/-- Combining normalized source operands keeps every stored class nontrivial. -/
theorem combine_active (first second : Option (List (List Path))) : ActiveOption (combineEqualities first second) := by
  cases first with
  | none => simp [combineEqualities, ActiveOption]
  | some first => cases second with
    | none => simp [combineEqualities, ActiveOption]
    | some second => cases first <;> cases second <;>
        first | exact normalize_active _ | simp [combineEqualities, ActiveOption, EqualityNormalize.Active]

/-- The source combination computes conjunction, including intermediate contradiction results. -/
theorem combine_value (first second : Option (List (List Path)))
    (firstActive : ActiveOption first) (secondActive : ActiveOption second) (term : Term Symbol) :
    ConstraintIndicators.equalityValue (classTest term) (combineEqualities first second) =
      (ConstraintIndicators.equalityValue (classTest term) first && ConstraintIndicators.equalityValue (classTest term) second) := by
  cases first with
  | none => simp [combineEqualities, ConstraintIndicators.equalityValue]
  | some first => cases second with
    | none => cases first <;> simp [combineEqualities, ConstraintIndicators.equalityValue]
    | some second =>
        have active : EqualityNormalize.Active (first ++ second) := by
          intro paths member
          rcases List.mem_append.mp member with member | member
          · exact firstActive first rfl paths member
          · exact secondActive second rfl paths member
        have exact := normalize_value (first ++ second) active term
        cases first <;> cases second <;>
          first | rfl | simpa [combineEqualities, ConstraintIndicators.equalityValue, List.all_append, Bool.and_assoc] using exact

mutual
/-- Actual positiveEqualities performs normalization at every Same and every conjunction step. -/
noncomputable def positiveNormalized : Guard Formula → Option (Option (List (List Path)))
  | .top => some (some [])
  | .same left right => if left ≠ right then some (normalize [[left, right]]) else none
  | .and parts => positiveNormalizedList parts
  | _ => none

/-- The source right fold normalizes each pair of accumulated equality operands. -/
noncomputable def positiveNormalizedList : List (Guard Formula) → Option (Option (List (List Path)))
  | [] => some (some [])
  | first :: rest => do
      let initial ← positiveNormalized first
      let remaining ← positiveNormalizedList rest
      pure (combineEqualities initial remaining)
end

mutual
/-- Every syntactically positive guard completes its actual staged array normalization. -/
theorem positiveNormalized_exact (guard : Guard Formula) (raw : List (List Path))
    (extracted : positive guard = some raw) :
    ∃ result, positiveNormalized guard = some result ∧ ActiveOption result ∧
      ∀ term : Term Symbol, ConstraintIndicators.equalityValue (classTest term) result = raw.all (classTest term) := by
  cases guard with
  | top =>
      have empty : raw = [] := by simpa [positive] using extracted.symm
      exact ⟨some [], rfl, by simp [ActiveOption, EqualityNormalize.Active], fun term => by simp [empty, ConstraintIndicators.equalityValue]⟩
  | same left right =>
      simp only [positive] at extracted
      split at extracted
      · rename_i different
        have same := Option.some.inj extracted
        subst raw
        exact ⟨normalize [[left, right]], by simp [positiveNormalized, different], normalize_active _,
          fun term => normalize_value _ (positive_active (.same left right : Guard Formula) _ (by simp [positive, different])) term⟩
      · cases extracted
  | and parts => exact positiveNormalizedList_exact parts raw extracted
  | bottom | entails _ _ | satisfies _ _ | holds _ _ | substitute _ _ | not _ | or _ => cases extracted

/-- The actual normalized conjunction fold agrees with the full extracted class list. -/
theorem positiveNormalizedList_exact (guards : List (Guard Formula)) (raw : List (List Path))
    (extracted : positiveList guards = some raw) :
    ∃ result, positiveNormalizedList guards = some result ∧ ActiveOption result ∧
      ∀ term : Term Symbol, ConstraintIndicators.equalityValue (classTest term) result = raw.all (classTest term) := by
  cases guards with
  | nil =>
      have empty : raw = [] := by simpa [positiveList] using extracted.symm
      exact ⟨some [], rfl, by simp [ActiveOption, EqualityNormalize.Active], fun term => by simp [empty, ConstraintIndicators.equalityValue]⟩
  | cons first rest =>
      simp only [positiveList, Bind.bind, Pure.pure, Option.bind_eq_some_iff, Option.some.injEq] at extracted
      obtain ⟨initial, head, remaining, tail, same⟩ := extracted
      subst raw
      obtain ⟨left, leftFound, leftActive, leftExact⟩ := positiveNormalized_exact first initial head
      obtain ⟨right, rightFound, rightActive, rightExact⟩ := positiveNormalizedList_exact rest remaining tail
      exact ⟨combineEqualities left right, by simp [positiveNormalizedList, leftFound, rightFound],
        combine_active left right, fun term => by rw [combine_value left right leftActive rightActive term,
          leftExact, rightExact, List.all_append]⟩
end

/-- Actual Constraint.equalities retains its EmptyConstraints fast path. -/
noncomputable def sourceEqualities (constraint : Constraint Formula) : Option (List (List Path)) :=
  match positiveNormalized constraint.guard with
  | none | some (some []) => constraint.equalities
  | some added => combineEqualities constraint.equalities added

mutual
/-- Intermediate array normalization does not change the source residual syntax test. -/
theorem positiveNormalized_support (guard : Guard Formula) :
    (positiveNormalized guard).isSome = (positive guard).isSome := by
  cases guard with
  | same left right => simp only [positiveNormalized, positive]; split <;> rfl
  | and parts => exact positiveNormalizedList_support parts
  | top | bottom | entails _ _ | satisfies _ _ | holds _ _ | substitute _ _ | not _ | or _ => rfl

/-- The source list fold succeeds exactly when every operand has positive equality syntax. -/
theorem positiveNormalizedList_support (guards : List (Guard Formula)) :
    (positiveNormalizedList guards).isSome = (positiveList guards).isSome := by
  cases guards with
  | nil => rfl
  | cons first rest =>
      have head := positiveNormalized_support first
      have tail := positiveNormalizedList_support rest
      cases a : positiveNormalized first <;> cases b : positive first <;>
        cases c : positiveNormalizedList rest <;> cases d : positiveList rest <;>
        simp_all [positiveNormalizedList, positiveList]
end

/-- Reading source equalities preserves the canonical cached-class invariant. -/
theorem sourceEqualities_active (constraint : Constraint Formula) (active : ActiveOption constraint.equalities) :
    ActiveOption (sourceEqualities constraint) := by
  unfold sourceEqualities
  split <;> first | exact active | exact combine_active _ _

/-- Staged source normalization derives the complete guard law at every positive guard. -/
theorem sourceEqualities_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (active : ActiveOption constraint.equalities)
    (positiveGuard : (positive constraint.guard).isSome = true) (term : Term (Label Formula)) :
    acceptsConstraint formulas solver constraint term =
      ConstraintIndicators.equalityValue (classTest term) (sourceEqualities constraint) := by
  obtain ⟨raw, extracted⟩ := Option.isSome_iff_exists.mp positiveGuard
  obtain ⟨added, found, addedActive, addedExact⟩ := positiveNormalized_exact (Symbol := Label Formula) constraint.guard raw extracted
  have guardValue : decide (SourceBooleanEntry.evaluateGuard formulas solver constraint.guard term = .yes) =
      ConstraintIndicators.equalityValue (classTest term) added := by
    rw [addedExact]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using positive_exact formulas solver constraint.guard raw extracted term
  unfold sourceEqualities
  rw [found]
  unfold acceptsConstraint
  rw [guardValue]
  cases added with
  | none => rw [combine_value _ _ active addedActive]
  | some classes => cases classes with
    | nil => simp [ConstraintIndicators.equalityValue]
    | cons first rest => rw [combine_value _ _ active addedActive]

/-- Readback of completed class normalization, separate from its ST representation. -/
inductive Normalized (constraint : Constraint Formula) : Option (List (List Path)) → Prop where
  | contradiction (stored : constraint.equalities = none) : Normalized constraint none
  | computed (stored added : List (List Path)) (fuel : Nat)
      (cached : constraint.equalities = some stored)
      (active : EqualityNormalize.Active stored)
      (extracted : positive constraint.guard = some added)
      (finished : EqualityNormalize.mkEqConstraints fuel (stored ++ added) ≠ .timeout) :
      Normalized constraint (SymbolicEqualityBridge.resultClasses (EqualityNormalize.mkEqConstraints fuel (stored ++ added)))
  | source (active : ActiveOption constraint.equalities)
      (positiveGuard : (positive constraint.guard).isSome = true) : Normalized constraint (sourceEqualities constraint)

/-- Normalization readback derives the compact guard predicate, rather than assuming it. -/
theorem normalized_exact [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (equalities : Option (List (List Path)))
    (readback : Normalized constraint equalities) (term : Term (Label Formula)) :
    acceptsConstraint formulas solver constraint term = ConstraintIndicators.equalityValue (classTest term) equalities := by
  cases readback with
  | contradiction stored => simp [acceptsConstraint, stored, ConstraintIndicators.equalityValue]
  | computed stored added fuel cached active extracted finished =>
      have same : constraint = ⟨some stored, constraint.guard⟩ := by cases constraint; simp_all
      rw [same]
      exact normalized_guard formulas solver stored added _ fuel active extracted finished term
  | source active positiveGuard => exact sourceEqualities_exact formulas solver constraint active positiveGuard term

example : positive (Formula := Unit) (.same [0] [0]) = none := by decide
example : parse 2 [[[0], [2]]] = none := by decide
example : deep (some [[[0], [2]]]) = false := by decide
example : deep (some [[[0], [1, 0]]]) = true := by decide

end MicroCFTA.SourceCompactGuards
