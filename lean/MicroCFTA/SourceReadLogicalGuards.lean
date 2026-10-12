import MicroCFTA.SourceReadLogicalQueries
import MicroCFTA.SourceCurrentReadBridge

/-!
# Sound logical guard judgments from planned-read cells

The proof transports each certified query as mathematical evidence. It does
not call the backend on another fresh spelling or assume equal verdicts.
The complete logical judgment retains its existing ambient sort obligations.
-/
namespace MicroCFTA.SourceReadLogicalGuards
open FullSyntax SourceFormula FormulaSubstitution SourceObservations
open SourceQuotientEnvironment SourceQuotientQueries SourceReadLogicalDomains SourceReadLogicalQueries
open SourceQuotientGuards (Logical Public)
open SourceGuards (Guard Observations Path)

/-- A nested source guard uses only its outer allocation and read context. -/
structure Included (outer inner : Guard Formula) : Prop where
  paths : ∀ path ∈ SourceGuards.paths inner, path ∈ SourceGuards.paths outer
  symbols : ∀ path ∈ SourceGuards.sensitive inner, path ∈ SourceGuards.sensitive outer
  actuals : ∀ path ∈ SourceGuards.actualPaths inner, path ∈ SourceGuards.actualPaths outer
  requirements : ∀ formula ∈ SourceGuards.requirements inner, formula ∈ SourceGuards.requirements outer

private theorem missing (guard : Guard Formula) (first second : Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (path : Path)
    (requested : path ∈ SourceGuards.paths guard) (absent : first path = none) : second path = none := by
  have equal := reads.refinements path requested
  rw [absent] at equal
  exact Option.map_eq_none_iff.mp equal.symm

private theorem present (guard : Guard Formula) (first second : Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (path : Path)
    (requested : path ∈ SourceGuards.paths guard) (value : SourceGuards.Observed Formula) (found : first path = some value) :
    ∃ other, second path = some other ∧ other.refinement = value.refinement := by
  have equal := reads.refinements path requested
  rw [found] at equal
  exact Option.map_eq_some_iff.mp equal.symm

private theorem polarized_names (guard : Guard Formula) (observed : Observations Formula)
    (requirement : Formula) (member : requirement ∈ SourceGuards.requirements guard) (positive : Bool) :
    ∀ name ∈ formulaNames (if positive then requirement else operations.negate requirement),
      name ∈ SourceSemanticNames.ambient operations observed guard := by
  cases positive <;> simpa only [Bool.false_eq_true, ↓reduceIte, operations, formulaNames] using
    (SourceScopeStack.requirement_formula_names guard observed requirement member)

private theorem polarity (positive : Bool) (verdict : Guards.Verdict) (claim : Prop)
    (support : Guards.Supports verdict claim) :
    Guards.Supports (SourceGuards.polarize positive verdict) (if positive then claim else ¬claim) := by
  cases positive <;> cases verdict <;> simp_all [SourceGuards.polarize, Guards.negate, Guards.Supports]

private theorem absence (positive : Bool) : Guards.Supports (SourceGuards.absent positive) (positive = false) := by
  cases positive <;> simp [SourceGuards.absent, Guards.Supports]

private theorem conjunction (items : List α) (evaluate : α → Guards.Verdict) (claim : α → Prop)
    (sound : ∀ item ∈ items, Guards.Supports (evaluate item) (claim item)) :
    Guards.Supports (SourceGuards.combine true (items.map evaluate)) (∀ item ∈ items, claim item) := by
  cases verdict : SourceGuards.combine true (items.map evaluate) with
  | unknown => trivial
  | yes =>
      intro item member
      have chosen := (GuardConjunction.combine_yes _).mp verdict _ (List.mem_map.mpr ⟨item, member, rfl⟩)
      simpa only [chosen, Guards.Supports] using sound item member
  | no =>
      obtain ⟨item, member, chosen⟩ := List.mem_map.mp ((GuardConjunction.combine_no _).mp verdict)
      have refuted := sound item member
      rw [chosen] at refuted
      exact fun proved => refuted (proved item member)

private theorem disjunction (items : List α) (evaluate : α → Guards.Verdict) (claim : α → Prop)
    (sound : ∀ item ∈ items, Guards.Supports (evaluate item) (claim item)) :
    Guards.Supports (SourceGuards.combine false (items.map evaluate)) (∃ item : {value // value ∈ items}, claim item.val) := by
  cases verdict : SourceGuards.combine false (items.map evaluate) with
  | unknown => trivial
  | yes =>
      obtain ⟨item, member, chosen⟩ := List.mem_map.mp ((GuardConjunction.disjoin_yes _).mp verdict)
      have proved := sound item member
      rw [chosen] at proved
      exact ⟨⟨item, member⟩, proved⟩
  | no =>
      rintro ⟨⟨item, member⟩, proved⟩
      have chosen := (GuardConjunction.disjoin_no _).mp verdict _ (List.mem_map.mpr ⟨item, member, rfl⟩)
      have refuted := sound item member
      rw [chosen] at refuted
      exact refuted proved

/-- Current scoped evaluation supports the complete logical judgment without backend spelling stability. -/
theorem worker_supports (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula)) (outer : Guard Formula)
    (cell : Observations Formula) (reads : SourceReadAgreement.Reads outer cell (observe term))
    (compatible : Compatible sortDomain outer cell (observe term))
    (sound : SourceEntailment.Sound model (Admitted sortDomain cell outer) solver)
    (recipes : List Recipe) (old middle complete : List Scope) (stack : Stack term outer cell recipes old middle complete)
    (positive : Bool) (inner : Guard Formula) (included : Included outer inner) :
    Guards.Supports (SourceCurrentReadBridge.evaluate solver outer cell old positive inner)
      (Logical model sortDomain term outer complete positive inner) := by
  cases inner with
  | top | bottom => cases positive <;> simp [SourceCurrentReadBridge.evaluate, SourceSubstitutionPrecedence.evaluateWith,
      SourceEnclosingRenames.evaluateWith, SourceGuards.polarize, Guards.negate, Logical, Guards.Supports]
  | same left right =>
      have leftRead := reads.symbols left (included.symbols left (by simp [SourceGuards.sensitive]))
      have rightRead := reads.symbols right (included.symbols right (by simp [SourceGuards.sensitive]))
      simp only [SourceCurrentReadBridge.evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, Logical]
      cases leftFound : cell left with
      | none => simpa only [← leftRead, leftFound] using absence positive
      | some a => cases rightFound : cell right with
        | none => simpa only [← leftRead, ← rightRead, leftFound, rightFound] using absence positive
        | some b =>
            simp only [← leftRead, ← rightRead, leftFound, rightFound]
            by_cases equal : left = right
            · subst right
              obtain ⟨subterm, found, _⟩ := Option.map_eq_some_iff.mp (leftRead.symm.trans leftFound)
              have reflexive := (Language.termEq_correct (renameTree operations complete subterm) _).mpr rfl
              cases positive <;> simp [sameTerm, found, reflexive, SourceGuards.polarize, Guards.negate, Guards.Supports]
            · simp only [equal, ↓reduceIte]
              cases decided : sameShape operations cell old left right with
              | none => cases positive <;> simp [SourceGuards.polarize, Guards.negate, Guards.Supports]
              | some answer =>
                  have same := SourceScopeSymbols.same outer cell (observe term) reads recipes old middle stack.source stack.observed
                    left right (included.symbols left (by simp [SourceGuards.sensitive]))
                    (included.symbols right (by simp [SourceGuards.sensitive]))
                  have full := SourceQuotientGuards.same_sound model term outer recipes middle complete stack.sparse stack.full
                    left right answer (same.symm.trans decided)
                  cases positive <;> cases answer <;> simp [full, SourceGuards.polarize, Guards.negate, Guards.Supports]
  | entails left right =>
      have leftRequested := included.paths left (by simp [SourceGuards.paths])
      have rightRequested := included.paths right (by simp [SourceGuards.paths])
      simp only [SourceCurrentReadBridge.evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, Logical]
      cases leftFound : cell left with
      | none => simpa only [leftFound, missing outer cell (observe term) reads left leftRequested leftFound] using absence positive
      | some a =>
          obtain ⟨otherA, otherLeft, sameA⟩ := present outer cell (observe term) reads left leftRequested a leftFound
          cases rightFound : cell right with
          | none => simpa only [leftFound, otherLeft, rightFound,
              missing outer cell (observe term) reads right rightRequested rightFound] using absence positive
          | some b =>
              obtain ⟨otherB, otherRight, sameB⟩ := present outer cell (observe term) reads right rightRequested b rightFound
              simp only [otherLeft, otherRight, sameA, sameB]
              apply polarity
              exact ordinary model nullary laws sortDomain solver term outer cell reads compatible sound recipes old middle complete stack
                a.refinement b.refinement (SourceScopeStack.observed_formula_names outer cell left a leftRequested leftFound)
                (SourceScopeStack.observed_formula_names outer cell right b rightRequested rightFound)
  | satisfies target requirement =>
      have requested := included.paths target (by simp [SourceGuards.paths])
      simp only [SourceCurrentReadBridge.evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, Logical]
      cases found : cell target with
      | none => simpa only [found, missing outer cell (observe term) reads target requested found] using absence positive
      | some value =>
          obtain ⟨other, otherFound, same⟩ := present outer cell (observe term) reads target requested value found
          simp only [otherFound, same]
          exact ordinary model nullary laws sortDomain solver term outer cell reads compatible sound recipes old middle complete stack
            value.refinement _ (SourceScopeStack.observed_formula_names outer cell target value requested found)
            (polarized_names outer cell requirement (included.requirements requirement (by simp [SourceGuards.requirements])) positive)
  | holds targets requirement =>
      have requested : ∀ path ∈ targets, path ∈ SourceGuards.paths outer := by simpa only [SourceGuards.paths] using included.paths
      have same := SourceReadAgreement.observeMany_refinements cell (observe term) targets
        (fun path member => reads.refinements path (requested path member))
      simp only [SourceCurrentReadBridge.evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, Logical]
      cases found : SourceGuards.observeMany cell targets with
      | none =>
          rw [found] at same
          have otherMissing := Option.map_eq_none_iff.mp same.symm
          simpa only [found, otherMissing] using absence positive
      | some values =>
          rw [found] at same
          obtain ⟨otherValues, otherFound, _⟩ := Option.map_eq_some_iff.mp same.symm
          simp only [otherFound]
          exact SourceReadLogicalQueries.holds model nullary laws sortDomain solver term outer cell reads compatible sound
            recipes old middle complete stack targets requested values otherValues found otherFound _
            (polarized_names outer cell requirement (included.requirements requirement (by simp [SourceGuards.requirements])) positive)
  | substitute additions inner =>
      have requestedRead : SourceScopeStack.Requested outer additions := by
        intro entry member
        exact ⟨included.symbols entry.actual (by simp [SourceGuards.sensitive]; exact Or.inl ⟨entry, member, by simp⟩),
          included.symbols entry.formal (by simp [SourceGuards.sensitive]; exact Or.inl ⟨entry, member, by simp⟩)⟩
      have requestedActual : Requested outer additions := by
        intro entry member
        exact ⟨included.actuals entry.actual (by simp only [SourceGuards.actualPaths, List.mem_append, List.mem_map]; exact Or.inl ⟨entry, member, rfl⟩),
          included.paths entry.formal (by simp [SourceGuards.paths]; exact Or.inl ⟨entry, member, by simp⟩)⟩
      have inside : Included outer inner := ⟨fun path member => included.paths path (by simp [SourceGuards.paths, member]),
        fun path member => included.symbols path (by simp [SourceGuards.sensitive, member]),
        fun path member => included.actuals path (by simp [SourceGuards.actualPaths, member]),
        (by simpa only [SourceGuards.requirements] using included.requirements)⟩
      have related := SourceResolvedTables.resolveMany_aligned operations outer cell (observe term) reads additions requestedRead
      change SourceResolvedTables.OptionRel _ (SourceScopeStack.resolve outer cell additions)
        (SourceScopeStack.resolve outer (observe term) additions) at related
      simp only [SourceCurrentReadBridge.evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, Logical]
      cases found : SourceScopeStack.resolve outer cell additions with
      | none =>
          have middleMissing : resolve term outer (sameShape operations (observe term) []) additions = none := by
            cases other : SourceScopeStack.resolve outer (observe term) additions with
            | none => exact other
            | some scope => simp [found, other, SourceResolvedTables.OptionRel] at related
          have fullMissing : resolve term outer (sameTerm operations term []) additions = none := by
            cases full : resolve term outer (sameTerm operations term []) additions with
            | none => rfl
            | some scope =>
                obtain ⟨oldScope, impossible⟩ := resolve_exists term outer _ (sameShape operations (observe term) []) additions scope full
                simp [middleMissing] at impossible
          unfold SourceScopeStack.resolve at found
          simpa only [found, fullMissing] using absence positive
      | some scope =>
          cases middleFound : SourceScopeStack.resolve outer (observe term) additions with
          | none => simp [found, middleFound, SourceResolvedTables.OptionRel] at related
          | some middleScope =>
              have paired : Language.All₂ (SourceResolvedTables.Aligned (SourceFreshTables.tableRenaming operations outer cell (observe term)))
                  scope middleScope := by simpa only [found, middleFound, SourceResolvedTables.OptionRel] using related
              have sparseFound : resolve term outer (sameShape operations (observe term) []) additions = some middleScope := middleFound
              obtain ⟨completeScope, completeFound⟩ := resolve_exists term outer _ (sameTerm operations term []) additions middleScope sparseFound
              have rawFound := found
              unfold SourceScopeStack.resolve at rawFound
              simp only [rawFound, completeFound]
              cases pass : scope.any (SourceEnclosingRenames.renamedByEnclosing old) ||
                  SourceSubstitutionPrecedence.ambiguousIdentityPrecedence scope with
              | true => simp [Guards.Supports]
              | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  have policies := SourceCurrentReadTransport.checks _ scope middleScope old middle paired
                    (SourceScopeSymbols.aligned outer cell (observe term) reads recipes old middle stack.source stack.observed)
                  exact worker_supports model nullary laws sortDomain solver term outer cell reads compatible sound
                    (additions :: recipes) (scope :: old) (middleScope :: middle) (completeScope :: complete)
                    ⟨.cons ⟨found, requestedRead⟩ stack.source, .cons ⟨middleFound, requestedRead⟩ stack.observed,
                      .cons ⟨sparseFound, requestedActual⟩ stack.sparse, .cons ⟨completeFound, requestedActual⟩ stack.full,
                      accepted_cons middleScope middle stack.accepted (policies.symm.trans pass)⟩ positive inner inside
  | not inner =>
      have inside : Included outer inner := ⟨by simpa only [SourceGuards.paths] using included.paths,
        by simpa only [SourceGuards.sensitive] using included.symbols,
        by simpa only [SourceGuards.actualPaths] using included.actuals,
        by simpa only [SourceGuards.requirements] using included.requirements⟩
      simpa only [SourceCurrentReadBridge.evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, Logical] using
        worker_supports model nullary laws sortDomain solver term outer cell reads compatible sound recipes old middle complete stack (!positive) inner inside
  | and parts | or parts =>
      have inside (part : Guard Formula) (member : part ∈ parts) : Included outer part :=
        ⟨fun path present => included.paths path (by simpa only [SourceGuards.paths] using List.mem_flatMap.mpr ⟨part, member, present⟩),
          fun path present => included.symbols path (by simpa only [SourceGuards.sensitive] using List.mem_flatMap.mpr ⟨part, member, present⟩),
          fun path present => included.actuals path (by simpa only [SourceGuards.actualPaths] using List.mem_flatMap.mpr ⟨part, member, present⟩),
          fun formula present => included.requirements formula (by simpa only [SourceGuards.requirements] using List.mem_flatMap.mpr ⟨part, member, present⟩)⟩
      simp only [SourceCurrentReadBridge.evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, Logical]
      cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals first
        | (apply conjunction; intro part member
           exact worker_supports model nullary laws sortDomain solver term outer cell reads compatible sound recipes old middle complete stack _ part (inside part member))
        | (apply disjunction; intro part member
           exact worker_supports model nullary laws sortDomain solver term outer cell reads compatible sound recipes old middle complete stack _ part (inside part member))
termination_by sizeOf inner

/-- The public dispatcher allocates one table for each listed scoped guard. -/
def contexts : Guard Formula → List (Guard Formula)
  | .and parts | .or parts => parts.flatMap contexts
  | .not inner | .substitute [] inner => contexts inner
  | guard => [guard]

/-- The public planned-read evaluator supports complete logical validity without exact verdict stability. -/
theorem public_supports (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (cell : Observations Formula) (reads : SourceReadAgreement.Reads guard cell (observe term))
    (compatible : ∀ context ∈ contexts guard, Compatible sortDomain context cell (observe term))
    (sound : ∀ context ∈ contexts guard, SourceEntailment.Sound model (Admitted sortDomain cell context) solver)
    (positive : Bool) :
    Guards.Supports (SourceSubstitutionPrecedence.evaluate operations solver cell (sameShape operations cell) positive guard)
      (Public model sortDomain term positive guard) := by
  cases guard with
  | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ =>
      simp only [SourceSubstitutionPrecedence.evaluate, Public]
      exact worker_supports model nullary laws sortDomain solver term _ cell reads (compatible _ (by simp [contexts]))
        (sound _ (by simp [contexts])) [] [] [] [] (empty_stack term _ cell) positive _
        ⟨fun _ member => member, fun _ member => member, fun _ member => member, fun _ member => member⟩
  | substitute additions inner =>
      cases additions with
      | nil =>
          simp only [SourceSubstitutionPrecedence.evaluate, Public]
          exact public_supports model nullary laws sortDomain solver term inner cell
            (SourceReadAgreement.restrict _ inner cell (observe term) reads (by simp [SourceGuards.paths]) (by simp [SourceGuards.sensitive]))
            (by simpa only [contexts] using compatible) (by simpa only [contexts] using sound) positive
      | cons first rest =>
          simp only [SourceSubstitutionPrecedence.evaluate, Public]
          exact worker_supports model nullary laws sortDomain solver term _ cell reads (compatible _ (by simp [contexts]))
            (sound _ (by simp [contexts])) [] [] [] [] (empty_stack term _ cell) positive _
            ⟨fun _ member => member, fun _ member => member, fun _ member => member, fun _ member => member⟩
  | not inner =>
      simp only [SourceSubstitutionPrecedence.evaluate, Public]
      exact public_supports model nullary laws sortDomain solver term inner cell
        (SourceReadAgreement.restrict _ inner cell (observe term) reads (by simp [SourceGuards.paths]) (by simp [SourceGuards.sensitive]))
        (by simpa only [contexts] using compatible) (by simpa only [contexts] using sound) (!positive)
  | and parts | or parts =>
      simp only [SourceSubstitutionPrecedence.evaluate, Public]
      cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals first
        | apply conjunction
        | apply disjunction
      all_goals
        intro part member
        exact public_supports model nullary laws sortDomain solver term part cell
          (SourceReadAgreement.restrict _ part cell (observe term) reads
            (fun path present => by simpa only [SourceGuards.paths] using List.mem_flatMap.mpr ⟨part, member, present⟩)
            (fun path present => by simpa only [SourceGuards.sensitive] using List.mem_flatMap.mpr ⟨part, member, present⟩))
          (fun context present => compatible context (by simpa only [contexts] using List.mem_flatMap.mpr ⟨part, member, present⟩))
          (fun context present => sound context (by simpa only [contexts] using List.mem_flatMap.mpr ⟨part, member, present⟩)) _
termination_by sizeOf guard

/-- In an all-integer environment, the additional ambient-domain condition is automatic. -/
theorem integer_supports (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (cell : Observations Formula) (reads : SourceReadAgreement.Reads guard cell (observe term))
    (sound : SourceEntailment.Sound integerModel (fun _ _ => True) solver) (positive : Bool) :
    Guards.Supports (SourceSubstitutionPrecedence.evaluate operations solver cell (sameShape operations cell) positive guard)
      (Public integerModel (fun _ _ => True) term positive guard) := by
  apply public_supports integerModel (by intro value; rfl)
    (by constructor <;> intros <;> simp_all [integerModel, CoreFormula.evalRelation]) (fun _ _ => True)
    solver term guard cell reads (fun context _ => integer_compatible context cell (observe term))
  intro context member declarations antecedent consequent
  have support := sound declarations antecedent consequent
  cases result : solver declarations antecedent consequent with
  | unknown => trivial
  | yes =>
      rw [result] at support
      exact fun env _ assumed => support env trivial assumed
  | no =>
      rw [result] at support
      exact fun proved => support (fun env _ assumed => proved env ⟨fun _ _ => trivial, fun _ _ => trivial⟩ assumed)

end MicroCFTA.SourceReadLogicalGuards
