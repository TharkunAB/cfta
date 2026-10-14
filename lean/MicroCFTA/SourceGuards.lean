import MicroCFTA.Guards
import MicroCFTA.Language

/-!
# Complete source guard syntax and actual-value allocation

Formula operations are an explicit interface. Guard traversal, observations,
actual identity grouping, fresh-name allocation, and ambiguity tracking follow
`Refinement.Evaluate`. Formula substitution is verified separately.
`evaluateWith` retains the worker before `d6b8837` for regression witnesses.
`SourceEnclosingRenames` adds the current enclosing-renaming check.
-/
namespace MicroCFTA.SourceGuards
open Guards
abbrev Path := List Nat
abbrev Name := String

/-- The source records leaf, inner, or mixed groups in this declaration order. -/
inductive Leafness where
  | mixed | inner | leaf
  deriving DecidableEq, Repr

/-- A complete root observation, including the constructor name and its refinement. -/
structure Observed (Formula : Type) where
  name : Name
  refinement : Formula
  leafness : Leafness
  deriving DecidableEq, Repr

/-- One actual-for-formal position substitution. -/
structure Substitution where
  actual : Path
  formal : Path
  deriving DecidableEq, Repr

/-- Every source guard constructor, including list connectives and nested substitutions. -/
inductive Guard (Formula : Type) where
  | top | bottom
  | same (left right : Path)
  | entails (antecedent consequent : Path)
  | satisfies (target : Path) (requirement : Formula)
  | holds (targets : List Path) (formula : Formula)
  | substitute (additions : List Substitution) (inner : Guard Formula)
  | not (inner : Guard Formula)
  | and (parts : List (Guard Formula))
  | or (parts : List (Guard Formula))
  deriving Repr

/-- Formula and name operations used by the complete evaluator. -/
structure Formulas (Formula : Type) where
  substitute : List (Name × Name) → Formula → Formula
  negate : Formula → Formula
  conjunction : List Formula → Formula
  equalNames : Name → Name → Formula
  freeNames : Formula → List Name

/-- A path observer can omit positions that the candidate term does not have. -/
abbrev Observations (Formula : Type) := Path → Option (Observed Formula)

/-- First-occurrence lists represent the path sets collected from a guard. -/
def paths : Guard Formula → List Path
  | .top | .bottom => []
  | .same left right | .entails left right => [left, right]
  | .satisfies target _ => [target]
  | .holds targets _ => targets
  | .substitute additions inner => additions.flatMap (fun s => [s.actual, s.formal]) ++ paths inner
  | .not inner => paths inner
  | .and parts | .or parts => parts.flatMap paths

/-- Substitution positions and structural comparisons require complete symbol observations. -/
def sensitive : Guard Formula → List Path
  | .same left right => [left, right]
  | .substitute additions inner => additions.flatMap (fun s => [s.actual, s.formal]) ++ sensitive inner
  | .not inner => sensitive inner
  | .and parts | .or parts => parts.flatMap sensitive
  | _ => []

/-- Actual positions are gathered through every Boolean and substitution scope. -/
def actualPaths : Guard Formula → List Path
  | .substitute additions inner => additions.map Substitution.actual ++ actualPaths inner
  | .not inner => actualPaths inner
  | .and parts | .or parts => parts.flatMap actualPaths
  | _ => []

/-- Literal requirement formulas contribute their free names to the fresh-name avoid set. -/
def requirements : Guard Formula → List Formula
  | .satisfies _ formula | .holds _ formula => [formula]
  | .substitute _ inner | .not inner => requirements inner
  | .and parts | .or parts => parts.flatMap requirements
  | _ => []

/-- The source ascending path-set order, without duplicates. -/
def orderedPaths (paths : List Path) : List Path :=
  paths.eraseDups.mergeSort (fun left right => compare left right != .gt)

/-- One actual path and the full root identity read there. -/
structure Actual (Formula : Type) where
  target : Path
  name : Name
  refinement : Formula
  deriving DecidableEq, Repr

/-- Keep precisely the actual positions that exist in the observed candidate. -/
def actuals (observed : Observations Formula) (guard : Guard Formula) : List (Actual Formula) :=
  (orderedPaths (actualPaths guard)).filterMap fun target =>
    (observed target).map (fun value => ⟨target, value.name, value.refinement⟩)

/-- Choose the first equal actual identity, including the source's equal named-leaf rule. -/
def representative [DecidableEq Formula] (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (values : List (Actual Formula)) (actual : Actual Formula) : Path :=
  match values.find? (fun other =>
    decide (other.name = actual.name) && decide (other.refinement = actual.refinement) &&
      (decide (sameAt actual.target other.target = some true) ||
        (decide ((observed actual.target).map Observed.leafness = some .leaf) &&
         decide ((observed other.target).map Observed.leafness = some .leaf)))) with
  | some canonical => canonical.target
  | none => actual.target

/-- One representative and ambient name for each distinct actual identity. -/
def values [DecidableEq Formula] (observed : Observations Formula) (sameAt : Path → Path → Option Bool)
    (guard : Guard Formula) : List (Path × Name) :=
  let entries := actuals observed guard
  (entries.map (fun actual => (representative observed sameAt entries actual, actual.name))).eraseDups

/-- Distinct actual identities with the same ambient name need distinct solver names. -/
def conflicts [DecidableEq Formula] (observed : Observations Formula) (sameAt : Path → Path → Option Bool)
    (guard : Guard Formula) : List (Path × Name) :=
  let entries := values observed sameAt guard
  entries.filter (fun entry => 1 < entries.countP (fun other => decide (other.2 = entry.2)))

/-- Allocate from the source stream beginning at `__cfta_actual_0`. -/
def freshNames (avoid : List Name) (count : Nat) : List Name :=
  (((List.range (avoid.length + count)).map (fun index => "__cfta_actual_" ++ toString index)).filter
    (fun candidate => !avoid.contains candidate)).take count

/-- Every observed symbol name and refinement free name is unavailable for fresh identities. -/
def usedNames (formulas : Formulas Formula) (observed : Observations Formula) (guard : Guard Formula) : List Name :=
  ((orderedPaths (paths guard)).flatMap fun target =>
    match observed target with
    | none => []
    | some value => value.name :: formulas.freeNames value.refinement) ++
  (requirements guard).flatMap formulas.freeNames

/-- Allocate one fresh declaration for each conflicting actual representative. -/
def allocated [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (guard : Guard Formula) : List (Path × (Name × Name)) :=
  let conflicting := conflicts observed sameAt guard
  (conflicting.zip (freshNames (usedNames formulas observed guard) conflicting.length)).map
    (fun (entry, fresh) => (entry.1, fresh, entry.2))

/-- A collision remains ambiguous when complete identity is unknown and the two observations are not both leaves. -/
def ambiguous [DecidableEq Formula] (observed : Observations Formula) (sameAt : Path → Path → Option Bool)
    (guard : Guard Formula) : List Path :=
  let entries := actuals observed guard
  ((entries.filter (fun actual => entries.any (fun other =>
    decide (actual.target ≠ other.target) && decide (actual.name = other.name) &&
    decide (actual.refinement = other.refinement) && decide (sameAt actual.target other.target = none) &&
    (decide ((observed actual.target).map Observed.leafness ≠ some .leaf) ||
      decide ((observed other.target).map Observed.leafness ≠ some .leaf))))).map Actual.target).eraseDups

/-- The source fresh-value and ambiguity tables used by every nested substitution scope. -/
def substitutionValues [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (guard : Guard Formula) : List (Path × (Name × Name)) × List Path :=
  let entries := actuals observed guard
  let declarations := allocated formulas observed sameAt guard
  ((entries.filterMap (fun actual =>
    (declarations.lookup (representative observed sameAt entries actual)).map (fun binding => (actual.target, binding)))),
    ambiguous observed sameAt guard)

/-- A resolved source scope retains logical names, literal symbol names, and actual assumptions separately. -/
structure Resolved (Formula : Type) where
  replacement : Name × Name
  symbolReplacement : Name × Name
  actualAssumption : Formula
  declaration : Option (Name × Name)
  identityKnown : Bool
  deriving Repr

/-- The source's reserved refinement value name. -/
def valueName : Name := "__cfta_value"

/-- Resolve a simultaneous substitution only when both actual and formal positions exist. -/
def resolve (formulas : Formulas Formula) (observed : Observations Formula)
    (fresh : List (Path × (Name × Name))) (unknown : List Path) (substitution : Substitution) : Option (Resolved Formula) := do
  let actual ← observed substitution.actual
  let formal ← observed substitution.formal
  let declaration := fresh.lookup substitution.actual
  let actualName := (declaration.map Prod.fst).getD actual.name
  pure ⟨(formal.name, actualName), (formal.name, actual.name),
    formulas.substitute [(valueName, actualName)] actual.refinement,
    declaration, !unknown.contains substitution.actual⟩

/-- Apply simultaneous scopes from innermost to outermost. -/
def applySubstitutions (formulas : Formulas Formula) (scopes : List (List (Resolved Formula))) (formula : Formula) : Formula :=
  scopes.foldl (fun formula scope => formulas.substitute (scope.map Resolved.replacement) formula) formula

/-- Actual refinements remain ambient assumptions and are not renamed by later guard scopes. -/
def withActualAssumptions (formulas : Formulas Formula) (scopes : List (List (Resolved Formula))) (formula : Formula) : Formula :=
  formulas.conjunction ((scopes.flatten.map Resolved.actualAssumption) ++ [formula])

/-- A scoped solver query keeps its declarations explicit. -/
abbrev Entailment (Formula : Type) := List (Name × Name) → Formula → Formula → Verdict

/-- A refutation under an unknown actual identity must remain Unknown. -/
def decideWith (solver : Entailment Formula) (bindings : List (Name × Name)) (scopes : List (List (Resolved Formula)))
    (antecedent consequent : Formula) : Verdict :=
  let declarations := bindings ++ scopes.flatten.filterMap Resolved.declaration
  match solver declarations.eraseDups antecedent consequent with
  | .no => if scopes.all (fun scope => scope.all Resolved.identityKnown) then .no else .unknown
  | result => result

/-- The sparse identity safeguard cannot produce No while a scope contains an unknown identity. -/
theorem ambiguous_never_no (solver : Entailment Formula) (bindings : List (Name × Name))
    (scopes : List (List (Resolved Formula))) (antecedent consequent : Formula)
    (ambiguous : scopes.all (fun scope => scope.all Resolved.identityKnown) = false) :
    decideWith solver bindings scopes antecedent consequent ≠ .no := by
  unfold decideWith
  cases found : solver (bindings ++ scopes.flatten.filterMap Resolved.declaration).eraseDups antecedent consequent <;>
    simp only [found, ambiguous, Bool.false_eq_true, ↓reduceIte, ne_eq] <;> decide

/-- Known identities leave all three solver verdicts unchanged. -/
theorem known_query (solver : Entailment Formula) (bindings : List (Name × Name))
    (scopes : List (List (Resolved Formula))) (antecedent consequent : Formula)
    (known : scopes.all (fun scope => scope.all Resolved.identityKnown) = true) :
    decideWith solver bindings scopes antecedent consequent =
      solver (bindings ++ scopes.flatten.filterMap Resolved.declaration).eraseDups antecedent consequent := by
  unfold decideWith
  cases found : solver (bindings ++ scopes.flatten.filterMap Resolved.declaration).eraseDups antecedent consequent <;>
    simp only [found, known, ↓reduceIte]


/-- Read every requested value in order, failing when one path is absent. -/
def observeMany (observed : Observations Formula) : List Path → Option (List (Observed Formula))
  | [] => some []
  | target :: rest => do return (← observed target) :: (← observeMany observed rest)

/-- Resolve every actual/formal pair in one simultaneous scope, in source order. -/
def resolveMany (formulas : Formulas Formula) (observed : Observations Formula)
    (fresh : List (Path × (Name × Name))) (unknown : List Path) : List Substitution → Option (List (Resolved Formula))
  | [] => some []
  | first :: rest => do return (← resolve formulas observed fresh unknown first) :: (← resolveMany formulas observed fresh unknown rest)

/-- The reserved name for one positional term in a relational contract. -/
def contractName (index : Nat) : Name := "__cfta_contract_" ++ toString index

/-- A relational contract has one formal per target and aliases repeated target paths. -/
def contract (formulas : Formulas Formula) (targets : List Path) (observations : List (Observed Formula)) :
    List Name × Formula :=
  let formals := (List.range targets.length).map contractName
  let firstNames := targets.zip formals
  let aliases := firstNames.filterMap (fun (target, formal) => do
    let first ← firstNames.lookup target
    if first = formal then none else some (formulas.equalNames formal first))
  (formals, formulas.conjunction
    ((formals.zip observations).map (fun (formal, value) =>
      formulas.substitute [(valueName, formal)] value.refinement) ++ aliases))

/-- The source converts a missing path to No; negation of that guard succeeds. -/
def absent (positive : Bool) : Verdict := if positive then .no else .yes

/-- Ordinary syntactic and entailment negation complements the completed three-way result. -/
def polarize (positive : Bool) (verdict : Verdict) : Verdict := if positive then verdict else Guards.negate verdict

/-- Conjunction and disjunction preserve Unknown unless a decisive result short-circuits. -/
def combine (conjunctive : Bool) : List Verdict → Verdict
  | [] => if conjunctive then .yes else .no
  | result :: rest =>
      if conjunctive then
        if result = .no then .no else Guards.conjunction result (combine conjunctive rest)
      else if result = .yes then .yes else Guards.disjunction result (combine conjunctive rest)

/-- Evaluate all source constructors. Polarity executes the source's pushed negation cases directly. -/
def evaluateWith (formulas : Formulas Formula) (solver : Entailment Formula) (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (fresh : List (Path × (Name × Name))) (unknown : List Path)
    (scopes : List (List (Resolved Formula))) (positive : Bool) : Guard Formula → Verdict
  | .top => polarize positive .yes
  | .bottom => polarize positive .no
  | .same left right =>
      match observed left, observed right with
      | some _, some _ => polarize positive (if left = right then .yes else
          match sameAt scopes left right with | some true => .yes | some false => .no | none => .unknown)
      | _, _ => absent positive
  | .entails left right =>
      match observed left, observed right with
      | some antecedent, some consequent => polarize positive
          (decideWith solver [] scopes
            (withActualAssumptions formulas scopes (applySubstitutions formulas scopes antecedent.refinement))
            (applySubstitutions formulas scopes consequent.refinement))
      | _, _ => absent positive
  | .satisfies target requirement =>
      match observed target with
      | some value => decideWith solver [] scopes
          (withActualAssumptions formulas scopes (applySubstitutions formulas scopes value.refinement))
          (applySubstitutions formulas scopes (if positive then requirement else formulas.negate requirement))
      | none => absent positive
  | .holds targets requirement =>
      match observeMany observed targets with
      | some values =>
          let prepared := contract formulas targets values
          decideWith solver (prepared.1.map (fun name => (name, valueName))) scopes
            (withActualAssumptions formulas scopes (applySubstitutions formulas scopes prepared.2))
            (applySubstitutions formulas scopes (if positive then requirement else formulas.negate requirement))
      | none => absent positive
  | .substitute additions inner =>
      match resolveMany formulas observed fresh unknown additions with
      | some resolved => evaluateWith formulas solver observed sameAt fresh unknown (resolved :: scopes) positive inner
      | none => absent positive
  | .not inner => evaluateWith formulas solver observed sameAt fresh unknown scopes (!positive) inner
  | .and parts => combine positive (parts.map (evaluateWith formulas solver observed sameAt fresh unknown scopes positive))
  | .or parts => combine (!positive) (parts.map (evaluateWith formulas solver observed sameAt fresh unknown scopes positive))

/-- The common source entry point computes actual identities once for the entire guard. -/
def evaluateGuardWithSame [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (observed : Observations Formula) (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (guard : Guard Formula) : Verdict :=
  let identities := substitutionValues formulas observed (sameAt []) guard
  evaluateWith formulas solver observed sameAt identities.1 identities.2 [] true guard

/-- Duplicate contract paths always use the first positional name in the alias table. -/
theorem contract_first_name (targets : List Path) (target : Path) (formal : Name)
    (found : (targets.zip ((List.range targets.length).map contractName)).lookup target = some formal) :
    (target, formal) ∈ targets.zip ((List.range targets.length).map contractName) := by
  obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp found
  rw [same]
  simp

/-- Negating a condition negates its formula instead of treating failed entailment as refutation. -/
theorem negative_condition (formulas : Formulas Formula) (solver : Entailment Formula) (observed : Observations Formula)
    (sameAt : List (List (Resolved Formula)) → Path → Path → Option Bool)
    (fresh : List (Path × (Name × Name))) (unknown : List Path) (scopes : List (List (Resolved Formula)))
    (target : Path) (requirement : Formula) :
    evaluateWith formulas solver observed sameAt fresh unknown scopes true (.not (.satisfies target requirement)) =
      evaluateWith formulas solver observed sameAt fresh unknown scopes false (.satisfies target requirement) := by
  simp [evaluateWith]

end MicroCFTA.SourceGuards
