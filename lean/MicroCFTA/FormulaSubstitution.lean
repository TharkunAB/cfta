import MicroCFTA.FormulaSemantics

/-!
# Checked simultaneous substitution

This module follows the repaired `Formula.substituteChecked`. Applications
with no arguments are named values. A nonempty application can rename its
head to another name. Other replacements at that head produce an error
after the arguments have succeeded. An argument error takes precedence.
The historical algorithm and its counterexample remain in `FullSyntax`.
-/

namespace MicroCFTA.FormulaSubstitution

open FullSyntax

attribute [local simp] LatticeLinear.except_bind_ok LatticeLinear.except_bind_error
  LatticeLinear.except_map_ok LatticeLinear.except_map_error

/-- A replacement that cannot be expressed by a named application head. -/
inductive Error where
  | unsupportedFunction (name : Name) (replacement : Term)
  deriving Repr

/-- Remove names already encountered by the left-to-right `nub` traversal. -/
def uniqueNamesFrom (seen : List Name) : List Name → List Name
  | [] => []
  | name :: rest => if seen.contains name then uniqueNamesFrom seen rest
      else name :: uniqueNamesFrom (name :: seen) rest

/-- Retain the first occurrence of each name, as `Data.List.nub` does. -/
def uniqueNames := uniqueNamesFrom []

/-- Read a finite name renaming, with identity outside its domain. -/
def renameName (renamed : List (Name × Name)) (name : Name) : Name :=
  match renamed with
  | [] => name
  | (old, fresh) :: rest => if name = old then fresh else renameName rest name

/-- Prepare the actual fresh binder names and the active simultaneous substitution. -/
def prepare (active : List (Name × Term)) (bound : List (Name × ValueSort))
    (bodyNames : List Name) : List (Name × ValueSort) × List (Name × Term) :=
  let kept := active.filter fun entry => !(bound.map Prod.fst).contains entry.1
  let captured := kept.flatMap fun entry => termNames entry.2
  let avoid := captured ++ bodyNames ++ bound.map Prod.fst ++ kept.map Prod.fst
  let names := (uniqueNames (bound.map Prod.fst)).filter captured.contains
  let renamed := names.zip (freshNames avoid names.length)
  (bound.map (fun (name, sort) => (renameName renamed name, sort)),
    renamed.map (fun (name, fresh) => (name, Term.var fresh)) ++ kept)

mutual
/-- Simultaneous term substitution with explicit rejection of non-name function replacements. -/
def term (active : List (Name × Term)) : Term → Except Error Term
  | .lit n => .ok (.lit n)
  | .var name => .ok ((lookup name active).getD (.var name))
  | .app name [] => .ok ((lookup name active).getD (.app name []))
  | .app name (argument :: rest) =>
      match lookup name active with
      | none => (.app name) <$> arguments active (argument :: rest)
      | some (.var renamed) => (.app renamed) <$> arguments active (argument :: rest)
      | some replacement => do
          let _ ← arguments active (argument :: rest)
          .error (.unsupportedFunction name replacement)
  | .neg t => Term.neg <$> term active t
  | .add t u => return .add (← term active t) (← term active u)
  | .sub t u => return .sub (← term active t) (← term active u)
  | .mul t u => return .mul (← term active t) (← term active u)
  | .div t u => return .div (← term active t) (← term active u)
  | .mod t u => return .mod (← term active t) (← term active u)
  | .ite p t u => return .ite (← formula active p) (← term active t) (← term active u)
  | .cast t sort => (fun replaced => Term.cast replaced sort) <$> term active t
termination_by t => sizeOf t

/-- Traverse arguments in source order and retain the first failure. -/
def arguments (active : List (Name × Term)) : List Term → Except Error (List Term)
  | [] => .ok []
  | t :: ts => return (← term active t) :: (← arguments active ts)
termination_by ts => sizeOf ts

/-- Substitute every formula constructor, including both kinds of sorted quantifier. -/
def formula (active : List (Name × Term)) : Formula → Except Error Formula
  | .top => .ok .top
  | .bottom => .ok .bottom
  | .and ps => Formula.and <$> parts active ps
  | .or ps => Formula.or <$> parts active ps
  | .not p => Formula.not <$> formula active p
  | .atom r t u => return .atom r (← term active t) (← term active u)
  | .forall bound p =>
      let (renamed, nested) := prepare active bound (formulaNames p)
      Formula.forall renamed <$> formula nested p
  | .exists bound p =>
      let (renamed, nested) := prepare active bound (formulaNames p)
      Formula.exists renamed <$> formula nested p
termination_by p => sizeOf p

/-- Traverse Boolean parts in source order and retain the first failure. -/
def parts (active : List (Name × Term)) : List Formula → Except Error (List Formula)
  | [] => .ok []
  | p :: ps => return (← formula active p) :: (← parts active ps)
termination_by ps => sizeOf ps
end

/-- Ignore identity entries once before the checked simultaneous traversal. -/
def checked (replacements : List (Name × Term)) (p : Formula) : Except Error Formula :=
  formula (replacements.filter fun entry => !identityReplacement entry) p

/-- Unsupported higher-order replacement fails explicitly at a nonempty named application. -/
theorem function_replacement_rejected (active : List (Name × Term)) (name : Name)
    (argument : Term) (rest : List Term) (replacement : Term)
    (found : lookup name active = some replacement) (nonName : ∀ other, replacement ≠ .var other)
    (replaced : List Term) (success : arguments active (argument :: rest) = .ok replaced) :
    term active (.app name (argument :: rest)) = .error (.unsupportedFunction name replacement) := by
  cases replacement <;> simp [term, found, success]
  rename_i other
  exact False.elim (nonName other rfl)

/-- An argument failure precedes an unsupported outer application head. -/
theorem argument_error_first (active : List (Name × Term)) (name : Name)
    (argument : Term) (rest : List Term) (error : Error)
    (failure : arguments active (argument :: rest) = .error error) :
    term active (.app name (argument :: rest)) = .error error := by
  cases found : lookup name active with
  | none => simp [term, found, failure]
  | some replacement => cases replacement <;> simp [term, found, failure]

/-- The repaired result of the original integer-binder counterexample. -/
def captureFixed : Formula :=
  .forall [("__microcfta_bound_1", .int)] (.atom .eq (.var "__microcfta_bound_1") (.lit 0))

/-- The repaired source renames the nullary application to the bound value. -/
theorem capture_fixed :
    checked [("unused", .var "x")] captureOriginal = .ok captureFixed := by
  have fresh : freshNames ["x", "x", "x", "unused"] 1 = ["__microcfta_bound_1"] := by decide +kernel
  simp [checked, formula, term, captureOriginal, captureFixed, prepare, uniqueNames, uniqueNamesFrom,
    identityReplacement, formulaNames, termNames, argumentsNames, fresh, renameName, lookup] <;> rfl

/-- The repaired result has no free names. -/
theorem capture_closed : freeNames captureFixed = [] := by
  simp [captureFixed, freeNames, formulaNames, termNames]

/-- The repaired result preserves the false universally quantified statement. -/
theorem capture_false (env : Name → Int) : ¬Holds integerModel env captureFixed := by
  intro all
  simp only [captureFixed, Holds, allBound] at all
  have one := all (1 : Int) True.intro
  simp [evaluateTerm, integerModel, update, CoreFormula.evalRelation] at one

/-- Binder preparation preserves every binder's sort and order. -/
theorem prepare_sorts (active : List (Name × Term)) (bound : List (Name × ValueSort))
    (bodyNames : List Name) : (prepare active bound bodyNames).1.map Prod.snd = bound.map Prod.snd := by
  simp [prepare, List.map_map]

/-- Repeated binders receive the same renamed name and retain their shadowing relation. -/
theorem duplicate_binders (active : List (Name × Term)) (name : Name) (first second : ValueSort)
    (bodyNames : List Name) :
    ∃ renamed, (prepare active [(name, first), (name, second)] bodyNames).1 =
      [(renamed, first), (renamed, second)] := by
  simp only [prepare]
  exact ⟨_, rfl⟩

/-- Binder names stop matching entries in the active substitution. -/
def without (bound : List (Name × ValueSort)) (active : List (Name × Term)) :=
  active.filter fun entry => !(bound.map Prod.fst).contains entry.1

theorem uniqueNamesFrom_mem (seen names : List Name) (name : Name) :
    name ∈ uniqueNamesFrom seen names ↔ name ∈ names ∧ name ∉ seen := by
  induction names generalizing seen with
  | nil => simp [uniqueNamesFrom]
  | cons head rest ih =>
      by_cases used : head ∈ seen
      · simp [uniqueNamesFrom, used, ih]
        intro unused equal
        subst name
        exact False.elim (unused used)
      · simp [uniqueNamesFrom, used, ih]
        grind

/-- The executable `nub` contains exactly the input names. -/
theorem uniqueNames_mem (names : List Name) (name : Name) : name ∈ uniqueNames names ↔ name ∈ names := by
  simp [uniqueNames, uniqueNamesFrom_mem]

/-- Lookup after shadow removal agrees outside the binder names. -/
theorem lookup_without (bound : List (Name × ValueSort)) (active : List (Name × Term)) (name : Name) :
    lookup name (without bound active) =
      if name ∈ bound.map Prod.fst then none else lookup name active := by
  induction active with
  | nil => simp [without, lookup]
  | cons entry rest ih =>
      rcases entry with ⟨key, replacement⟩
      by_cases same : name = key
      · subst key
        by_cases boundName : name ∈ bound.map Prod.fst
        · simpa [without, lookup, boundName] using ih
        · simp [without, lookup, boundName]
      · by_cases boundKey : key ∈ bound.map Prod.fst <;>
          simpa [without, lookup, same, boundKey] using ih

/-- Successful lookup returns an actual active replacement. -/
theorem lookup_member (active : List (Name × Term)) (name : Name) (replacement : Term)
    (found : lookup name active = some replacement) : (name, replacement) ∈ active := by
  induction active with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      by_cases same : name = key
      · simp [lookup, same] at found
        subst key; subst value; simp
      · exact List.mem_cons_of_mem _ (ih (by simpa [lookup, same] using found))

/-- The environment denoted by a simultaneous substitution. Replacement terms use the original environment. -/
noncomputable def assignment (model : Interpretation Value) (env : Name → Value)
    (active : List (Name × Term)) (name : Name) : Value :=
  match lookup name active with
  | none => env name
  | some replacement => evaluateTerm model env replacement

/-- Removing bound entries changes no assignment outside the binder names. -/
theorem assignment_without (model : Interpretation Value) (env : Name → Value)
    (active : List (Name × Term)) (bound : List (Name × ValueSort)) (name : Name)
    (free : name ∉ bound.map Prod.fst) :
    assignment model env (without bound active) name = assignment model env active name := by
  simp [assignment, lookup_without, free]

end MicroCFTA.FormulaSubstitution
