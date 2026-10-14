import MicroCFTA.FormulaLowering
import MicroCFTA.Guards

/-!
# The Liquid Fixpoint query adapter

The model keeps the source declaration order and first-match sort lookup.
Hash sets are lists with duplicate removal; their iteration order is not used
by the semantic claims. The response and interruption are explicit inputs.
The measured floating-point time comparison is an explicit Boolean input.
No theorem certifies the external solver, serializer, clock, or IO protocol.
-/
namespace MicroCFTA.SolverAdapter
open FullSyntax
open FormulaLowering (TargetSort)

abbrev Declaration := Name × TargetSort

mutual
/-- The emitted value cases of Liquid Fixpoint 0.9.6.3.7 `exprSymbolsSet`. -/
def termSymbols : FormulaLowering.Term → List Name
  | .integer _ => []
  | .variable name => [name]
  | .negative inner | .cast inner _ => termSymbols inner
  | .binary _ left right | .application left right => termSymbols left ++ termSymbols right
  | .conditional condition yes no => formulaSymbols condition ++ termSymbols yes ++ termSymbols no
termination_by term => sizeOf term

/-- The emitted predicate cases remove every locally bound name. -/
def formulaSymbols : FormulaLowering.Formula → List Name
  | .true | .false => []
  | .and parts | .or parts => partsSymbols parts
  | .not inner => formulaSymbols inner
  | .atom _ left right => termSymbols left ++ termSymbols right
  | .forall bound inner | .exists bound inner =>
      (formulaSymbols inner).filter fun name => !(bound.map Prod.fst).contains name
termination_by formula => sizeOf formula

/-- Set union is represented by append before the final duplicate removal. -/
def partsSymbols : List FormulaLowering.Formula → List Name
  | [] => []
  | first :: rest => formulaSymbols first ++ partsSymbols rest
termination_by parts => sizeOf parts
end

mutual
theorem term_symbols_lower (input : FullSyntax.Term) :
    termSymbols (FormulaLowering.lowerTerm input) = FullSyntax.termNames input := by
  cases input with
  | lit _ | var _ => simp [FormulaLowering.lowerTerm, termSymbols, FullSyntax.termNames]
  | app name arguments =>
      simpa [FormulaLowering.lowerTerm, FullSyntax.termNames, termSymbols] using
        apps_symbols_lower arguments (.variable name)
  | neg inner | cast inner _ =>
      simpa [FormulaLowering.lowerTerm, FullSyntax.termNames, termSymbols] using term_symbols_lower inner
  | add left right | sub left right | mul left right | div left right | mod left right =>
      simp [FormulaLowering.lowerTerm, FullSyntax.termNames, termSymbols,
        term_symbols_lower left, term_symbols_lower right]
  | ite condition yes no =>
      simp [FormulaLowering.lowerTerm, FullSyntax.termNames, termSymbols,
        formula_symbols_lower condition, term_symbols_lower yes, term_symbols_lower no]
termination_by sizeOf input

theorem apps_symbols_lower (arguments : List FullSyntax.Term) (function : FormulaLowering.Term) :
    termSymbols (FormulaLowering.lowerApps function arguments) =
      termSymbols function ++ FullSyntax.argumentsNames arguments := by
  cases arguments with
  | nil => simp [FormulaLowering.lowerApps, FullSyntax.argumentsNames]
  | cons argument rest =>
      simp only [FormulaLowering.lowerApps, FullSyntax.argumentsNames]
      rw [apps_symbols_lower rest (.application function (FormulaLowering.lowerTerm argument))]
      simp [termSymbols, term_symbols_lower argument, List.append_assoc]
termination_by sizeOf arguments

theorem formula_symbols_lower (input : FullSyntax.Formula) :
    formulaSymbols (FormulaLowering.lowerFormula input) = FullSyntax.formulaNames input := by
  cases input with
  | top | bottom => simp [FormulaLowering.lowerFormula, formulaSymbols, FullSyntax.formulaNames]
  | and parts | or parts =>
      simpa [FormulaLowering.lowerFormula, FullSyntax.formulaNames, formulaSymbols] using parts_symbols_lower parts
  | not inner =>
      simpa [FormulaLowering.lowerFormula, FullSyntax.formulaNames, formulaSymbols] using formula_symbols_lower inner
  | atom _ left right =>
      simp [FormulaLowering.lowerFormula, FullSyntax.formulaNames, formulaSymbols,
        term_symbols_lower left, term_symbols_lower right]
  | «forall» bound inner | «exists» bound inner =>
      simp [FormulaLowering.lowerFormula, FullSyntax.formulaNames, formulaSymbols,
        formula_symbols_lower inner, List.map_map, Function.comp_def]
termination_by sizeOf input

theorem parts_symbols_lower (parts : List FullSyntax.Formula) :
    partsSymbols (FormulaLowering.lowerParts parts) = FullSyntax.partsNames parts := by
  cases parts with
  | nil => simp [FormulaLowering.lowerParts, partsSymbols, FullSyntax.partsNames]
  | cons first rest =>
      simp [FormulaLowering.lowerParts, FullSyntax.partsNames, partsSymbols,
        formula_symbols_lower first, parts_symbols_lower rest]
termination_by sizeOf parts
end

/-- The source unions the symbols of both queries and all ambient assumptions. -/
def mentioned (assumptions : List FullSyntax.Formula) (antecedent consequent : FullSyntax.Formula) : List Name :=
  (formulaSymbols (FormulaLowering.lowerFormula antecedent) ++
    formulaSymbols (FormulaLowering.lowerFormula consequent) ++
    partsSymbols (FormulaLowering.lowerParts assumptions)).eraseDups

theorem mentioned_exact (assumptions : List FullSyntax.Formula)
    (antecedent consequent : FullSyntax.Formula) (name : Name) :
    name ∈ mentioned assumptions antecedent consequent ↔
      name ∈ FullSyntax.formulaNames antecedent ∨ name ∈ FullSyntax.formulaNames consequent ∨
        name ∈ FullSyntax.partsNames assumptions := by
  simp [mentioned, formula_symbols_lower, parts_symbols_lower]

/-- The source distinguished refinement value name. -/
def valueName : Name := "__cfta_value"

/-- The source default query limit is ten thousand milliseconds. -/
def defaultTimeLimit : Int := 10000

/-- The source retains all given declarations and adds the default value sort. -/
def declarations (given : List Declaration) : List Declaration :=
  if valueName ∈ given.map Prod.fst then given else (valueName, .int) :: given

/-- Declaration lookup uses the first matching name, including duplicate inputs. -/
def lookupSort (name : Name) : List Declaration → Option TargetSort
  | [] => none
  | (key, sort) :: rest => if name = key then some sort else lookupSort name rest

/-- Fresh names cannot collide with ambient declarations; undeclared originals use Int. -/
def freshDeclaration (ambient : List Declaration) (binding : Name × Name) : Option Declaration :=
  if binding.1 ∈ ambient.map Prod.fst then none
  else some (binding.1, (lookupSort binding.2 ambient).getD .int)

/-- The source traverses bindings without removing duplicate fresh names. -/
def freshDeclarations (ambient : List Declaration) : List (Name × Name) → Option (List Declaration)
  | [] => some []
  | binding :: rest => do
      let first ← freshDeclaration ambient binding
      let tail ← freshDeclarations ambient rest
      pure (first :: tail)

theorem fresh_rejected (ambient : List Declaration) (binding : Name × Name) :
    freshDeclaration ambient binding = none ↔ binding.1 ∈ ambient.map Prod.fst := by
  simp [freshDeclaration]

theorem fresh_sort (ambient : List Declaration) (binding : Name × Name)
    (absent : binding.1 ∉ ambient.map Prod.fst) :
    freshDeclaration ambient binding = some (binding.1, (lookupSort binding.2 ambient).getD .int) := by
  simp [freshDeclaration, absent]

theorem fresh_all_accepted (ambient : List Declaration) (bindings : List (Name × Name)) :
    (freshDeclarations ambient bindings).isSome = true ↔
      ∀ binding ∈ bindings, binding.1 ∉ ambient.map Prod.fst := by
  induction bindings with
  | nil => simp [freshDeclarations]
  | cons binding rest ih =>
      by_cases collides : binding.1 ∈ ambient.map Prod.fst
      · have rejected : ¬∀ entry ∈ binding :: rest, entry.1 ∉ ambient.map Prod.fst :=
          fun all => all binding (by simp) collides
        constructor
        · intro accepted
          simp [freshDeclarations, freshDeclaration, collides] at accepted
        · intro all
          exact False.elim (rejected all)
      · simp only [List.forall_mem_cons, collides, not_false_eq_true, true_and, ←ih]
        cases result : freshDeclarations ambient rest <;>
          simp [freshDeclarations, freshDeclaration, collides, result]

theorem value_declared (given : List Declaration) : valueName ∈ (declarations given).map Prod.fst := by
  simp only [declarations]
  split <;> simp_all

theorem declared_sort_first (name : Name) (sort : TargetSort) (rest : List Declaration) :
    lookupSort name ((name, sort) :: rest) = some sort := by simp [lookupSort]

/-- Only names outside both declaration sets receive a default integer declaration. -/
def undeclared (ambient fresh : List Declaration) (mentioned : List Name) : List Declaration :=
  ((mentioned.eraseDups).filter fun name =>
    !(ambient.map Prod.fst ++ fresh.map Prod.fst).contains name).map (fun name => (name, .int))

theorem undeclared_exact (ambient fresh : List Declaration) (mentioned : List Name)
    (name : Name) (sort : TargetSort) :
    (name, sort) ∈ undeclared ambient fresh mentioned ↔
      name ∈ mentioned ∧ name ∉ ambient.map Prod.fst ∧ name ∉ fresh.map Prod.fst ∧ sort = .int := by
  simp only [undeclared, List.mem_map]
  constructor
  · rintro ⟨item, member, equal⟩
    have same : item = name := congrArg Prod.fst equal
    subst item
    have rest := List.mem_filter.mp member
    refine ⟨by simpa using rest.1, ?_, ?_, (congrArg Prod.snd equal).symm⟩
    · simpa using (show name ∉ ambient.map Prod.fst ∧ name ∉ fresh.map Prod.fst from by simpa using rest.2).1
    · simpa using (show name ∉ ambient.map Prod.fst ∧ name ∉ fresh.map Prod.fst from by simpa using rest.2).2
  · rintro ⟨member, oldAbsent, freshAbsent, rfl⟩
    exact ⟨name, by simp [member, oldAbsent, freshAbsent], rfl⟩

/-- The exact assertion passed to smtAssertDecl before CheckSat. -/
def assertion (assumptions : List FullSyntax.Formula) (antecedent consequent : FullSyntax.Formula) :
    FormulaLowering.Formula :=
  .and (FormulaLowering.lowerParts assumptions ++
    [FormulaLowering.lowerFormula antecedent, .not (FormulaLowering.lowerFormula consequent)])

/-- A successful source preflight produces all query-local declarations and one assertion. -/
structure Prepared where
  declared : List Declaration
  asserted : FormulaLowering.Formula

/-- Mentioned names come from the emitted expression symbol collector. -/
def prepare (given : List Declaration) (bindings : List (Name × Name)) (mentioned : List Name)
    (assumptions : List FullSyntax.Formula) (antecedent consequent : FullSyntax.Formula) : Option Prepared := do
  let ambient := declarations given
  let fresh ← freshDeclarations ambient bindings
  pure ⟨ambient ++ fresh ++ undeclared ambient fresh mentioned, assertion assumptions antecedent consequent⟩

/-- The complete source preflight includes the actual emitted free-symbol set. -/
def prepareQuery (given : List Declaration) (bindings : List (Name × Name))
    (assumptions : List FullSyntax.Formula) (antecedent consequent : FullSyntax.Formula) : Option Prepared :=
  prepare given bindings (mentioned assumptions antecedent consequent) assumptions antecedent consequent

/-- Every mentioned name is declared after a successful preflight. -/
theorem mentioned_declared (ambient fresh : List Declaration) (names : List Name)
    (name : Name) (present : name ∈ names) :
    name ∈ (ambient ++ fresh ++ undeclared ambient fresh names).map Prod.fst := by
  by_cases old : name ∈ ambient.map Prod.fst
  · simp [old]
  by_cases generated : name ∈ fresh.map Prod.fst
  · simp [generated]
  have added : (name, TargetSort.int) ∈ undeclared ambient fresh names :=
    (undeclared_exact ambient fresh names name .int).mpr ⟨present, old, generated, rfl⟩
  have member : name ∈ (undeclared ambient fresh names).map Prod.fst := List.mem_map.mpr ⟨_, added, rfl⟩
  simp [member]

/-- Every environment considered by the assertion respects every supplied declaration. -/
def Admitted (model : FormulaLowering.Model Value) (declared : List Declaration) (env : Name → Value) : Prop :=
  ∀ binding ∈ declared, model.hasSort binding.2 (env binding.1)

private theorem holdsAll_append (model : FormulaLowering.Model Value) (env : Name → Value)
    (first second : List FormulaLowering.Formula) :
    FormulaLowering.holdsAll model env (first ++ second) ↔
      FormulaLowering.holdsAll model env first ∧ FormulaLowering.holdsAll model env second := by
  induction first with
  | nil => simp [FormulaLowering.holdsAll]
  | cons head tail ih => simp [FormulaLowering.holdsAll, ih, and_assoc]

/-- The emitted assertion is exactly an ambient counterexample to entailment. -/
theorem assertion_exact (model : FormulaLowering.Model Value) (env : Name → Value)
    (assumptions : List FullSyntax.Formula) (antecedent consequent : FullSyntax.Formula) :
    FormulaLowering.Holds model env (assertion assumptions antecedent consequent) ↔
      FullSyntax.holdsAll (FormulaLowering.sourceModel model) env assumptions ∧
      FullSyntax.Holds (FormulaLowering.sourceModel model) env antecedent ∧
      ¬FullSyntax.Holds (FormulaLowering.sourceModel model) env consequent := by
  simp only [assertion, FormulaLowering.Holds, holdsAll_append,
    FormulaLowering.holdsAll, FormulaLowering.formula_lower, and_true]
  exact and_congr (FormulaLowering.parts_lower model assumptions env).1 Iff.rfl

/-- The intended query ranges over the declared domains under the ambient assumptions. -/
def Entails (model : FormulaLowering.Model Value) (declared : List Declaration)
    (assumptions : List FullSyntax.Formula) (antecedent consequent : FullSyntax.Formula) : Prop :=
  ∀ env, Admitted model declared env →
    FullSyntax.holdsAll (FormulaLowering.sourceModel model) env assumptions →
    FullSyntax.Holds (FormulaLowering.sourceModel model) env antecedent →
    FullSyntax.Holds (FormulaLowering.sourceModel model) env consequent

/-- Unsatisfiability of the exact assertion is equivalent to the declared-domain entailment. -/
theorem unsat_iff_entails (model : FormulaLowering.Model Value) (declared : List Declaration)
    (assumptions : List FullSyntax.Formula) (antecedent consequent : FullSyntax.Formula) :
    (¬∃ env, Admitted model declared env ∧
      FormulaLowering.Holds model env (assertion assumptions antecedent consequent)) ↔
      Entails model declared assumptions antecedent consequent := by
  classical
  simp only [assertion_exact, Entails]
  constructor
  · intro none env admitted ambient left
    exact Classical.byContradiction (fun denied => none ⟨env, admitted, ambient, left, denied⟩)
  · rintro proved ⟨env, admitted, ambient, left, denied⟩
    exact denied (proved env admitted ambient left)

/-- Response constructors relevant to the source mapping. -/
inductive Response where
  | unsat | sat | unknown
  | error (message : String)
  | unexpected (description : String)
  deriving DecidableEq, Repr

/-- Exceptions remain distinct from conservative Unknown verdicts. -/
inductive Failure where
  | timeLimit (milliseconds : Int)
  | rejected (message : String)
  | unexpected (description : String)
  | interrupted (description : String)
  deriving DecidableEq, Repr

/-- The returned value or raised exception of a query. -/
inductive Result where
  | returned (verdict : Guards.Verdict)
  | raised (failure : Failure)
  deriving DecidableEq, Repr

/-- Map a response after the measured comparison `seconds * 1000 >= milliseconds`. -/
def responseVerdict (milliseconds : Int) (limitReached : Bool) : Response → Result
  | .unsat => .returned .yes
  | .sat => .returned .no
  | .unknown => if limitReached then .raised (.timeLimit milliseconds) else .returned .unknown
  | .error message => .raised (.rejected message)
  | .unexpected description => .raised (.unexpected description)

theorem unknown_before_limit (milliseconds : Int) :
    responseVerdict milliseconds false .unknown = .returned .unknown := rfl

theorem unknown_at_limit (milliseconds : Int) :
    responseVerdict milliseconds true .unknown = .raised (.timeLimit milliseconds) := rfl

/-- The external check either throws or supplies a response and measured comparison. -/
inductive Attempt where
  | interrupted (description : String)
  | answered (response : Response) (limitReached : Bool)
  deriving DecidableEq, Repr

/-- Pure control result; replacement describes the requested process action. -/
structure Decision where
  replaceContext : Bool
  result : Result
  deriving DecidableEq, Repr

/-- Source exceptions and Error responses request replacement before propagation. -/
def finish (milliseconds : Int) : Attempt → Decision
  | .interrupted description => ⟨true, .raised (.interrupted description)⟩
  | .answered response reached =>
      ⟨match response with | .error _ => true | _ => false,
        responseVerdict milliseconds reached response⟩

/-- Preflight collisions return Unknown without submitting a query or replacing a context. -/
def run (given : List Declaration) (bindings : List (Name × Name))
    (milliseconds : Int) (attempt : Attempt) : Decision :=
  match freshDeclarations (declarations given) bindings with
  | none => ⟨false, .returned .unknown⟩
  | some _ => finish milliseconds attempt

/-- The complete pure query protocol submits only a successfully prepared request. -/
def execute (given : List Declaration) (bindings : List (Name × Name))
    (assumptions : List FullSyntax.Formula) (antecedent consequent : FullSyntax.Formula)
    (milliseconds : Int) (check : Prepared → Attempt) : Decision :=
  match prepareQuery given bindings assumptions antecedent consequent with
  | none => ⟨false, .returned .unknown⟩
  | some request => finish milliseconds (check request)

/-- A successful preflight always emits the exact source assertion. -/
theorem prepared_assertion (given : List Declaration) (bindings : List (Name × Name))
    (assumptions : List FullSyntax.Formula) (antecedent consequent : FullSyntax.Formula)
    (request : Prepared) (found : prepareQuery given bindings assumptions antecedent consequent = some request) :
    request.asserted = assertion assumptions antecedent consequent := by
  cases fresh : freshDeclarations (declarations given) bindings <;>
    simp [prepareQuery, prepare, fresh] at found
  subst request
  rfl

/-- The actual prepared request declares every name read by either query or an assumption. -/
theorem prepared_names (given : List Declaration) (bindings : List (Name × Name))
    (assumptions : List FullSyntax.Formula) (antecedent consequent : FullSyntax.Formula)
    (request : Prepared) (found : prepareQuery given bindings assumptions antecedent consequent = some request)
    (name : Name) (present : name ∈ mentioned assumptions antecedent consequent) :
    name ∈ request.declared.map Prod.fst := by
  cases fresh : freshDeclarations (declarations given) bindings with
  | none => simp [prepareQuery, prepare, fresh] at found
  | some entries =>
      simp [prepareQuery, prepare, fresh] at found
      subst request
      simpa only [List.append_assoc] using mentioned_declared (declarations given) entries _ name present

/-- A preflight rejection cannot inspect the external check result. -/
theorem rejected_without_check (given : List Declaration) (bindings : List (Name × Name))
    (assumptions : List FullSyntax.Formula) (antecedent consequent : FullSyntax.Formula)
    (milliseconds : Int) (check : Prepared → Attempt)
    (rejected : freshDeclarations (declarations given) bindings = none) :
    execute given bindings assumptions antecedent consequent milliseconds check =
      ⟨false, .returned .unknown⟩ := by
  simp [execute, prepareQuery, prepare, rejected]

/-- The external solver contract is limited to the meaning of Sat and Unsat. -/
def ResponseCorrect (model : FormulaLowering.Model Value) (request : Prepared) : Response → Prop
  | .unsat => ¬∃ env, Admitted model request.declared env ∧ FormulaLowering.Holds model env request.asserted
  | .sat => ∃ env, Admitted model request.declared env ∧ FormulaLowering.Holds model env request.asserted
  | _ => True

/-- Exceptions do not claim a semantic answer. -/
def ResultSupports : Result → Prop → Prop
  | .returned verdict, proposition => Guards.Supports verdict proposition
  | .raised _, _ => True

/-- A sound external response gives a sound verdict for the actual declared-domain query. -/
theorem response_sound (model : FormulaLowering.Model Value) (request : Prepared)
    (assumptions : List FullSyntax.Formula) (antecedent consequent : FullSyntax.Formula)
    (asserted : request.asserted = assertion assumptions antecedent consequent)
    (milliseconds : Int) (reached : Bool) (response : Response)
    (correct : ResponseCorrect model request response) :
    ResultSupports (responseVerdict milliseconds reached response)
      (Entails model request.declared assumptions antecedent consequent) := by
  cases response with
  | unsat =>
      apply (unsat_iff_entails model request.declared assumptions antecedent consequent).mp
      simpa [ResponseCorrect, asserted] using correct
  | sat =>
      intro entailed
      have noWitness := (unsat_iff_entails model request.declared assumptions antecedent consequent).mpr entailed
      exact noWitness (by simpa [ResponseCorrect, asserted] using correct)
  | unknown => cases reached <;> trivial
  | error _ | unexpected _ => trivial

/-- The adapter does not add any semantic assumption beyond a correct external response. -/
theorem execute_sound (model : FormulaLowering.Model Value)
    (given : List Declaration) (bindings : List (Name × Name))
    (assumptions : List FullSyntax.Formula) (antecedent consequent : FullSyntax.Formula)
    (milliseconds : Int) (check : Prepared → Attempt) (request : Prepared)
    (found : prepareQuery given bindings assumptions antecedent consequent = some request)
    (correct : ∀ response reached, check request = .answered response reached → ResponseCorrect model request response) :
    ResultSupports (execute given bindings assumptions antecedent consequent milliseconds check).result
      (Entails model request.declared assumptions antecedent consequent) := by
  simp only [execute, found]
  cases answer : check request with
  | interrupted _ => trivial
  | answered response reached =>
      exact response_sound model request assumptions antecedent consequent
        (prepared_assertion given bindings assumptions antecedent consequent request found)
        milliseconds reached response (correct response reached answer)

theorem error_replaces (milliseconds : Int) (message : String) (reached : Bool) :
    finish milliseconds (.answered (.error message) reached) =
      ⟨true, .raised (.rejected message)⟩ := rfl

theorem interruption_replaces (milliseconds : Int) (message : String) :
    finish milliseconds (.interrupted message) = ⟨true, .raised (.interrupted message)⟩ := rfl

/-- Time-limit conversion occurs after the source successful-check branch. -/
theorem timeout_keeps_context (milliseconds : Int) :
    finish milliseconds (.answered .unknown true) =
      ⟨false, .raised (.timeLimit milliseconds)⟩ := rfl

/-- The adapter does not reject duplicate generated names before submitting the query. -/
example : freshDeclarations (declarations []) [("fresh", "x"), ("fresh", "x")] =
    some [("fresh", .int), ("fresh", .int)] := by decide +kernel

/-- An unused ambient declaration is enough to reject the first generated spelling. -/
example : run [("__cfta_actual_0", .int)]
    [("__cfta_actual_0", "a"), ("__cfta_actual_1", "a")]
    10000 (.answered .unsat false) = ⟨false, .returned .unknown⟩ := by decide +kernel

/-- A spelling that avoids the same ambient declaration reaches the Unsat result. -/
example : run [("__cfta_actual_0", .int)]
    [("__cfta_actual_1", "a"), ("__cfta_actual_2", "a")]
    10000 (.answered .unsat false) = ⟨false, .returned .yes⟩ := by decide +kernel

/-- The full query preparation has the same collision, even for an empty Top query. -/
example : execute [("__cfta_actual_0", .int)]
    [("__cfta_actual_0", "a"), ("__cfta_actual_1", "a")]
    [] .top .top 10000 (fun _ => .answered .unsat false) =
      ⟨false, .returned .unknown⟩ := by decide +kernel

/-- Changing only the fresh spelling permits the same valid Top query. -/
example : execute [("__cfta_actual_0", .int)]
    [("__cfta_actual_1", "a"), ("__cfta_actual_2", "a")]
    [] .top .top 10000 (fun _ => .answered .unsat false) =
      ⟨false, .returned .yes⟩ := by decide +kernel

/-- Explicit source sorts win; an undeclared original defaults to Int. -/
example : (freshDeclaration [("x", .bool)] ("fresh", "x"),
    freshDeclaration [("x", .bool)] ("fresh", "missing")) =
      (some ("fresh", .bool), some ("fresh", .int)) := by decide +kernel

/-- Ambient duplicate names are retained, with the first declaration used for fresh sorts. -/
example : declarations [(valueName, .real), (valueName, .int)] =
    [(valueName, .real), (valueName, .int)] ∧
    freshDeclaration (declarations [(valueName, .real), (valueName, .int)]) ("fresh", valueName) =
      some ("fresh", .real) := by decide +kernel

/-- Top is a valid query under every ambient sort domain and assumption set. -/
theorem top_entails (model : FormulaLowering.Model Value) (declared : List Declaration)
    (assumptions : List FullSyntax.Formula) : Entails model declared assumptions .top .top := by
  intro env _ _ _
  trivial

end MicroCFTA.SolverAdapter
