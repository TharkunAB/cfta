import MicroCFTA.CoreLattice
import Std.Data.String.ToNat

/-!
# The extended sorted formula syntax

This is the complete syntax added by `9ad319d`. The earlier `CoreFormula`
module remains the integer fragment that the automata construct. Quantified
semantics uses propositions. It does not assume a decision procedure for all
integer formulas. An interpretation supplies sort domains and primitive
operations; real arithmetic and solver behavior are separate boundaries.

Substitution follows the source algorithm, including its treatment of names
at function-application heads. The final counterexample exposes a semantic
failure in that algorithm even for an integer binder and a nullary application.
-/

namespace MicroCFTA.FullSyntax

abbrev Name := String
abbrev Relation := CoreFormula.Relation

/-- All source sorts, including named function signatures. -/
inductive ValueSort where
  | int | real | bool
  | function (arguments : List ValueSort) (result : ValueSort)
  deriving Repr

mutual
/-- All source term constructors after the sorted formula extension. -/
inductive Term where
  | lit (value : Int)
  | var (name : Name)
  | app (function : Name) (arguments : List Term)
  | neg (inner : Term)
  | add (left right : Term)
  | sub (left right : Term)
  | mul (left right : Term)
  | div (left right : Term)
  | mod (left right : Term)
  | ite (condition : Formula) (yes no : Term)
  | cast (inner : Term) (sort : ValueSort)
  deriving Repr

/-- All source Boolean constructors and sorted quantifiers. -/
inductive Formula where
  | top
  | and (parts : List Formula)
  | bottom
  | or (parts : List Formula)
  | not (inner : Formula)
  | atom (relation : Relation) (left right : Term)
  | forall (bound : List (Name × ValueSort)) (inner : Formula)
  | exists (bound : List (Name × ValueSort)) (inner : Formula)
  deriving Repr
end

/-- Primitive meanings and sort domains for the complete raw syntax. -/
structure Interpretation (Value : Type) where
  literal : Int → Value
  neg : Value → Value
  add : Value → Value → Value
  sub : Value → Value → Value
  mul : Value → Value → Value
  div : Value → Value → Value
  mod : Value → Value → Value
  apply : Value → List Value → Value
  cast : Value → ValueSort → Value
  hasSort : ValueSort → Value → Prop
  relation : Relation → Value → Value → Prop

/-- Assign one bound name while preserving every other name. -/
def update (env : Name → Value) (name : Name) (value : Value) : Name → Value :=
  fun other => if other = name then value else env other

/-- Universal sorted binders, from the outer binder to the inner binder. -/
def allBound (model : Interpretation Value) : List (Name × ValueSort) → (Name → Value) →
    ((Name → Value) → Prop) → Prop
  | [], env, body => body env
  | (name, sort) :: rest, env, body =>
      ∀ value, model.hasSort sort value → allBound model rest (update env name value) body

/-- Existential sorted binders, from the outer binder to the inner binder. -/
def someBound (model : Interpretation Value) : List (Name × ValueSort) → (Name → Value) →
    ((Name → Value) → Prop) → Prop
  | [], env, body => body env
  | (name, sort) :: rest, env, body =>
      ∃ value, model.hasSort sort value ∧ someBound model rest (update env name value) body

noncomputable section
open Classical in
mutual
/-- Interpret all term constructors, including sorted function values and conditional terms. -/
def evaluateTerm (model : Interpretation Value) (env : Name → Value) : Term → Value
  | .lit n => model.literal n
  | .var name => env name
  | .app name arguments => model.apply (env name) (evaluateTerms model env arguments)
  | .neg t => model.neg (evaluateTerm model env t)
  | .add t u => model.add (evaluateTerm model env t) (evaluateTerm model env u)
  | .sub t u => model.sub (evaluateTerm model env t) (evaluateTerm model env u)
  | .mul t u => model.mul (evaluateTerm model env t) (evaluateTerm model env u)
  | .div t u => model.div (evaluateTerm model env t) (evaluateTerm model env u)
  | .mod t u => model.mod (evaluateTerm model env t) (evaluateTerm model env u)
  | .ite p t u => if Holds model env p then evaluateTerm model env t else evaluateTerm model env u
  | .cast t sort => model.cast (evaluateTerm model env t) sort
termination_by t => sizeOf t

/-- Interpret the arguments of an uninterpreted function in source order. -/
def evaluateTerms (model : Interpretation Value) (env : Name → Value) : List Term → List Value
  | [] => []
  | t :: ts => evaluateTerm model env t :: evaluateTerms model env ts
termination_by ts => sizeOf ts

/-- Classical truth of the complete sorted syntax. -/
def Holds (model : Interpretation Value) (env : Name → Value) : Formula → Prop
  | .top => True
  | .bottom => False
  | .and ps => holdsAll model env ps
  | .or ps => holdsAny model env ps
  | .not p => ¬Holds model env p
  | .atom r t u => model.relation r (evaluateTerm model env t) (evaluateTerm model env u)
  | .forall bound p => allBound model bound env (fun assigned => Holds model assigned p)
  | .exists bound p => someBound model bound env (fun assigned => Holds model assigned p)
termination_by p => sizeOf p

/-- Every conjunction part holds. -/
def holdsAll (model : Interpretation Value) (env : Name → Value) : List Formula → Prop
  | [] => True
  | p :: ps => Holds model env p ∧ holdsAll model env ps
termination_by ps => sizeOf ps

/-- At least one disjunction part holds. -/
def holdsAny (model : Interpretation Value) (env : Name → Value) : List Formula → Prop
  | [] => False
  | p :: ps => Holds model env p ∨ holdsAny model env ps
termination_by ps => sizeOf ps
end
end

mutual
/-- Free names of a term. Function names participate in the same name space. -/
def termNames : Term → List Name
  | .lit _ => []
  | .var name => [name]
  | .app functionName arguments => functionName :: argumentsNames arguments
  | .neg t | .cast t _ => termNames t
  | .add t u | .sub t u | .mul t u | .div t u | .mod t u => termNames t ++ termNames u
  | .ite p t u => formulaNames p ++ termNames t ++ termNames u
termination_by t => sizeOf t

/-- Free names in function arguments. -/
def argumentsNames : List Term → List Name
  | [] => []
  | t :: ts => termNames t ++ argumentsNames ts
termination_by ts => sizeOf ts

/-- Free names of a formula, before duplicate removal. -/
def formulaNames : Formula → List Name
  | .top | .bottom => []
  | .and ps | .or ps => partsNames ps
  | .not p => formulaNames p
  | .atom _ t u => termNames t ++ termNames u
  | .forall bound p | .exists bound p =>
      (formulaNames p).filter fun name => !(bound.map Prod.fst).contains name
termination_by p => sizeOf p

/-- Free names of formula list parts. -/
def partsNames : List Formula → List Name
  | [] => []
  | p :: ps => formulaNames p ++ partsNames ps
termination_by ps => sizeOf ps
end

/-- The source free-name set, with hash iteration order abstracted. -/
def freeNames (p : Formula) : List Name := (formulaNames p).eraseDups

/-- Detect the exact identity entries that the source removes before substitution. -/
def identityReplacement : Name × Term → Bool
  | (name, .var other) => name == other
  | _ => false

/-- Source replacement lookup uses the first active matching entry. -/
def lookup (name : Name) : List (Name × Term) → Option Term
  | [] => none
  | (key, term) :: rest => if name = key then some term else lookup name rest

/-- A finite prefix of the source's fresh-name stream. -/
def freshNames (avoid : List Name) (count : Nat) : List Name :=
  (((List.range (avoid.length + count)).map
    (fun index => "__microcfta_bound_" ++ toString (index + 1))).filter
      (fun candidate => !avoid.contains candidate)).take count

private theorem freshCandidate_injective : Function.Injective
    (fun index : Nat => "__microcfta_bound_" ++ toString (index + 1)) := by
  intro left right equal
  have digits := (String.append_right_inj "__microcfta_bound_").mp equal
  have same : left + 1 = right + 1 := Nat.repr_injective digits
  omega

private theorem freshCandidates_nodup (count : Nat) :
    ((List.range count).map (fun index => "__microcfta_bound_" ++ toString (index + 1))).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact List.Pairwise.imp (fun apart same => apart (freshCandidate_injective same)) List.nodup_range

private theorem filter_partition_length (items : List Name) (keep : Name → Bool) :
    (items.filter keep).length + (items.filter fun item => !keep item).length = items.length := by
  induction items with
  | nil => rfl
  | cons item rest ih => cases h : keep item <;> simp [h] at * <;> omega

/-- The finite candidate prefix always supplies every requested fresh binder name. -/
theorem freshNames_length (avoid : List Name) (count : Nat) :
    (freshNames avoid count).length = count := by
  let candidates := (List.range (avoid.length + count)).map
    (fun index => "__microcfta_bound_" ++ toString (index + 1))
  have unique := freshCandidates_nodup (avoid.length + count)
  have rejectedUnique := List.Pairwise.filter (fun name => avoid.contains name) unique
  have rejectedBound : (candidates.filter fun name => avoid.contains name).length ≤ avoid.length := by
    apply List.Nodup.length_le_of_subset rejectedUnique
    intro name member
    simpa using (List.mem_filter.mp member).2
  have partition := filter_partition_length candidates (fun name => avoid.contains name)
  have length : candidates.length = avoid.length + count := by simp [candidates]
  unfold freshNames
  rw [List.length_take]
  change min count (candidates.filter fun name => !avoid.contains name).length = count
  omega

/-- Every requested fresh name is distinct from every other fresh name. -/
theorem freshNames_nodup (avoid : List Name) (count : Nat) : (freshNames avoid count).Nodup := by
  exact (List.Pairwise.filter _ (freshCandidates_nodup (avoid.length + count))).take

/-- Remove shadowed substitutions and prepend the source's bound-variable renamings. -/
def prepareBinders (active : List (Name × Term)) (bound : List (Name × ValueSort))
    (bodyNames : List Name) : List (Name × ValueSort) × List (Name × Term) :=
  let kept := active.filter fun entry => !(bound.map Prod.fst).contains entry.1
  let captured := kept.flatMap fun entry => termNames entry.2
  let avoid := captured ++ bodyNames ++ bound.map Prod.fst
  let renamed := (bound.zip (freshNames avoid bound.length)).map fun ((name, sort), fresh) =>
    if captured.contains name then ((fresh, sort), [(name, Term.var fresh)])
    else ((name, sort), [])
  (renamed.map Prod.fst, renamed.flatMap Prod.snd ++ kept)

/-- Binder preparation retains every binder and its position. -/
theorem prepareBinders_length (active : List (Name × Term)) (bound : List (Name × ValueSort))
    (bodyNames : List Name) : (prepareBinders active bound bodyNames).1.length = bound.length := by
  simp [prepareBinders, freshNames_length]

mutual
/-- Source substitution in terms leaves the name at every application head unchanged. -/
def substituteTerm (active : List (Name × Term)) : Term → Term
  | .lit n => .lit n
  | .var name => (lookup name active).getD (.var name)
  | .app functionName arguments => .app functionName (substituteArguments active arguments)
  | .neg t => .neg (substituteTerm active t)
  | .add t u => .add (substituteTerm active t) (substituteTerm active u)
  | .sub t u => .sub (substituteTerm active t) (substituteTerm active u)
  | .mul t u => .mul (substituteTerm active t) (substituteTerm active u)
  | .div t u => .div (substituteTerm active t) (substituteTerm active u)
  | .mod t u => .mod (substituteTerm active t) (substituteTerm active u)
  | .ite p t u => .ite (substituteActive active p) (substituteTerm active t) (substituteTerm active u)
  | .cast t sort => .cast (substituteTerm active t) sort
termination_by t => sizeOf t

/-- Source substitution in every function argument. -/
def substituteArguments (active : List (Name × Term)) : List Term → List Term
  | [] => []
  | t :: ts => substituteTerm active t :: substituteArguments active ts
termination_by ts => sizeOf ts

/-- The complete source substitution algorithm under sorted binders. -/
def substituteActive (active : List (Name × Term)) : Formula → Formula
  | .top => .top
  | .bottom => .bottom
  | .and ps => .and (substituteParts active ps)
  | .or ps => .or (substituteParts active ps)
  | .not p => .not (substituteActive active p)
  | .atom r t u => .atom r (substituteTerm active t) (substituteTerm active u)
  | .forall bound p =>
      let (renamed, nestedActive) := prepareBinders active bound (formulaNames p)
      .forall renamed (substituteActive nestedActive p)
  | .exists bound p =>
      let (renamed, nestedActive) := prepareBinders active bound (formulaNames p)
      .exists renamed (substituteActive nestedActive p)
termination_by p => sizeOf p

/-- Source substitution in every Boolean list part. -/
def substituteParts (active : List (Name × Term)) : List Formula → List Formula
  | [] => []
  | p :: ps => substituteActive active p :: substituteParts active ps
termination_by ps => sizeOf ps
end

/-- Remove identity entries once, then perform the complete source substitution. -/
def substitute (replacements : List (Name × Term)) (p : Formula) : Formula :=
  substituteActive (replacements.filter fun entry => !identityReplacement entry) p

/-- Every produced fresh name avoids the forbidden set. -/
theorem freshNames_avoids (avoid : List Name) (count : Nat) (name : Name)
    (member : name ∈ freshNames avoid count) : name ∉ avoid := by
  have filtered := List.mem_of_mem_take member
  exact by simpa using (List.mem_filter.mp filtered).2

/-- Applied function names never receive a variable replacement. -/
theorem substitute_app_head (active : List (Name × Term)) (name : Name) (arguments : List Term) :
    substituteTerm active (.app name arguments) = .app name (substituteArguments active arguments) := by
  simp [substituteTerm]

/-- An integer interpretation sufficient for the integer-only counterexample. -/
def integerModel : Interpretation Int where
  literal := id
  neg := (- ·)
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := Int.ediv
  mod := Int.emod
  apply := fun function arguments => if arguments.isEmpty then function else 0
  cast := fun value _ => value
  hasSort := fun sort value => match sort with
    | .int => True
    | .bool => value = 0 ∨ value = 1
    | .real | .function _ _ => False
  relation := fun relation left right => CoreFormula.evalRelation relation left right = true

/-- The source translates a nullary application to its function expression unchanged. -/
theorem nullary_application (env : Name → Int) (name : Name) :
    evaluateTerm integerModel env (.app name []) = env name := by
  simp [evaluateTerm, evaluateTerms, integerModel]

/-- The closed formula used in the runtime capture reproduction. -/
def captureOriginal : Formula := .forall [("x", .int)] (.atom .eq (.app "x" []) (.lit 0))

/-- The result produced by the source for a substitution on an absent name. -/
def captureRewritten : Formula :=
  .forall [("__microcfta_bound_1", .int)] (.atom .eq (.app "x" []) (.lit 0))

/-- The executable source transcription reproduces the faulty alpha-renaming. -/
theorem capture_substitution :
    substitute [("unused", .var "x")] captureOriginal = captureRewritten := by
  have fresh : freshNames ["x", "x", "x"] 1 = ["__microcfta_bound_1"] := by decide +kernel
  simp [substitute, captureOriginal, captureRewritten, substituteActive, substituteTerm,
    substituteArguments, prepareBinders, identityReplacement, formulaNames,
    termNames, argumentsNames, fresh]

/-- Substitution introduces a free name even though the replaced name was absent. -/
theorem capture_freeNames :
    freeNames captureOriginal = [] ∧ freeNames captureRewritten = ["x"] := by
  simp [freeNames, captureOriginal, captureRewritten, formulaNames, termNames, argumentsNames, List.eraseDups_cons]

/-- The original closed formula is false over the integers. -/
theorem capture_original_false (env : Name → Int) : ¬Holds integerModel env captureOriginal := by
  intro all
  simp only [captureOriginal, Holds, allBound] at all
  have one := all (1 : Int) True.intro
  simp [evaluateTerm, evaluateTerms, integerModel, update, CoreFormula.evalRelation] at one

/-- Under ambient `x = 0`, the substituted formula becomes true. -/
theorem capture_rewritten_true (env : Name → Int) (zero : env "x" = 0) :
    Holds integerModel env captureRewritten := by
  simp [captureRewritten, Holds, allBound, evaluateTerm, evaluateTerms, integerModel,
    update, CoreFormula.evalRelation, zero]

/-- The source substitution does not preserve meaning, even for an absent replacement name. -/
theorem substitution_not_sound :
    ¬Holds integerModel (fun _ => 0) captureOriginal ∧
      Holds integerModel (fun _ => 0) (substitute [("unused", .var "x")] captureOriginal) := by
  exact ⟨capture_original_false _, by rw [capture_substitution]; exact capture_rewritten_true _ rfl⟩

mutual
/-- Embed the proved integer term fragment without changing its syntax. -/
def embedTerm : CoreFormula.Term → Term
  | .lit n => .lit n
  | .var name => .var name
  | .neg t => .neg (embedTerm t)
  | .add t u => .add (embedTerm t) (embedTerm u)
  | .sub t u => .sub (embedTerm t) (embedTerm u)
  | .mul t u => .mul (embedTerm t) (embedTerm u)
  | .ite p t u => .ite (embedFormula p) (embedTerm t) (embedTerm u)
termination_by t => sizeOf t

/-- Embed the complete quantifier-free core Boolean fragment. -/
def embedFormula : CoreFormula.Formula → Formula
  | .top => .top
  | .bottom => .bottom
  | .and ps => .and (embedParts ps)
  | .or ps => .or (embedParts ps)
  | .not p => .not (embedFormula p)
  | .atom r t u => .atom r (embedTerm t) (embedTerm u)
termination_by p => sizeOf p

/-- Embed every part of a core formula list. -/
def embedParts : List CoreFormula.Formula → List Formula
  | [] => []
  | p :: ps => embedFormula p :: embedParts ps
termination_by ps => sizeOf ps
end

mutual
/-- The full syntax's integer interpretation preserves the earlier term semantics. -/
theorem embedTerm_evaluation (env : Name → Int) (t : CoreFormula.Term) :
    evaluateTerm integerModel env (embedTerm t) = CoreFormula.evalTerm env t := by
  cases t with
  | lit n => simp [embedTerm, evaluateTerm, CoreFormula.evalTerm] <;> rfl
  | var n => simp [embedTerm, evaluateTerm, CoreFormula.evalTerm] <;> rfl
  | neg t => simp [embedTerm, evaluateTerm, CoreFormula.evalTerm, embedTerm_evaluation env t] <;> rfl
  | add t u => simp [embedTerm, evaluateTerm, CoreFormula.evalTerm,
      embedTerm_evaluation env t, embedTerm_evaluation env u] <;> rfl
  | sub t u => simp [embedTerm, evaluateTerm, CoreFormula.evalTerm,
      embedTerm_evaluation env t, embedTerm_evaluation env u] <;> rfl
  | mul t u => simp [embedTerm, evaluateTerm, CoreFormula.evalTerm,
      embedTerm_evaluation env t, embedTerm_evaluation env u] <;> rfl
  | ite p t u => simp [embedTerm, evaluateTerm, CoreFormula.evalTerm,
      embedFormula_holds env p, embedTerm_evaluation env t, embedTerm_evaluation env u] <;> rfl
termination_by sizeOf t

/-- Full classical truth agrees with the earlier executable core truth. -/
theorem embedFormula_holds (env : Name → Int) (p : CoreFormula.Formula) :
    Holds integerModel env (embedFormula p) ↔ CoreFormula.evalFormula env p = true := by
  cases p with
  | top => simp [embedFormula, Holds, CoreFormula.evalFormula] <;> rfl
  | bottom => simp [embedFormula, Holds, CoreFormula.evalFormula] <;> rfl
  | and ps => simp [embedFormula, Holds, CoreFormula.evalFormula, embedParts_all env ps] <;> rfl
  | or ps => simp [embedFormula, Holds, CoreFormula.evalFormula, embedParts_any env ps] <;> rfl
  | not p => simp [embedFormula, Holds, CoreFormula.evalFormula, embedFormula_holds env p] <;> rfl
  | atom r t u => simp [embedFormula, Holds, CoreFormula.evalFormula,
      embedTerm_evaluation env t, embedTerm_evaluation env u] <;> rfl
termination_by sizeOf p

/-- Conjunction lists retain every truth condition under embedding. -/
theorem embedParts_all (env : Name → Int) (ps : List CoreFormula.Formula) :
    holdsAll integerModel env (embedParts ps) ↔ CoreFormula.evalAll env ps = true := by
  cases ps with
  | nil => simp [embedParts, holdsAll, CoreFormula.evalAll] <;> rfl
  | cons p ps => simp [embedParts, holdsAll, CoreFormula.evalAll,
      embedFormula_holds env p, embedParts_all env ps] <;> rfl
termination_by sizeOf ps

/-- Disjunction lists retain every truth condition under embedding. -/
theorem embedParts_any (env : Name → Int) (ps : List CoreFormula.Formula) :
    holdsAny integerModel env (embedParts ps) ↔ CoreFormula.evalAny env ps = true := by
  cases ps with
  | nil => simp [embedParts, holdsAny, CoreFormula.evalAny] <;> rfl
  | cons p ps => simp [embedParts, holdsAny, CoreFormula.evalAny,
      embedFormula_holds env p, embedParts_any env ps] <;> rfl
termination_by sizeOf ps
end

/-- The source lattice parser rejects all newly added arithmetic forms and conditional terms. -/
def lowerTerm : Term → LatticeLinear.Expr Name
  | .lit n => .integer n
  | .var name => .name name
  | .neg t => .neg (lowerTerm t)
  | .add t u => .add (lowerTerm t) (lowerTerm u)
  | .sub t u => .sub (lowerTerm t) (lowerTerm u)
  | .mul t u => .mul (lowerTerm t) (lowerTerm u)
  | .app _ _ | .div _ _ | .mod _ _ | .ite _ _ _ | .cast _ _ => .unsupported

mutual
/-- The source signed compiler supports the Boolean core and rejects each quantifier. -/
def lowerFormula : Formula → LatticeFormula.Formula Name
  | .top => .top
  | .bottom => .bottom
  | .and ps => lowerAll ps
  | .or ps => lowerAny ps
  | .not p => .neg (lowerFormula p)
  | .atom r t u => .atom (CoreLattice.lowerRelation r) (lowerTerm t) (lowerTerm u)
  | .forall _ _ | .exists _ _ => .unsupported
termination_by p => sizeOf p

/-- Compile conjunction lists with the source fold and identity. -/
def lowerAll : List Formula → LatticeFormula.Formula Name
  | [] => .top
  | p :: ps => .conj (lowerFormula p) (lowerAll ps)
termination_by ps => sizeOf ps

/-- Compile disjunction lists with the source fold and identity. -/
def lowerAny : List Formula → LatticeFormula.Formula Name
  | [] => .bottom
  | p :: ps => .disj (lowerFormula p) (lowerAny ps)
termination_by ps => sizeOf ps
end

/-- The extended source parser agrees with the proved core term parser on every core term. -/
theorem lowerTerm_embed (t : CoreFormula.Term) :
    lowerTerm (embedTerm t) = CoreLattice.lowerTerm t := by
  cases t with
  | lit n => simp [embedTerm, lowerTerm, CoreLattice.lowerTerm]
  | var n => simp [embedTerm, lowerTerm, CoreLattice.lowerTerm]
  | neg t => simp [embedTerm, lowerTerm, CoreLattice.lowerTerm, lowerTerm_embed t]
  | add t u | sub t u | mul t u =>
      simp [embedTerm, lowerTerm, CoreLattice.lowerTerm, lowerTerm_embed t, lowerTerm_embed u]
  | ite p t u => simp [embedTerm, lowerTerm, CoreLattice.lowerTerm]
termination_by sizeOf t

mutual
/-- Extended source formula compilation agrees exactly with the previously proved core compiler. -/
theorem lowerFormula_embed (p : CoreFormula.Formula) :
    lowerFormula (embedFormula p) = CoreLattice.lowerFormula p := by
  cases p with
  | top => simp [embedFormula, lowerFormula, CoreLattice.lowerFormula]
  | bottom => simp [embedFormula, lowerFormula, CoreLattice.lowerFormula]
  | and ps => simp [embedFormula, lowerFormula, CoreLattice.lowerFormula, lowerAll_embed ps]
  | or ps => simp [embedFormula, lowerFormula, CoreLattice.lowerFormula, lowerAny_embed ps]
  | not p => simp [embedFormula, lowerFormula, CoreLattice.lowerFormula, lowerFormula_embed p]
  | atom r t u => simp [embedFormula, lowerFormula, CoreLattice.lowerFormula, lowerTerm_embed]
termination_by sizeOf p

/-- Conjunction compilation agrees for every embedded core part. -/
theorem lowerAll_embed (ps : List CoreFormula.Formula) :
    lowerAll (embedParts ps) = CoreLattice.lowerAll ps := by
  cases ps with
  | nil => simp [embedParts, lowerAll, CoreLattice.lowerAll]
  | cons p ps => simp [embedParts, lowerAll, CoreLattice.lowerAll,
      lowerFormula_embed p, lowerAll_embed ps]
termination_by sizeOf ps

/-- Disjunction compilation agrees for every embedded core part. -/
theorem lowerAny_embed (ps : List CoreFormula.Formula) :
    lowerAny (embedParts ps) = CoreLattice.lowerAny ps := by
  cases ps with
  | nil => simp [embedParts, lowerAny, CoreLattice.lowerAny]
  | cons p ps => simp [embedParts, lowerAny, CoreLattice.lowerAny,
      lowerFormula_embed p, lowerAny_embed ps]
termination_by sizeOf ps
end

/-- Compile the full source syntax, including its explicit unsupported cases. -/
def signed (variableOf : Name → Option Nat) (positive : Bool) (p : Formula) :=
  LatticeFormula.signed variableOf positive (lowerFormula p)

/-- Every old core compilation result remains unchanged by the source syntax extension. -/
theorem signed_embed (variableOf : Name → Option Nat) (positive : Bool) (p : CoreFormula.Formula) :
    signed variableOf positive (embedFormula p) = CoreLattice.signed variableOf positive p := by
  simp [signed, CoreLattice.signed, lowerFormula_embed]

/-- The lattice compiler rejects universal formulas without traversing their bodies. -/
theorem signed_forall (variableOf : Name → Option Nat) (positive : Bool)
    (bound : List (Name × ValueSort)) (p : Formula) :
    signed variableOf positive (.forall bound p) = .error .unsupported := by
  simp [signed, lowerFormula, LatticeFormula.signed]

/-- The lattice compiler rejects existential formulas without traversing their bodies. -/
theorem signed_exists (variableOf : Name → Option Nat) (positive : Bool)
    (bound : List (Name × ValueSort)) (p : Formula) :
    signed variableOf positive (.exists bound p) = .error .unsupported := by
  simp [signed, lowerFormula, LatticeFormula.signed]

/-- The lattice compiler rejects a cast even when it preserves an integer literal. -/
theorem cast_rejected (variableOf : Name → Option Nat) (t : Term) (sort : ValueSort) :
    LatticeLinear.linearTerm variableOf (lowerTerm (.cast t sort)) = .error .nonlinear := by
  simp [lowerTerm, LatticeLinear.linearTerm]

/-- The lattice compiler rejects division and modulo even when their operands are literals. -/
theorem division_modulo_rejected (variableOf : Name → Option Nat) (t u : Term) :
    LatticeLinear.linearTerm variableOf (lowerTerm (.div t u)) = .error .nonlinear ∧
      LatticeLinear.linearTerm variableOf (lowerTerm (.mod t u)) = .error .nonlinear := by
  simp [lowerTerm, LatticeLinear.linearTerm]

/-- The lattice compiler rejects all applications, including nullary applications. -/
theorem application_rejected (variableOf : Name → Option Nat) (name : Name) (arguments : List Term) :
    LatticeLinear.linearTerm variableOf (lowerTerm (.app name arguments)) = .error .nonlinear := by
  simp [lowerTerm, LatticeLinear.linearTerm]

/-- Defined evaluation in the lattice arithmetic syntax implies membership in the proved core fragment. -/
theorem lowerTerm_is_core (env : Name → Int) (t : Term) (value : Int)
    (evaluated : LatticeLinear.evalExpr env (lowerTerm t) = some value) :
    ∃ core : CoreFormula.Term, embedTerm core = t := by
  cases t with
  | lit n => exact ⟨.lit n, by simp [embedTerm]⟩
  | var name => exact ⟨.var name, by simp [embedTerm]⟩
  | neg t =>
      cases child : LatticeLinear.evalExpr env (lowerTerm t) with
      | none => simp [lowerTerm, LatticeLinear.evalExpr, child] at evaluated
      | some v =>
          obtain ⟨core, equal⟩ := lowerTerm_is_core env t v child
          exact ⟨.neg core, by simp [embedTerm, equal]⟩
  | add t u =>
      cases left : LatticeLinear.evalExpr env (lowerTerm t) <;>
        cases right : LatticeLinear.evalExpr env (lowerTerm u) <;>
        simp only [lowerTerm, LatticeLinear.evalExpr, left, right, Option.pure_def] at evaluated
      all_goals try contradiction
      next lv rv =>
        obtain ⟨lc, le⟩ := lowerTerm_is_core env t lv left
        obtain ⟨rc, re⟩ := lowerTerm_is_core env u rv right
        exact ⟨.add lc rc, by simp [embedTerm, le, re]⟩
  | sub t u =>
      cases left : LatticeLinear.evalExpr env (lowerTerm t) <;>
        cases right : LatticeLinear.evalExpr env (lowerTerm u) <;>
        simp only [lowerTerm, LatticeLinear.evalExpr, left, right, Option.pure_def] at evaluated
      all_goals try contradiction
      next lv rv =>
        obtain ⟨lc, le⟩ := lowerTerm_is_core env t lv left
        obtain ⟨rc, re⟩ := lowerTerm_is_core env u rv right
        exact ⟨.sub lc rc, by simp [embedTerm, le, re]⟩
  | mul t u =>
      cases left : LatticeLinear.evalExpr env (lowerTerm t) <;>
        cases right : LatticeLinear.evalExpr env (lowerTerm u) <;>
        simp only [lowerTerm, LatticeLinear.evalExpr, left, right, Option.pure_def] at evaluated
      all_goals try contradiction
      next lv rv =>
        obtain ⟨lc, le⟩ := lowerTerm_is_core env t lv left
        obtain ⟨rc, re⟩ := lowerTerm_is_core env u rv right
        exact ⟨.mul lc rc, by simp [embedTerm, le, re]⟩
  | app function arguments | div t u | mod t u | ite p t u | cast t sort =>
      simp [lowerTerm, LatticeLinear.evalExpr] at evaluated
termination_by sizeOf t

mutual
/-- Defined lattice evaluation extracts an exact core formula, not a semantic approximation. -/
theorem lowerFormula_is_core (env : Name → Int) (p : Formula) (value : Bool)
    (evaluated : LatticeFormula.evaluateFormula env (lowerFormula p) = some value) :
    ∃ core : CoreFormula.Formula, embedFormula core = p := by
  cases p with
  | top => exact ⟨.top, by simp [embedFormula]⟩
  | bottom => exact ⟨.bottom, by simp [embedFormula]⟩
  | and ps =>
      obtain ⟨core, equal⟩ := lowerAll_is_core env ps value (by simpa [lowerFormula] using evaluated)
      exact ⟨.and core, by simp [embedFormula, equal]⟩
  | or ps =>
      obtain ⟨core, equal⟩ := lowerAny_is_core env ps value (by simpa [lowerFormula] using evaluated)
      exact ⟨.or core, by simp [embedFormula, equal]⟩
  | not p =>
      cases child : LatticeFormula.evaluateFormula env (lowerFormula p) with
      | none => simp [lowerFormula, LatticeFormula.evaluateFormula, child] at evaluated
      | some v =>
          obtain ⟨core, equal⟩ := lowerFormula_is_core env p v child
          exact ⟨.not core, by simp [embedFormula, equal]⟩
  | atom r t u =>
      cases left : LatticeLinear.evalExpr env (lowerTerm t) <;>
        cases right : LatticeLinear.evalExpr env (lowerTerm u) <;>
        simp only [lowerFormula, LatticeFormula.evaluateFormula, left, right,
          Option.pure_def] at evaluated
      all_goals try contradiction
      next lv rv =>
        obtain ⟨lc, le⟩ := lowerTerm_is_core env t lv left
        obtain ⟨rc, re⟩ := lowerTerm_is_core env u rv right
        exact ⟨.atom r lc rc, by simp [embedFormula, le, re]⟩
  | «forall» bound p | «exists» bound p => simp [lowerFormula, LatticeFormula.evaluateFormula] at evaluated
termination_by sizeOf p

/-- A defined conjunction fold retains all source parts in the core fragment. -/
theorem lowerAll_is_core (env : Name → Int) (ps : List Formula) (value : Bool)
    (evaluated : LatticeFormula.evaluateFormula env (lowerAll ps) = some value) :
    ∃ core : List CoreFormula.Formula, embedParts core = ps := by
  cases ps with
  | nil => exact ⟨[], by simp [embedParts]⟩
  | cons p ps =>
      cases head : LatticeFormula.evaluateFormula env (lowerFormula p) <;>
        cases tail : LatticeFormula.evaluateFormula env (lowerAll ps) <;>
        simp only [lowerAll, LatticeFormula.evaluateFormula, head, tail,
          Option.pure_def] at evaluated
      all_goals try contradiction
      next hv tv =>
        obtain ⟨hc, he⟩ := lowerFormula_is_core env p hv head
        obtain ⟨tc, te⟩ := lowerAll_is_core env ps tv tail
        exact ⟨hc :: tc, by simp [embedParts, he, te]⟩
termination_by sizeOf ps

/-- A defined disjunction fold retains all source parts in the core fragment. -/
theorem lowerAny_is_core (env : Name → Int) (ps : List Formula) (value : Bool)
    (evaluated : LatticeFormula.evaluateFormula env (lowerAny ps) = some value) :
    ∃ core : List CoreFormula.Formula, embedParts core = ps := by
  cases ps with
  | nil => exact ⟨[], by simp [embedParts]⟩
  | cons p ps =>
      cases head : LatticeFormula.evaluateFormula env (lowerFormula p) <;>
        cases tail : LatticeFormula.evaluateFormula env (lowerAny ps) <;>
        simp only [lowerAny, LatticeFormula.evaluateFormula, head, tail,
          Option.pure_def] at evaluated
      all_goals try contradiction
      next hv tv =>
        obtain ⟨hc, he⟩ := lowerFormula_is_core env p hv head
        obtain ⟨tc, te⟩ := lowerAny_is_core env ps tv tail
        exact ⟨hc :: tc, by simp [embedParts, he, te]⟩
termination_by sizeOf ps
end

/-- Every successful parse of the full source syntax belongs exactly to the verified core fragment. -/
theorem signed_success_is_core (variableOf : Name → Option Nat) (positive : Bool)
    (p : Formula) (result : LatticeSigned.Checked)
    (success : signed variableOf positive p = .ok result) :
    ∃ core : CoreFormula.Formula, embedFormula core = p ∧
      CoreLattice.signed variableOf positive core = .ok result := by
  obtain ⟨value, evaluated, _⟩ := LatticeFormula.signed_correct variableOf
    (fun _ => 0) (fun _ => 0) (by intros; rfl) (lowerFormula p) positive result success
  obtain ⟨core, equal⟩ := lowerFormula_is_core (fun _ => 0) p value evaluated
  refine ⟨core, equal, ?_⟩
  rw [← equal, signed_embed] at success
  exact success

/-- A successful full-syntax parse counts exactly the assignments satisfying its classical meaning. -/
theorem signed_true_iff (variableOf : Name → Option Nat) (env : Name → Int)
    (assignment : Nat → Int)
    (environment : ∀ name index, variableOf name = some index → env name = assignment index)
    (p : Formula) (result : LatticeSigned.Checked)
    (success : signed variableOf true p = .ok result) :
    LatticeSigned.score assignment result.terms = 1 ↔ Holds integerModel env p := by
  obtain ⟨core, equal, parsed⟩ := signed_success_is_core variableOf true p result success
  rw [← equal, embedFormula_holds,
    CoreLattice.signed_indicator variableOf env assignment environment core result parsed]
  cases CoreFormula.evalFormula env core <;> decide

end MicroCFTA.FullSyntax
