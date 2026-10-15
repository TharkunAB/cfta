import MicroCFTA.SourceSolverNamePreparation

/-!
# Actual application arities and inferred source declarations

The source visits application heads before their arguments. It visits the
antecedent, consequent, and assumptions in that order. The final occurrence
of a name supplies its arity. Conflicting arities are not rejected.
-/
namespace MicroCFTA.SourceAppliedDeclarations
open FullSyntax (Name)
open FormulaLowering SolverAdapter SourceSolverNamePreparation

abbrev Arities := List (Name × Nat)

mutual
/-- Read applied names in the actual source formula order, including quantified bodies. -/
def applications : FullSyntax.Formula → Arities
  | .top | .bottom => []
  | .and parts | .or parts => partApplications parts
  | .not inner | .forall _ inner | .exists _ inner => applications inner
  | .atom _ left right => termApplications left ++ termApplications right
termination_by formula => sizeOf formula

/-- Record a function head before all applications in its ordered arguments. -/
def termApplications : FullSyntax.Term → Arities
  | .lit _ | .var _ => []
  | .neg inner | .cast inner _ => termApplications inner
  | .add left right | .sub left right | .mul left right | .div left right | .mod left right =>
      termApplications left ++ termApplications right
  | .app name arguments => (name, arguments.length) :: argumentApplications arguments
  | .ite condition yes no => applications condition ++ termApplications yes ++ termApplications no
termination_by term => sizeOf term

/-- Preserve source argument order in the application map input. -/
def argumentApplications : List FullSyntax.Term → Arities
  | [] => []
  | first :: rest => termApplications first ++ argumentApplications rest
termination_by terms => sizeOf terms

/-- Preserve source Boolean-part order in the application map input. -/
def partApplications : List FullSyntax.Formula → Arities
  | [] => []
  | first :: rest => applications first ++ partApplications rest
termination_by formulas => sizeOf formulas
end

/-- The source foldMap over Boolean parts is this exact ordered list. -/
theorem partApplications_flatMap (parts : List FullSyntax.Formula) :
    partApplications parts = parts.flatMap applications := by
  induction parts with
  | nil => simp only [partApplications, List.flatMap_nil]
  | cons first rest ih => simp only [partApplications, List.flatMap_cons, ih]

/-- The source foldMap over function arguments retains the head-before-arguments order. -/
theorem argumentApplications_flatMap (arguments : List FullSyntax.Term) :
    argumentApplications arguments = arguments.flatMap termApplications := by
  induction arguments with
  | nil => simp only [argumentApplications, List.flatMap_nil]
  | cons first rest ih => simp only [argumentApplications, List.flatMap_cons, ih]

/-- The source arity map receives the query before the ambient assumptions. -/
def queryApplications (assumptions : List FullSyntax.Formula)
    (antecedent consequent : FullSyntax.Formula) : Arities :=
  applications antecedent ++ applications consequent ++ partApplications assumptions

/-- The source foldMap visits the antecedent, consequent, and assumptions in order. -/
theorem queryApplications_source (assumptions : List FullSyntax.Formula)
    (antecedent consequent : FullSyntax.Formula) :
    queryApplications assumptions antecedent consequent =
      (antecedent :: consequent :: assumptions).flatMap applications := by
  simp only [queryApplications, List.flatMap_cons, partApplications_flatMap, List.append_assoc]

mutual
/-- Every embedded arithmetic-core term has no uninterpreted applications. -/
theorem core_term (term : CoreFormula.Term) : termApplications (FullSyntax.embedTerm term) = [] := by
  cases term with
  | lit _ | var _ => simp only [FullSyntax.embedTerm, termApplications]
  | neg inner => simpa only [FullSyntax.embedTerm, termApplications] using core_term inner
  | add left right | sub left right | mul left right =>
      simp only [FullSyntax.embedTerm, termApplications, core_term left, core_term right, List.nil_append]
  | ite condition yes no =>
      simp only [FullSyntax.embedTerm, termApplications, core_formula condition, core_term yes, core_term no, List.nil_append]
termination_by sizeOf term

/-- Every embedded arithmetic-core formula has the historical default-sort behavior. -/
theorem core_formula (formula : CoreFormula.Formula) : applications (FullSyntax.embedFormula formula) = [] := by
  cases formula with
  | top | bottom => simp only [FullSyntax.embedFormula, applications]
  | and parts | or parts => simpa only [FullSyntax.embedFormula, applications] using core_parts parts
  | not inner => simpa only [FullSyntax.embedFormula, applications] using core_formula inner
  | atom _ left right =>
      simp only [FullSyntax.embedFormula, applications, core_term left, core_term right, List.nil_append]
termination_by sizeOf formula

/-- Ambient arithmetic-core assumptions introduce no inferred function sorts. -/
theorem core_parts (parts : List CoreFormula.Formula) : partApplications (FullSyntax.embedParts parts) = [] := by
  cases parts with
  | nil => simp only [FullSyntax.embedParts, partApplications]
  | cons first rest =>
      simp only [FullSyntax.embedParts, partApplications, core_formula first, core_parts rest, List.nil_append]
termination_by sizeOf parts
end

/-- HashMap.fromList retains the last supplied arity for each name. -/
def lookupArity (name : Name) : Arities → Option Nat
  | [] => none
  | (key, arity) :: rest => match lookupArity name rest with
    | some found => some found
    | none => if key = name then some arity else none

/-- A final occurrence overrides every preceding arity for the same name. -/
theorem lookupArity_append (name : Name) (first second : Arities) :
    lookupArity name (first ++ second) = (lookupArity name second).orElse (fun _ => lookupArity name first) := by
  induction first with
  | nil => simp only [List.nil_append, lookupArity]; cases lookupArity name second <;> rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, arity⟩
      simp only [List.cons_append, lookupArity, ih]
      cases lookupArity name second <;> cases lookupArity name rest <;> rfl

/-- Applied names use an integer function sort; other undeclared names use Int. -/
def inferredSort (arities : Arities) (name : Name) : TargetSort :=
  match lookupArity name arities with
  | none => .int
  | some arity => lowerSort (.function (List.replicate arity .int) .int)

/-- Source mkFFunc normalizes a zero-argument inferred function to Int. -/
theorem inferred_nullary (name : Name) : inferredSort [(name, 0)] name = .int := by
  simp [inferredSort, lookupArity, lowerSort, lowerArguments]

/-- Only undeclared mentioned names receive the inferred source sort. -/
def undeclared (ambient fresh : List Declaration) (mentioned : List Name) (arities : Arities) : List Declaration :=
  ((mentioned.eraseDups).filter fun name =>
    !(ambient.map Prod.fst ++ fresh.map Prod.fst).contains name).map (fun name => (name, inferredSort arities name))

/-- Exact membership retains the source declaration exclusions and inferred sort. -/
theorem undeclared_exact (ambient fresh : List Declaration) (mentioned : List Name) (arities : Arities)
    (name : Name) (sort : TargetSort) :
    (name, sort) ∈ undeclared ambient fresh mentioned arities ↔
      name ∈ mentioned ∧ name ∉ ambient.map Prod.fst ∧ name ∉ fresh.map Prod.fst ∧ sort = inferredSort arities name := by
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

/-- Without applications, the historical default declarations are unchanged. -/
theorem undeclared_empty (ambient fresh : List Declaration) (mentioned : List Name) :
    undeclared ambient fresh mentioned [] = SolverAdapter.undeclared ambient fresh mentioned := rfl

/-- Injective encoding retains the last arity for each original name. -/
theorem lookupArity_rename (rename : Name → Name) (injective : Function.Injective rename)
    (arities : Arities) (name : Name) :
    lookupArity (rename name) (arities.map fun entry => (rename entry.1, entry.2)) = lookupArity name arities := by
  induction arities with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, arity⟩
      simp only [List.map_cons, lookupArity, ih, injective.eq_iff]

/-- The actual function sort survives the same injective name encoding. -/
theorem inferredSort_rename (rename : Name → Name) (injective : Function.Injective rename)
    (arities : Arities) (name : Name) :
    inferredSort (arities.map fun entry => (rename entry.1, entry.2)) (rename name) = inferredSort arities name := by
  simp only [inferredSort, lookupArity_rename rename injective]

/-- Name encoding preserves every inferred declaration, including conflicting arities. -/
theorem undeclared_rename (rename : Name → Name) (injective : Function.Injective rename)
    (ambient fresh : List Declaration) (names : List Name) (arities : Arities) :
    undeclared (ambient.map (mapDeclaration rename)) (fresh.map (mapDeclaration rename)) (names.map rename)
        (arities.map fun entry => (rename entry.1, entry.2)) =
      (undeclared ambient fresh names arities).map (mapDeclaration rename) := by
  unfold undeclared
  rw [eraseDups_names rename injective, declaration_names, declaration_names, ← List.map_append,
    filter_names rename injective]
  simp only [List.map_map, Function.comp_def, inferredSort_rename rename injective, mapDeclaration]

end MicroCFTA.SourceAppliedDeclarations
