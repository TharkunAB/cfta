import MicroCFTA.OpenIntegerSource

/-!
# Successful lattice parsing validates every free source name

Arithmetic parsing visits both operands before normalization. Boolean parsing
visits both branches before signed-set operations. A canceled coefficient or
an empty signed region cannot hide an undeclared source name.
-/
namespace MicroCFTA.LatticeDeclaredNames
open FullSyntax
attribute [local simp] LatticeLinear.except_bind_ok LatticeLinear.except_bind_error
  LatticeLinear.except_map_ok LatticeLinear.except_map_error

/-- Every free name of a successfully parsed source term has an actual declared coordinate. -/
theorem term_declared (variableOf : Name → Option Nat) (input : Term) (result : LatticeLinear.Linear)
    (parsed : LatticeLinear.linearTerm variableOf (lowerTerm input) = .ok result) :
    ∀ name ∈ termNames input, ∃ index, variableOf name = some index := by
  cases input with
  | lit value => simp [termNames]
  | var name =>
      cases found : variableOf name with
      | none => simp [lowerTerm, LatticeLinear.linearTerm, found] at parsed
      | some index => simpa [termNames] using Exists.intro index found
  | neg inner =>
      cases found : LatticeLinear.linearTerm variableOf (lowerTerm inner) with
      | error error => simp [lowerTerm, LatticeLinear.linearTerm, found, Except.map] at parsed
      | ok value => simpa [termNames] using term_declared variableOf inner value found
  | add left right | sub left right | mul left right =>
      cases leftParsed : LatticeLinear.linearTerm variableOf (lowerTerm left) with
      | error error => simp [lowerTerm, LatticeLinear.linearTerm, leftParsed] at parsed
      | ok leftValue =>
          cases rightParsed : LatticeLinear.linearTerm variableOf (lowerTerm right) with
          | error error => simp [lowerTerm, LatticeLinear.linearTerm, leftParsed, rightParsed] at parsed
          | ok rightValue =>
              intro name member
              simp only [termNames, List.mem_append] at member
              rcases member with member | member
              · exact term_declared variableOf left leftValue leftParsed name member
              · exact term_declared variableOf right rightValue rightParsed name member
  | app _ _ | div _ _ | mod _ _ | cast _ _ | ite _ _ _ =>
      simp [lowerTerm, LatticeLinear.linearTerm] at parsed
termination_by sizeOf input

/-- Retaining a parsed form's sparse invariant does not weaken name validation. -/
theorem parseTerm_declared (variableOf : Name → Option Nat) (input : Term)
    (result : {form : LatticeLinear.Linear // LatticeLinear.Valid form})
    (parsed : LatticeFormula.parseTerm variableOf (lowerTerm input) = .ok result) :
    ∀ name ∈ termNames input, ∃ index, variableOf name = some index := by
  unfold LatticeFormula.parseTerm at parsed
  split at parsed
  · cases parsed
  · next value found => exact term_declared variableOf input value found

/-- Atom parsing checks names from both operands, including canceled expressions. -/
theorem atom_declared (variableOf : Name → Option Nat) (positive : Bool)
    (relation : CoreFormula.Relation) (left right : Term) (result : LatticeSigned.Checked)
    (parsed : LatticeFormula.parseAtom variableOf positive (CoreLattice.lowerRelation relation)
      (lowerTerm left) (lowerTerm right) = .ok result) :
    ∀ name ∈ termNames left ++ termNames right, ∃ index, variableOf name = some index := by
  cases rightParsed : LatticeFormula.parseTerm variableOf (lowerTerm right) with
  | error error => simp [LatticeFormula.parseAtom, rightParsed] at parsed
  | ok rightValue =>
      cases leftParsed : LatticeFormula.parseTerm variableOf (lowerTerm left) with
      | error error => simp [LatticeFormula.parseAtom, rightParsed, leftParsed] at parsed
      | ok leftValue =>
          intro name member
          rcases List.mem_append.mp member with member | member
          · exact parseTerm_declared variableOf left leftValue leftParsed name member
          · exact parseTerm_declared variableOf right rightValue rightParsed name member

mutual
/-- A successful full-syntax signed parse declares every free source name. -/
theorem formula_declared (variableOf : Name → Option Nat) (positive : Bool)
    (input : Formula) (result : LatticeSigned.Checked)
    (parsed : signed variableOf positive input = .ok result) :
    ∀ name ∈ formulaNames input, ∃ index, variableOf name = some index := by
  cases input with
  | top | bottom => simp [formulaNames]
  | atom relation left right =>
      simpa [formulaNames] using atom_declared variableOf positive relation left right result
        (by simpa [signed, lowerFormula, LatticeFormula.signed] using parsed)
  | not inner =>
      simpa [formulaNames] using formula_declared variableOf (!positive) inner result
        (by simpa [signed, lowerFormula, LatticeFormula.signed] using parsed)
  | and parts =>
      simpa [formulaNames] using all_declared variableOf positive parts result
        (by simpa [signed, lowerFormula] using parsed)
  | or parts =>
      simpa [formulaNames] using any_declared variableOf positive parts result
        (by simpa [signed, lowerFormula] using parsed)
  | «forall» _ _ | «exists» _ _ => simp [signed, lowerFormula, LatticeFormula.signed] at parsed
termination_by sizeOf input

/-- Every conjunction child is checked before the signed intersection is formed. -/
theorem all_declared (variableOf : Name → Option Nat) (positive : Bool)
    (inputs : List Formula) (result : LatticeSigned.Checked)
    (parsed : LatticeFormula.signed variableOf positive (lowerAll inputs) = .ok result) :
    ∀ name ∈ partsNames inputs, ∃ index, variableOf name = some index := by
  cases inputs with
  | nil => simp [partsNames]
  | cons first rest =>
      cases firstParsed : LatticeFormula.signed variableOf positive (lowerFormula first) with
      | error error => simp [lowerAll, LatticeFormula.signed, firstParsed] at parsed
      | ok firstValue =>
          cases restParsed : LatticeFormula.signed variableOf positive (lowerAll rest) with
          | error error => simp [lowerAll, LatticeFormula.signed, firstParsed, restParsed] at parsed
          | ok restValue =>
              intro name member
              simp only [partsNames, List.mem_append] at member
              rcases member with member | member
              · exact formula_declared variableOf positive first firstValue firstParsed name member
              · exact all_declared variableOf positive rest restValue restParsed name member
termination_by sizeOf inputs

/-- Every disjunction child is checked before signed union normalization. -/
theorem any_declared (variableOf : Name → Option Nat) (positive : Bool)
    (inputs : List Formula) (result : LatticeSigned.Checked)
    (parsed : LatticeFormula.signed variableOf positive (lowerAny inputs) = .ok result) :
    ∀ name ∈ partsNames inputs, ∃ index, variableOf name = some index := by
  cases inputs with
  | nil => simp [partsNames]
  | cons first rest =>
      cases firstParsed : LatticeFormula.signed variableOf positive (lowerFormula first) with
      | error error => simp [lowerAny, LatticeFormula.signed, firstParsed] at parsed
      | ok firstValue =>
          cases restParsed : LatticeFormula.signed variableOf positive (lowerAny rest) with
          | error error => simp [lowerAny, LatticeFormula.signed, firstParsed, restParsed] at parsed
          | ok restValue =>
              intro name member
              simp only [partsNames, List.mem_append] at member
              rcases member with member | member
              · exact formula_declared variableOf positive first firstValue firstParsed name member
              · exact any_declared variableOf positive rest restValue restParsed name member
termination_by sizeOf inputs
end

/-- Public successful counting establishes membership in its exact declaration table. -/
theorem points_declared (names : List Name) (input : Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points names (lowerFormula input) = .ok points) :
    ∀ name ∈ formulaNames input, name ∈ names := by
  obtain ⟨compiled, parsed, _⟩ := LatticeAPI.points_success names (lowerFormula input) points built
  intro name member
  obtain ⟨index, declared⟩ := formula_declared (LatticeInput.variableOf names) true input compiled parsed name member
  exact List.mem_of_getElem? (LatticeAPI.variableOf_lookup names name index declared)

/-- The source integerGroup success discharges its single-value-name convention. -/
theorem points_leafScoped (domain : Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points [SourceGuards.valueName] (lowerFormula domain) = .ok points) :
    OpenIntegerSource.LeafScoped domain := by
  intro name member
  simpa using points_declared [SourceGuards.valueName] domain points built name member

/-- Successful public compilation over reserved coordinate names establishes the OpenKey scope invariant. -/
theorem points_scoped (width : Nat) (formula : Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points (OpenIntegerKeys.names width) (lowerFormula formula) = .ok points) :
    OpenIntegerKeys.Scoped width formula := by
  intro name member
  obtain ⟨index, bound, same⟩ := List.mem_map.mp
    (points_declared (OpenIntegerKeys.names width) formula points built name member)
  exact ⟨index, List.mem_range.mp bound, same.symm⟩

/-- The actual successful finite leaf table gives the exact renamed domain without a scope premise. -/
theorem integerGroup_exact (domain : Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points [SourceGuards.valueName] (lowerFormula domain) = .ok points) (tuple : List Int) :
    tuple ∈ OpenIntegerSource.pointDomain points ↔ tuple.length = 1 ∧
      Holds integerModel (OpenIntegerKeys.tupleEnv tuple)
        (OpenIntegerSource.integerKey domain (some points.count.toNat)).formula :=
  OpenIntegerSource.integerGroup_domain domain (points_leafScoped domain points built) points built tuple

/-- Elimination errors occur after the parser has validated every source name. -/
theorem elimination_declared (names : List Name) (input : Formula) (error : LatticePiece.SplitError)
    (failed : LatticeAPI.points names (lowerFormula input) = .error (.elimination error)) :
    ∀ name ∈ formulaNames input, name ∈ names := by
  cases parsed : LatticeFormula.signed (LatticeInput.variableOf names) true (lowerFormula input) with
  | error parseError => simp [LatticeAPI.points, parsed] at failed
  | ok compiled =>
      intro name member
      obtain ⟨index, declared⟩ := formula_declared (LatticeInput.variableOf names) true input compiled parsed name member
      exact List.mem_of_getElem? (LatticeAPI.variableOf_lookup names name index declared)

/-- Even a retained unbounded integer leaf has validated its original one-variable scope. -/
theorem retained_leafScoped (domain : Formula) (key : OpenIntegerKeys.Key)
    (retained : OpenIntegerSource.integerGroup domain = .ok (some key)) :
    OpenIntegerSource.LeafScoped domain := by
  cases counted : LatticeAPI.points [SourceGuards.valueName] (lowerFormula domain) with
  | ok points => exact points_leafScoped domain points counted
  | error error =>
      cases error with
      | formula _ | nonintegral => simp [OpenIntegerSource.integerGroup, counted] at retained
      | elimination error =>
          cases error with
          | nonUnitCoefficient => simp [OpenIntegerSource.integerGroup, counted] at retained
          | unboundedVariable =>
              intro name member
              simpa using elimination_declared [SourceGuards.valueName] domain .unboundedVariable counted name member

end MicroCFTA.LatticeDeclaredNames
