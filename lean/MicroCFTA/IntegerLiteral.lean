import MicroCFTA.LatticeSingleton

/-! Exact source singleton queries for generated integer labels. -/
namespace MicroCFTA.IntegerLiteral
open LatticeLinear LatticeSigned

/-- The refinement attached to a generated integer leaf. -/
def refinement (name : String) (value : Int) : FullSyntax.Formula := .atom .eq (.var name) (.lit value)

/-- Upper integer inequality: the chosen coordinate is at most the literal. -/
def upper (value : Int) : Linear := ⟨[(0, -1)], value⟩
/-- Lower integer inequality: the chosen coordinate is at least the literal. -/
def lower (value : Int) : Linear := ⟨[(0, 1)], -value⟩

theorem normalize_pair (value : Int) :
    LatticeNormalize.normalize [upper value, lower value] = some [lower value, upper value] := by
  simp [upper, lower, LatticeNormalize.normalize, LatticeNormalize.reduceAll, LatticeNormalize.reduce,
    LatticeNormalize.reduceByGcd, LatticeNormalize.divisor, LatticeNormalize.divideCoefficients,
    LatticeNormalize.tighten, LatticeNormalize.insertTightest, LatticeNormalize.hasContradiction,
    LatticeNormalize.contradicts, LatticeNormalize.opposite]
  omega

theorem upper_valid (value : Int) : Valid (upper value) := by simp [upper, Valid, Sparse.Ordered]

/-- The actual signed atom compiler applied to the literal equality. -/
def compiled (value : Int) : Checked := atom .eq (upper value) (upper_valid value)

theorem parseTerm_eq (variableOf : String → Option Nat) (expression : Expr String) (form : Linear)
    (valid : Valid form) (success : linearTerm variableOf expression = .ok form) :
    LatticeFormula.parseTerm variableOf expression = .ok ⟨form, valid⟩ := by
  unfold LatticeFormula.parseTerm
  split
  · rename_i error failed
    rw [success] at failed
    cases failed
  · rename_i actual found
    have same := Except.ok.inj (found.symm.trans success)
    subst actual
    rfl

theorem parsed_exact (name : String) (value : Int) :
    LatticeFormula.signed (LatticeInput.variableOf [name]) true
      (FullSyntax.lowerFormula (refinement name value)) = .ok (compiled value) := by
  have found : LatticeInput.variableOf [name] name = some 0 := by simp [LatticeInput.variableOf]
  have left : linearTerm (LatticeInput.variableOf [name]) (.name name) = .ok (⟨[(0, 1)], 0⟩ : Linear) := by
    simp [linearTerm, found]
  have right : linearTerm (LatticeInput.variableOf [name]) (.integer value) = .ok (constant value) := rfl
  have hl := parseTerm_eq _ _ _ (by simp [Valid, Sparse.Ordered]) left
  have hr := parseTerm_eq _ _ _ (constant_valid value) right
  simp only [refinement, FullSyntax.lowerFormula, FullSyntax.lowerTerm, CoreLattice.lowerRelation,
    LatticeFormula.signed, LatticeFormula.parseAtom, hl, hr, Bind.bind, Except.bind, ↓reduceIte]
  have difference : minus (constant value) ⟨[(0, 1)], 0⟩ = upper value := by
    simp [minus, plus, scale, constant, upper, LatticeLinear.removeZeros, Sparse.addSparse]
  simp only [difference, compiled]

theorem normalized_valid (value : Int) : ∀ form ∈ [lower value, upper value], Valid form := by
  intro form member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simp [lower, Valid, Sparse.Ordered]
  · exact upper_valid value

theorem normalized_feasible (value : Int) (valid : ∀ form ∈ [lower value, upper value], Valid form) :
    LatticeFeasible.feasible [lower value, upper value] valid = true := by
  apply LatticeFeasible.feasible_of_satisfies _ valid (fun _ => value)
  simp [LatticeNormalize.Satisfies, lower, upper, evaluate, evalCoefficients]
  omega

theorem compiled_terms (value : Int) : (compiled value).terms = [([lower value, upper value], 1)] := by
  have opposite : scale (-1) (upper value) = lower value := by simp [scale, upper, lower]
  simp only [compiled, atom, single, checked, opposite, simplify]
  unfold prepare
  split
  · rename_i missing
    rw [normalize_pair] at missing
    cases missing
  · rename_i actual found
    have same := Option.some.inj (found.symm.trans (normalize_pair value))
    subst actual
    simp [normalized_feasible, prepare, LatticeSigned.merge, LatticeSigned.insert, LatticeSigned.removeZeros]

/-- The one retained region and its constant indicator weight. -/
def piece (value : Int) : LatticePiece.Piece :=
  ⟨[lower value, upper value], LatticePolynomial.polynomialConstant 1⟩

theorem initial_eq (value : Int) : LatticeInput.initial (compiled value) = [piece value] := by
  simp [LatticeInput.initial, compiled_terms, LatticeInput.initialPiece, piece]

theorem bounds (value : Int) :
    LatticePiece.collectBounds 0 (LatticePiece.involved 0 (piece value).constraints) =
      .ok ([constant value], [constant value]) := by
  simp [piece, lower, upper, LatticePiece.involved, LatticeBound.mentions, LatticePiece.collectBounds,
    LatticeBound.bound, LatticeBound.coefficientOf, Sparse.valueAtSize, LatticeBound.deleteVariable,
    scale, constant, Bind.bind, Except.bind]

theorem split_exists (value : Int) (valid : LatticePiece.ValidPiece (piece value)) :
    ∃ output, LatticePipeline.splitFull 0 (piece value) valid = .ok output := by
  have raw : ∃ output, LatticePiece.splitRaw 0 (piece value) = .ok output := by
    simp only [LatticePiece.splitRaw, bounds, List.isEmpty_cons, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, rfl⟩
  obtain ⟨output, found⟩ := raw
  unfold LatticePipeline.splitFull
  split
  · rename_i error failed
    rw [found] at failed
    cases failed
  · exact ⟨_, rfl⟩

/-- Generated integer equality always has a successful finite elimination table. -/
theorem levels_exist (value : Int) : ∃ levels, LatticeLevels.buildLevels 1 (LatticeInput.initial (compiled value))
    (LatticeInput.initial_valid (compiled value)) = .ok levels := by
  have valid : LatticePiece.ValidPiece (piece value) :=
    LatticeInput.initial_valid (compiled value) _ (by simp [initial_eq])
  obtain ⟨split, found⟩ := split_exists value valid
  have eliminated : ∃ output, LatticeCount.eliminate 0 (LatticeInput.initial (compiled value))
      (LatticeInput.initial_valid (compiled value)) = .ok output := by
    generalize proof : LatticeInput.initial_valid (compiled value) = canonical
    clear proof
    revert canonical
    rw [initial_eq]
    intro canonical
    simp only [LatticeCount.eliminate, found, Bind.bind, Except.bind, List.append_nil]
    exact ⟨_, rfl⟩
  obtain ⟨output, eliminated⟩ := eliminated
  unfold LatticeLevels.buildLevels
  split
  · rename_i error failed
    rw [eliminated] at failed
    cases failed
  · exact ⟨_, rfl⟩

/-- The public counter succeeds for every integer value emitted by the compiler. -/
theorem points_exist (name : String) (value : Int) :
    ∃ result, LatticeAPI.points [name] (FullSyntax.lowerFormula (refinement name value)) = .ok result := by
  obtain ⟨levels, built⟩ := levels_exist value
  exact ⟨_, LatticeAPI.points_of_build [name] _ (compiled value) (parsed_exact name value) levels built⟩

theorem admits_iff (name : String) (value other : Int) :
    LatticeSingleton.Admits name (refinement name value) other ↔ other = value := by
  simp [LatticeSingleton.Admits, refinement, FullSyntax.Holds, FullSyntax.evaluateTerm,
    FullSyntax.integerModel, CoreFormula.evalRelation, LatticeInput.nameValues,
    LatticeInput.variableOf, LatticeSelect.assignTuple, LatticeBound.update]

/-- The actual onlyPoint implementation reads every canonical integer label exactly. -/
theorem onlyPoint_literal (name : String) (value : Int) :
    LatticeSingleton.onlyPoint name (refinement name value) = some value := by
  obtain ⟨result, success⟩ := points_exist name value
  exact LatticeSingleton.onlyPoint_complete name _ value result success
    ((admits_iff name value value).mpr rfl) (fun other accepted => (admits_iff name value other).mp accepted)

end MicroCFTA.IntegerLiteral
