import MicroCFTA.LatticeFormula
import MicroCFTA.LatticeCount

/-!
# Formula input and initial polynomial pieces

The source maps every signed conjunction to a constant polynomial. Name lookup
uses the first matching position in the given variable list. The following
proofs derive the initial validity, variable support, and indicator semantics.
-/

namespace MicroCFTA.LatticeInput
open LatticeLinear LatticeNormalize LatticeSigned LatticeFormula

/-- Merging coefficient maps introduces no new variable index. -/
theorem addSparse_supported (allowed : Nat → Prop) (left right : List (Nat × Int))
    (hl : ∀ entry ∈ left, allowed entry.1) (hr : ∀ entry ∈ right, allowed entry.1) :
    ∀ entry ∈ Sparse.addSparse left right, allowed entry.1 := by
  fun_induction Sparse.addSparse left right with
  | case1 => exact hr
  | case2 => exact hl
  | case3 ls lv left rs rv right h ih =>
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact hl (ls, lv) (by simp)
    · exact ih (fun entry member => hl entry (by simp [member])) hr entry member
  | case4 ls lv left rs rv right h h' ih =>
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact hr (rs, rv) (by simp)
    · exact ih hl (fun entry member => hr entry (by simp [member])) entry member
  | case5 ls lv left rs rv right h h' ih =>
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact hl (ls, lv) (by simp)
    · exact ih (fun entry member => hl entry (by simp [member]))
        (fun entry member => hr entry (by simp [member])) entry member

/-- Linear addition stays in the combined source variable universe. -/
theorem plus_supported (allowed : Nat → Prop) (left right : Linear)
    (hl : Supported allowed left) (hr : Supported allowed right) : Supported allowed (plus left right) := by
  intro entry member
  exact addSparse_supported allowed left.coefficients right.coefficients hl hr entry
    (List.mem_filter.mp member).1

/-- Scalar multiplication introduces no new variable indices. -/
theorem scale_supported (allowed : Nat → Prop) (factor : Int) (form : Linear)
    (supported : Supported allowed form) : Supported allowed (scale factor form) := by
  by_cases zero : factor = 0
  · simp [scale, zero, constant, Supported]
  · intro entry member
    simp only [scale, zero, ↓reduceIte] at member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact supported original present

/-- A constant uses no variable. -/
theorem constant_supported (allowed : Nat → Prop) (value : Int) : Supported allowed (constant value) := by
  simp [Supported, constant]

/-- Linear subtraction stays in the combined source variable universe. -/
theorem minus_supported (allowed : Nat → Prop) (left right : Linear)
    (hl : Supported allowed left) (hr : Supported allowed right) : Supported allowed (minus left right) :=
  plus_supported allowed left _ hl (scale_supported allowed (-1) right hr)

/-- A successful constant-times-linear parse introduces no variable. -/
theorem multiplyLinear_supported (allowed : Nat → Prop) (left right result : Linear)
    (hl : Supported allowed left) (hr : Supported allowed right)
    (success : multiplyLinear (Name := Name) left right = .ok result) : Supported allowed result := by
  unfold multiplyLinear at success
  split at success
  · cases success; exact scale_supported allowed _ right hr
  · split at success
    · cases success; exact scale_supported allowed _ left hl
    · cases success

attribute [local simp] LatticeLinear.except_bind_ok LatticeLinear.except_bind_error
  LatticeLinear.except_map_ok LatticeLinear.except_map_error Except.map

/-- Parsed linear terms use only the indices supplied by name lookup. -/
theorem linearTerm_supported (allowed : Nat → Prop) (variableOf : Name → Option Nat)
    (lookup : ∀ name index, variableOf name = some index → allowed index)
    (expression : Expr Name) (result : Linear) (success : linearTerm variableOf expression = .ok result) :
    Supported allowed result := by
  induction expression generalizing result with
  | integer value => simp [linearTerm] at success; subst result; exact constant_supported allowed value
  | name identifier =>
    cases found : variableOf identifier with
    | none => simp [linearTerm, found] at success
    | some index =>
      simp [linearTerm, found] at success
      subst result
      simpa [Supported] using lookup identifier index found
  | neg inner ih =>
    cases parsed : linearTerm variableOf inner with
    | error error => simp [linearTerm, parsed] at success
    | ok form =>
      simp [linearTerm, parsed] at success
      subst result
      exact scale_supported allowed _ form (ih form parsed)
  | cast inner ih => exact ih result success
  | add left right ihl ihr =>
    cases lhs : linearTerm variableOf left <;> cases rhs : linearTerm variableOf right <;>
      simp [linearTerm, lhs, rhs] at success
    subst result
    exact plus_supported allowed _ _ (ihl _ lhs) (ihr _ rhs)
  | sub left right ihl ihr =>
    cases lhs : linearTerm variableOf left <;> cases rhs : linearTerm variableOf right <;>
      simp [linearTerm, lhs, rhs] at success
    subst result
    exact minus_supported allowed _ _ (ihl _ lhs) (ihr _ rhs)
  | mul left right ihl ihr =>
    cases lhs : linearTerm variableOf left <;> cases rhs : linearTerm variableOf right <;>
      simp [linearTerm, lhs, rhs] at success
    exact multiplyLinear_supported allowed _ _ result (ihl _ lhs) (ihr _ rhs) success
  | unsupported => simp [linearTerm] at success

/-- Every conjunction in a signed table stays in one finite variable universe. -/
def Fits (allowed : Nat → Prop) (terms : Signed) : Prop :=
  ∀ entry ∈ terms, ∀ form ∈ entry.1, Supported allowed form

/-- Simplification preserves the variable universe derived from parsed terms. -/
theorem simplify_fits (allowed : Nat → Prop) (terms : Signed) (valid : ValidSigned terms)
    (fits : Fits allowed terms) : Fits allowed (simplify terms valid) :=
  simplify_property _ terms valid (fun entry member forms success =>
    normalize_supported allowed entry.1 (fits entry member) forms success)

/-- A single conjunction retains its variable universe. -/
theorem single_fits (allowed : Nat → Prop) (forms : List Linear)
    (valid : ∀ form ∈ forms, Valid form) (fits : ∀ form ∈ forms, Supported allowed form) :
    Fits allowed (single forms valid).terms := by
  apply simplify_fits
  simpa [Fits] using fits

/-- Cartesian conjunction uses only the variables of its input keys. -/
theorem product_fits (allowed : Nat → Prop) (left right : Signed) (hl : Fits allowed left) (hr : Fits allowed right) :
    Fits allowed (product left right) := by
  intro entry member form present
  obtain ⟨leftEntry, leftMember, row⟩ := List.mem_flatMap.mp member
  obtain ⟨rightEntry, rightMember, rfl⟩ := List.mem_map.mp row
  rcases List.mem_append.mp present with leftPresent | rightPresent
  · exact hl leftEntry leftMember form leftPresent
  · exact hr rightEntry rightMember form rightPresent

/-- Checked conjunction preserves variable support. -/
theorem conjoin_fits (allowed : Nat → Prop) (left right : Checked)
    (hl : Fits allowed left.terms) (hr : Fits allowed right.terms) : Fits allowed (conjoin left right).terms :=
  simplify_fits allowed _ _ (product_fits allowed _ _ hl hr)

/-- Coefficient negation changes no variable indices. -/
theorem negate_fits (allowed : Nat → Prop) (terms : Signed) (fits : Fits allowed terms) :
    Fits allowed (negate terms) := by
  intro entry member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact fits original present

/-- Appended signed maps stay within the common variable universe. -/
theorem append_fits (allowed : Nat → Prop) (left right : Signed) (hl : Fits allowed left) (hr : Fits allowed right) :
    Fits allowed (left ++ right) := by
  intro entry member
  rcases List.mem_append.mp member with member | member
  · exact hl entry member
  · exact hr entry member

/-- Checked disjunction preserves variable support through its overlap subtraction. -/
theorem disjoin_fits (allowed : Nat → Prop) (left right : Checked)
    (hl : Fits allowed left.terms) (hr : Fits allowed right.terms) : Fits allowed (disjoin left right).terms :=
  simplify_fits allowed _ _ (append_fits allowed _ _ (append_fits allowed _ _ hl hr)
    (negate_fits allowed _ (conjoin_fits allowed left right hl hr)))

/-- Atomic relations use only the difference's variables. -/
theorem atom_fits (allowed : Nat → Prop) (relation : Relation) (difference : Linear)
    (valid : Valid difference) (fits : Supported allowed difference) :
    Fits allowed (LatticeSigned.atom relation difference valid).terms := by
  have positive := single_fits allowed [difference] (by simpa using valid) (by simpa using fits)
  have negative := single_fits allowed [scale (-1) difference]
    (by simpa using scale_valid (-1) difference valid)
    (by simpa using scale_supported allowed (-1) difference fits)
  have strictPositive := single_fits allowed [minus difference (constant 1)]
    (by simpa using minus_valid difference (constant 1) valid (constant_valid 1))
    (by simpa using minus_supported allowed difference (constant 1) fits (constant_supported allowed 1))
  have strictNegative := single_fits allowed [minus (scale (-1) difference) (constant 1)]
    (by simpa using minus_valid _ (constant 1) (scale_valid (-1) difference valid) (constant_valid 1))
    (by simpa using minus_supported allowed _ (constant 1)
          (scale_supported allowed (-1) difference fits) (constant_supported allowed 1))
  cases relation with
  | le => exact positive
  | lt => exact strictPositive
  | ge => exact negative
  | gt => exact strictNegative
  | eq | ueq =>
    apply single_fits
    · intro form member
      rcases List.mem_cons.mp member with rfl | member
      · exact valid
      · have same : form = scale (-1) difference := by simpa using member
        subst form
        exact scale_valid (-1) difference valid
    · intro form member
      rcases List.mem_cons.mp member with rfl | member
      · exact fits
      · have same : form = scale (-1) difference := by simpa using member
        subst form
        exact scale_supported allowed (-1) difference fits
  | ne | une => exact disjoin_fits allowed _ _ strictPositive strictNegative

/-- Certificate-retaining arithmetic parsing preserves variable support. -/
theorem parseTerm_fits (allowed : Nat → Prop) (variableOf : Name → Option Nat)
    (lookup : ∀ name index, variableOf name = some index → allowed index)
    (expression : Expr Name) (result : { form : Linear // Valid form })
    (success : parseTerm variableOf expression = .ok result) : Supported allowed result.val := by
  unfold parseTerm at success
  split at success
  · cases success
  · next form parsed => cases success; exact linearTerm_supported allowed variableOf lookup expression form parsed

/-- Parsed atoms use only declared variable indices. -/
theorem parseAtom_fits (allowed : Nat → Prop) (variableOf : Name → Option Nat)
    (lookup : ∀ name index, variableOf name = some index → allowed index)
    (positive : Bool) (relation : Relation) (left right : Expr Name) (result : Checked)
    (success : parseAtom variableOf positive relation left right = .ok result) : Fits allowed result.terms := by
  cases rhs : parseTerm variableOf right <;> cases lhs : parseTerm variableOf left <;>
    simp [parseAtom, rhs, lhs] at success
  cases success
  apply atom_fits
  exact minus_supported allowed _ _ (parseTerm_fits allowed variableOf lookup right _ rhs)
    (parseTerm_fits allowed variableOf lookup left _ lhs)

/-- All successful formula compilation stays within the declared variable universe. -/
theorem signed_fits (allowed : Nat → Prop) (variableOf : Name → Option Nat)
    (lookup : ∀ name index, variableOf name = some index → allowed index)
    (formula : Formula Name) (positive : Bool) (result : Checked)
    (success : signed variableOf positive formula = .ok result) : Fits allowed result.terms := by
  induction formula generalizing positive result with
  | atom relation left right => exact parseAtom_fits allowed variableOf lookup positive relation left right result success
  | top =>
    simp [signed] at success; cases success
    cases positive <;> simp [always, never, Fits]
  | bottom =>
    simp [signed] at success; cases success
    cases positive <;> simp [always, never, Fits]
  | conj left right ihl ihr =>
    cases lhs : signed variableOf positive left <;> cases rhs : signed variableOf positive right <;>
      simp [signed, lhs, rhs] at success
    cases success
    cases positive
    · exact disjoin_fits allowed _ _ (ihl _ _ lhs) (ihr _ _ rhs)
    · exact conjoin_fits allowed _ _ (ihl _ _ lhs) (ihr _ _ rhs)
  | disj left right ihl ihr =>
    cases lhs : signed variableOf positive left <;> cases rhs : signed variableOf positive right <;>
      simp [signed, lhs, rhs] at success
    cases success
    cases positive
    · exact conjoin_fits allowed _ _ (ihl _ _ lhs) (ihr _ _ rhs)
    · exact disjoin_fits allowed _ _ (ihl _ _ lhs) (ihr _ _ rhs)
  | neg inner ih => exact ih (!positive) result success
  | imp premise conclusion ihp ihc =>
    cases lhs : signed variableOf (!positive) premise <;> cases rhs : signed variableOf positive conclusion <;>
      simp [signed, lhs, rhs] at success
    cases success
    cases positive
    · exact conjoin_fits allowed _ _ (ihp _ _ lhs) (ihc _ _ rhs)
    · exact disjoin_fits allowed _ _ (ihp _ _ lhs) (ihc _ _ rhs)
  | iff left right ihl ihr =>
    cases lp : signed variableOf true left <;> cases rp : signed variableOf positive right <;>
      cases ln : signed variableOf false left <;> cases rn : signed variableOf (!positive) right <;>
      simp [signed, lp, rp, ln, rn] at success
    cases success
    exact disjoin_fits allowed _ _ (conjoin_fits allowed _ _ (ihl _ _ lp) (ihr _ _ rp))
      (conjoin_fits allowed _ _ (ihl _ _ ln) (ihr _ _ rn))
  | cast inner ih => exact ih positive result success
  | unsupported => simp [signed] at success

/-- Read the first matching name index, as the source's `elemIndex` does. -/
def variableOf [DecidableEq Name] : List Name → Name → Option Nat
  | [], _ => none
  | first :: rest, name => if name = first then some 0 else (variableOf rest name).map Nat.succ

/-- Every declared name maps to a coordinate inside the source dimension. -/
theorem variableOf_lt [DecidableEq Name] (names : List Name) (name : Name) (index : Nat)
    (found : variableOf names name = some index) : index < names.length := by
  induction names generalizing index with
  | nil => simp [variableOf] at found
  | cons first rest ih =>
    by_cases same : name = first
    · simp [variableOf, same] at found; subst index; simp
    · cases tail : variableOf rest name with
      | none => simp [variableOf, same, tail] at found
      | some old =>
        simp [variableOf, same, tail] at found
        subst index
        exact Nat.succ_lt_succ (ih old tail)

/-- Interpret declared names through their selected coordinates. -/
def nameValues [DecidableEq Name] (names : List Name) (assignment : Nat → Int) (name : Name) : Int :=
  ((variableOf names name).map assignment).getD 0

/-- Name interpretation satisfies the parser environment without an external premise. -/
theorem nameValues_correct [DecidableEq Name] (names : List Name) (assignment : Nat → Int)
    (name : Name) (index : Nat) (found : variableOf names name = some index) :
    nameValues names assignment name = assignment index := by simp [nameValues, found]

/-- Turn one signed conjunction into the source's constant polynomial piece. -/
def initialPiece (entry : List Linear × Int) : LatticePiece.Piece :=
  ⟨entry.1, LatticePolynomial.polynomialConstant (entry.2 : Rat)⟩

/-- Initialize all counting pieces from the compiled signed map. -/
def initial (compiled : Checked) : List LatticePiece.Piece := compiled.terms.map initialPiece

/-- A constant polynomial has valid ordered monomials. -/
theorem constant_ordered (value : Rat) : LatticePolynomial.OrderedMonomials (LatticePolynomial.polynomialConstant value) := by
  apply LatticePolynomial.normalize_ordered
  simp [LatticePolynomial.OrderedMonomials, LatticePolynomial.OrderedMonomial]

/-- Initial piece validity is derived from signed compilation. -/
theorem initial_valid (compiled : Checked) : ∀ piece ∈ initial compiled, LatticePiece.ValidPiece piece := by
  intro piece member
  obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
  exact ⟨compiled.valid entry present, constant_ordered _⟩

/-- Initial terminal metadata is already established by signed normalization. -/
theorem initial_metadata (compiled : Checked) : ∀ piece ∈ initial compiled, LatticeCount.TerminalMetadata piece := by
  intro piece member
  obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
  exact ⟨compiled.nonconstant entry present, LatticePolynomial.normalize_unique _⟩

/-- One initial polynomial piece contributes its integer signed score exactly. -/
theorem initialPiece_value (assignment : Nat → Int) (entry : List Linear × Int) :
    LatticePiece.pieceValue assignment (initialPiece entry) =
      ((entry.2 * Lattice.indicator (region assignment entry.1) : Int) : Rat) := by
  simp only [initialPiece, LatticePiece.pieceValue, LatticePolynomial.evaluate_constant]
  change (if region assignment entry.1 then (entry.2 : Rat) else 0) = _
  cases region assignment entry.1 <;> simp [Lattice.indicator]

/-- Initial polynomial evaluation is exactly the compiled signed indicator. -/
theorem initial_total (assignment : Nat → Int) (compiled : Checked) :
    LatticeCount.total (initial compiled) assignment = (score assignment compiled.terms : Rat) := by
  unfold initial LatticeCount.total
  induction compiled.terms with
  | nil => simp [FiniteSum.listSum, score]
  | cons entry rest ih =>
    simp only [List.map_cons, FiniteSum.listSum, initialPiece_value, ih, score]
    simp

/-- Formula parsing establishes the natural zero-or-one initial count at every assignment. -/
theorem initial_indicator [DecidableEq Name] (names : List Name) (formula : Formula Name)
    (compiled : Checked) (success : signed (variableOf names) true formula = .ok compiled)
    (assignment : Nat → Int) :
    ∃ value, evaluateFormula (nameValues names assignment) formula = some value ∧
      LatticeCount.total (initial compiled) assignment = (if value then 1 else 0) := by
  obtain ⟨value, interpreted, counted⟩ := signed_indicator (variableOf names) (nameValues names assignment)
    assignment (nameValues_correct names assignment) formula compiled success
  refine ⟨value, interpreted, ?_⟩
  rw [initial_total, counted]
  cases value <;> rfl

/-- The elimination order covers every variable that occurs in an initial piece. -/
theorem initial_covers [DecidableEq Name] (names : List Name) (formula : Formula Name)
    (compiled : Checked) (success : signed (variableOf names) true formula = .ok compiled) :
    ∀ index, index ∈ (List.range names.length).reverse ∨
      ∀ piece ∈ initial compiled, LatticePipeline.FreePiece index piece := by
  have fits := signed_fits (fun index => index < names.length) (variableOf names)
    (variableOf_lt names) formula true compiled success
  intro index
  by_cases within : index < names.length
  · exact Or.inl (by simp [within])
  · apply Or.inr
    intro piece member
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    constructor
    · intro form occurs coefficient member same
      have bound := fits entry present form occurs coefficient member
      exact within (same ▸ bound)
    · exact PolynomialSupport.constant_free index _

/-- Successful full elimination computes the iterated sum of the formula's exact indicator. -/
theorem count_correct [DecidableEq Name] (names : List Name) (formula : Formula Name)
    (compiled : Checked) (parsed : signed (variableOf names) true formula = .ok compiled)
    (output : List LatticePiece.Piece)
    (success : LatticeCount.sumOut (List.range names.length).reverse (initial compiled) (initial_valid compiled) = .ok output) :
    LatticeCount.SumsOut (List.range names.length).reverse (LatticeCount.total (initial compiled))
      (fun _ => LatticeCount.polynomialCount output) := by
  have summed := LatticeCount.sumOut_correct _ _ (initial_valid compiled) output success
  have equal : (fun _ : Nat → Int => LatticeCount.polynomialCount output) = LatticeCount.total output := by
    funext assignment
    exact LatticeCount.polynomialCount_correct assignment _ _ (initial_valid compiled) (initial_metadata compiled)
      (initial_covers names formula compiled parsed) output success
  rwa [equal]

/-- The source's final rational count is an integer and is nonnegative. -/
theorem count_natural [DecidableEq Name] (names : List Name) (formula : Formula Name)
    (compiled : Checked) (parsed : signed (variableOf names) true formula = .ok compiled)
    (output : List LatticePiece.Piece)
    (success : LatticeCount.sumOut (List.range names.length).reverse (initial compiled) (initial_valid compiled) = .ok output) :
    ∃ count : Nat, LatticeCount.polynomialCount output = (count : Rat) := by
  apply LatticeCount.polynomialCount_natural _ _ (initial_valid compiled) (initial_metadata compiled)
    (initial_covers names formula compiled parsed) output success
  intro assignment
  obtain ⟨value, _, counted⟩ := initial_indicator names formula compiled parsed assignment
  cases value
  · exact ⟨0, counted⟩
  · exact ⟨1, counted⟩

end MicroCFTA.LatticeInput
