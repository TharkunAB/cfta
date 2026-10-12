import MicroCFTA.RecipeCompile
import MicroCFTA.LatticeSingleton

/-!
# Integer coordinates in filled outcome terms

The source extracts coordinates only at the original placeholder leaves.
All other symbols are checked later by equality with the complete rewritten
term. The traversal below follows `pointsStatic.holes` and `holesIn`.
-/
namespace MicroCFTA.IntegerTermCodec
open Language RecipeCompile

deriving instance DecidableEq for FillLabel

/-- The integer constructor creates a placeholder leaf, never a placeholder parent. -/
def LeafHoles : Term (FillLabel Symbol) → Prop
  | .node label children => (label = .placeholder → children = []) ∧ ∀ child ∈ children, LeafHoles child

mutual
/-- Extract one filled symbol for each original placeholder leaf. Other labels are checked by the caller. -/
def holeSymbols : Term (FillLabel Symbol) → Term (FillLabel Symbol) → Option (List Symbol)
  | .node .placeholder [], .node (.user symbol) [] => some [symbol]
  | .node _ children, .node _ filled => holesIn children filled
termination_by original _ => sizeOf original

/-- Source length alignment and left-to-right extraction, with failure on an arity mismatch. -/
def holesIn : List (Term (FillLabel Symbol)) → List (Term (FillLabel Symbol)) → Option (List Symbol)
  | [], [] => some []
  | original :: rest, filled :: tail => do
      let first ← holeSymbols original filled
      let others ← holesIn rest tail
      pure (first ++ others)
  | _, _ => none
termination_by originals _ => sizeOf originals
end

mutual
/-- The actual source extraction recovers precisely the prefix consumed by hole filling. -/
theorem holeSymbols_fill (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (term : Term (FillLabel Symbol)) (valid : LeafHoles term)
    (enough : holes term ≤ point.length) :
    holeSymbols term (fillTerm literal exactLabel point term).2 = some ((point.take (holes term)).map literal) := by
  cases term with
  | node label children =>
      simp only [LeafHoles] at valid
      cases label with
      | placeholder =>
          have empty := valid.1 rfl
          subst children
          cases point with
          | nil => simp [holes] at enough
          | cons value rest => simp [fillTerm, holeSymbols, holes]
      | user symbol =>
          simp only [fillTerm, holeSymbols, holes]
          exact holesIn_fill literal exactLabel point children valid.2 (by simpa [holes] using enough)
      | internal tag =>
          simp only [fillTerm, holeSymbols, holes]
          exact holesIn_fill literal exactLabel point children valid.2 (by simpa [holes] using enough)
termination_by sizeOf term

/-- Consecutive child subtrees extract successive coordinate prefixes without permutation. -/
theorem holesIn_fill (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (terms : List (Term (FillLabel Symbol)))
    (valid : ∀ term ∈ terms, LeafHoles term) (enough : forestHoles terms ≤ point.length) :
    holesIn terms (fillForest literal exactLabel point terms).2 = some ((point.take (forestHoles terms)).map literal) := by
  cases terms with
  | nil => simp [fillForest, holesIn, forestHoles]
  | cons term rest =>
      have firstEnough : holes term ≤ point.length := by simp only [forestHoles] at enough; omega
      have tailEnough : forestHoles rest ≤ (point.drop (holes term)).length := by
        rw [List.length_drop]
        simp only [forestHoles] at enough
        omega
      simp only [fillForest, holesIn,
        holeSymbols_fill literal exactLabel point term (valid term (by simp)) firstEnough,
        fillTerm_remaining, forestHoles]
      rw [holesIn_fill literal exactLabel _ rest (fun term member => valid term (by simp [member])) tailEnough]
      simp only [Bind.bind, Option.bind, Pure.pure]
      rw [← List.map_append, ← List.take_add]
termination_by sizeOf terms
end

/-- The exact hole count derives the complete extracted coordinate list. -/
theorem exact_symbols (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (term : Term (FillLabel Symbol)) (valid : LeafHoles term)
    (dimension : point.length = holes term) :
    holeSymbols term (fillTerm literal exactLabel point term).2 = some (point.map literal) := by
  simpa [← dimension] using holeSymbols_fill literal exactLabel point term valid (by omega)

/-- The source rankPoint reader traverses extracted leaf refinements in their original order. -/
def readSymbols (read : Symbol → Option Int) : List Symbol → Option (List Int)
  | [] => some []
  | symbol :: rest => do
      let value ← read symbol
      let values ← readSymbols read rest
      pure (value :: values)

theorem read_literals (literal : Int → Symbol) (read : Symbol → Option Int)
    (literalRead : ∀ value, read (literal value) = some value) (point : List Int) :
    readSymbols read (point.map literal) = some point := by
  induction point with
  | nil => rfl
  | cons value rest ih => simp [readSymbols, literalRead, ih]

/-- Extract and read the tuple at the source placeholder positions. -/
def readPoint (read : Symbol → Option Int) (original filled : Term (FillLabel Symbol)) : Option (List Int) := do
  let symbols ← holeSymbols original filled
  readSymbols read symbols

/-- Filling and reading are inverse operations; no term-codec inverse is assumed. -/
theorem read_fill (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (point : List Int) (term : Term (FillLabel Symbol)) (valid : LeafHoles term)
    (dimension : point.length = holes term) : readPoint read term (fillTerm literal exactLabel point term).2 = some point := by
  simp only [readPoint, exact_symbols literal exactLabel point term valid dimension]
  exact read_literals literal read literalRead point

/-- Distinct tuples cannot collapse to the same filled term, even if user-label specialization is noninjective. -/
theorem fill_injective (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (term : Term (FillLabel Symbol)) (valid : LeafHoles term) (left right : List Int)
    (leftSize : left.length = holes term) (rightSize : right.length = holes term)
    (same : (fillTerm literal exactLabel left term).2 = (fillTerm literal exactLabel right term).2) : left = right := by
  have equal := congrArg (readPoint read term) same
  rw [read_fill literal exactLabel read literalRead left term valid leftSize,
    read_fill literal exactLabel read literalRead right term valid rightSize] at equal
  exact Option.some.inj equal

/-- The source reader split at a product agrees with its left and right hole counts. -/
theorem product_split (left right : List Int) :
    (left ++ right).take left.length = left ∧ (left ++ right).drop left.length = right := by simp

/-- An enclosing label receives the whole remaining point; each child consumes only its own prefix. -/
theorem forest_split (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (first : Term (FillLabel Symbol)) (rest : List (Term (FillLabel Symbol))) :
    fillForest literal exactLabel point (first :: rest) =
      let front := fillTerm literal exactLabel point first
      let tail := fillForest literal exactLabel (point.drop (holes first)) rest
      (tail.1, front.2 :: tail.2) := by simp only [fillForest, fillTerm_remaining]

/-- One original outcome's whole-term ranker, including the source's final full-term check. -/
def rankTerm [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (points : LatticeAPI.Points)
    (original wanted : Term (FillLabel Symbol)) : Option Nat := do
  let point ← readPoint read original wanted
  let rank ← LatticeSelect.rankFrom points.levels points.dimension 0 (fun _ => 0) point
  if Language.termEq (fillTerm literal exactLabel point original).2 wanted then some rank else none

/-- Decode a valid tuple rank and fill this fixed original outcome. -/
def decodeTerm (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (points : LatticeAPI.Points) (original : Term (FillLabel Symbol))
    (rank : Fin (LatticeSelect.pointCount points.levels)) : Term (FillLabel Symbol) :=
  (fillTerm literal exactLabel (LatticeSelect.decode points.dimension points.levels rank) original).2

/-- The public lattice constructor gives the exact tuple rank used by the term ranker. -/
theorem public_rank_decode (names : List FullSyntax.Name) (formula : FullSyntax.Formula)
    (points : LatticeAPI.Points)
    (success : LatticeAPI.points names (FullSyntax.lowerFormula formula) = .ok points)
    (rank : Fin (LatticeSelect.pointCount points.levels)) :
    LatticeSelect.rankFrom points.levels points.dimension 0 (fun _ => 0)
      (LatticeSelect.decode points.dimension points.levels rank) = some rank.val := by
  obtain ⟨compiled, parsed, built, dimension, _⟩ :=
    LatticeAPI.points_success names (FullSyntax.lowerFormula formula) points success
  obtain ⟨core, _, coreParsed⟩ := FullSyntax.signed_success_is_core _ true formula compiled parsed
  rw [dimension]
  exact (LatticeSelect.decode_defined names core compiled coreParsed points.levels built rank).2

/-- Decoding and ranking the rewritten term are inverse at every valid public lattice rank. -/
theorem rank_decode [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (names : List FullSyntax.Name) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (success : LatticeAPI.points names (FullSyntax.lowerFormula formula) = .ok points)
    (original : Term (FillLabel Symbol)) (valid : LeafHoles original)
    (dimension : holes original = names.length) (rank : Fin (LatticeSelect.pointCount points.levels)) :
    rankTerm literal exactLabel read points original (decodeTerm literal exactLabel points original rank) = some rank.val := by
  have table := LatticeSelect.points_api_exact names formula points success
  have tupleSize : (LatticeSelect.decode points.dimension points.levels rank).length = holes original :=
    ((table.2.2.1 _).mpr ⟨rank, rfl⟩).1.trans dimension.symm
  simp only [rankTerm, decodeTerm,
    read_fill literal exactLabel read literalRead _ original valid tupleSize, Bind.bind, Option.bind]
  rw [public_rank_decode names formula points success rank]
  simp [Language.termEq_correct]

/-- A fixed well-formed outcome has distinct filled terms at every lattice rank. -/
theorem decode_injective [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (names : List FullSyntax.Name) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (success : LatticeAPI.points names (FullSyntax.lowerFormula formula) = .ok points)
    (original : Term (FillLabel Symbol)) (valid : LeafHoles original) (dimension : holes original = names.length) :
    Function.Injective (decodeTerm literal exactLabel points original) := by
  intro left right same
  have equal := congrArg (rankTerm literal exactLabel read points original) same
  rw [rank_decode literal exactLabel read literalRead names formula points success original valid dimension left,
    rank_decode literal exactLabel read literalRead names formula points success original valid dimension right] at equal
  exact Fin.ext (Option.some.inj equal)

/-- A successful whole-term rank retains both coordinate extraction and every rewritten symbol check. -/
theorem rankTerm_success [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (points : LatticeAPI.Points)
    (original wanted : Term (FillLabel Symbol)) (rank : Nat)
    (ranked : rankTerm literal exactLabel read points original wanted = some rank) :
    ∃ point, readPoint read original wanted = some point ∧
      LatticeSelect.rankFrom points.levels points.dimension 0 (fun _ => 0) point = some rank ∧
      (fillTerm literal exactLabel point original).2 = wanted := by
  unfold rankTerm at ranked
  cases extracted : readPoint read original wanted with
  | none => simp [extracted, Bind.bind, Option.bind] at ranked
  | some point =>
      cases found : LatticeSelect.rankFrom points.levels points.dimension 0 (fun _ => 0) point with
      | none => simp [extracted, found, Bind.bind, Option.bind] at ranked
      | some actual =>
          simp only [extracted, found, Bind.bind, Option.bind] at ranked
          split at ranked
          · rename_i checked
            cases ranked
            exact ⟨point, rfl, found, (Language.termEq_correct _ _).mp checked⟩
          · cases ranked

/-- The full-term check prevents a rank for any term outside the actual rewritten tuple language. -/
theorem rankTerm_sound [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (names : List FullSyntax.Name) (formula : FullSyntax.Formula)
    (points : LatticeAPI.Points) (success : LatticeAPI.points names (FullSyntax.lowerFormula formula) = .ok points)
    (original wanted : Term (FillLabel Symbol)) (rank : Nat)
    (ranked : rankTerm literal exactLabel read points original wanted = some rank) :
    ∃ validRank : Fin (LatticeSelect.pointCount points.levels), validRank.val = rank ∧
      decodeTerm literal exactLabel points original validRank = wanted := by
  obtain ⟨point, _, pointRank, checked⟩ := rankTerm_success literal exactLabel read points original wanted rank ranked
  obtain ⟨compiled, parsed, built, dimension, _⟩ :=
    LatticeAPI.points_success names (FullSyntax.lowerFormula formula) points success
  obtain ⟨core, _, coreParsed⟩ := FullSyntax.signed_success_is_core _ true formula compiled parsed
  rw [dimension] at pointRank
  have bound := LatticeSelect.rankFrom_range names core compiled coreParsed points.levels built
    names.length 0 (by omega) (fun _ => 0) point rank pointRank
  have counted : rank < LatticeSelect.pointCount points.levels := by
    rw [← LatticeSelect.root_count names core compiled coreParsed points.levels built] at bound
    exact bound
  let validRank : Fin (LatticeSelect.pointCount points.levels) := ⟨rank, counted⟩
  have decoded := LatticeSelect.decodeFrom_rankFrom names core compiled coreParsed points.levels built
    names.length 0 (by omega) (fun _ => 0) point rank pointRank
  refine ⟨validRank, rfl, ?_⟩
  simpa [decodeTerm, LatticeSelect.decode, dimension, validRank, decoded] using checked

/-- Whole-term ranking recognizes exactly the terms produced by all valid tuple ranks. -/
theorem rankTerm_exact [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (names : List FullSyntax.Name) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (success : LatticeAPI.points names (FullSyntax.lowerFormula formula) = .ok points)
    (original : Term (FillLabel Symbol)) (valid : LeafHoles original) (dimension : holes original = names.length)
    (wanted : Term (FillLabel Symbol)) :
    (∃ rank, rankTerm literal exactLabel read points original wanted = some rank) ↔
      ∃ rank : Fin (LatticeSelect.pointCount points.levels), decodeTerm literal exactLabel points original rank = wanted := by
  constructor
  · rintro ⟨rank, found⟩
    obtain ⟨validRank, _, decoded⟩ := rankTerm_sound literal exactLabel read names formula points success original wanted rank found
    exact ⟨validRank, decoded⟩
  · rintro ⟨rank, rfl⟩
    exact ⟨rank.val, rank_decode literal exactLabel read literalRead names formula points success original valid dimension rank⟩

end MicroCFTA.IntegerTermCodec
