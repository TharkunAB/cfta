import MicroCFTA.IntegerTermCodec
import MicroCFTA.SupportTerms
import MicroCFTA.IntegerLabelCodec
import MicroCFTA.OpenIntegerReaders

/-!
# Integer filling through private term views

Private labels stay typed while the source computes spine and labelled views.
The hole reader uses a separate adapter after projection. The adapter does not
control projection and does not assume that projection is injective.
-/
namespace MicroCFTA.IntegerTermViews
open Language GeneratorCombinators

/-- Retain the distinctions that the source projection inspects. -/
def adaptLabel : Label Symbol → RecipeCompile.FillLabel Symbol
  | .user symbol => .user symbol
  | .placeholder => .placeholder
  | .pure => .internal 0
  | .apply => .internal 1
  | .joinN => .internal 2
  | .choice branch => .internal (18 * branch + 3)
  | .index rank => .internal (18 * rank + 4)
  | .join => .internal 5
  | .centerKeyed => .internal 6
  | .argKeyed => .internal 7
  | .recursion => .internal 8
  | .family => .internal 9
  | .atKey => .internal 10
  | .key index => .internal (18 * index + 11)
  | .argKey component argument => .internal (18 * ((component + argument) ^ 2 + component) + 12)
  | .leftKeyed => .internal 13
  | .rightKeyed => .internal 14
  | .group index => .internal (18 * index + 15)

mutual
/-- Convert labels for the existing hole reader after a typed view is selected. -/
def adapt : Term (Label Symbol) → Term (RecipeCompile.FillLabel Symbol)
  | .node label children => .node (adaptLabel label) (adaptForest children)
def adaptForest : List (Term (Label Symbol)) → List (Term (RecipeCompile.FillLabel Symbol))
  | [] => []
  | first :: rest => adapt first :: adaptForest rest
end

/-- The actual integer and pure constructors are leaves. -/
def Valid : Term (Label Symbol) → Prop
  | .node label children =>
      (label = .placeholder → children = []) ∧ (label = .pure → children = []) ∧
      ∀ child ∈ children, Valid child

/-- The coordinate count of a typed term. -/
def count (term : Term (Label Symbol)) : Nat := RecipeCompile.holes (adapt term)
/-- The coordinate count of a typed forest. -/
def forestCount (terms : List (Term (Label Symbol))) : Nat := RecipeCompile.forestHoles (adaptForest terms)

mutual
/-- Source `fillHoles.fill`, with all private constructor labels retained. -/
def fill (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) : Term (Label Symbol) → List Int × Term (Label Symbol)
  | .node .placeholder children =>
      match point with
      | value :: rest => (rest, .node (.user (literal value)) [])
      | [] => let tail := fillForest literal exactLabel [] children
              (tail.1, .node .placeholder tail.2)
  | .node (.user symbol) children =>
      let tail := fillForest literal exactLabel point children
      (tail.1, .node (.user (exactLabel point symbol)) tail.2)
  | .node privateLabel children =>
      let tail := fillForest literal exactLabel point children
      (tail.1, .node privateLabel tail.2)
termination_by term => sizeOf term

def fillForest (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) : List (Term (Label Symbol)) → List Int × List (Term (Label Symbol))
  | [] => (point, [])
  | first :: rest =>
      let front := fill literal exactLabel point first
      let tail := fillForest literal exactLabel front.1 rest
      (tail.1, front.2 :: tail.2)
termination_by terms => sizeOf terms
end

mutual
/-- The typed traversal has exactly the existing source filling behavior. -/
theorem adapt_fill (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (term : Term (Label Symbol)) :
    (fill literal exactLabel point term).1 = (RecipeCompile.fillTerm literal exactLabel point (adapt term)).1 ∧
    adapt (fill literal exactLabel point term).2 = (RecipeCompile.fillTerm literal exactLabel point (adapt term)).2 := by
  cases term with
  | node label children =>
      cases label <;> simp [fill, adapt, adaptLabel, RecipeCompile.fillTerm,
        adapt_fillForest literal exactLabel point children] <;>
        cases point <;> simp [fill, adapt, adaptLabel, RecipeCompile.fillTerm,
          adapt_fillForest literal exactLabel [] children, adaptForest]
termination_by sizeOf term

theorem adapt_fillForest (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (terms : List (Term (Label Symbol))) :
    (fillForest literal exactLabel point terms).1 = (RecipeCompile.fillForest literal exactLabel point (adaptForest terms)).1 ∧
    adaptForest (fillForest literal exactLabel point terms).2 =
      (RecipeCompile.fillForest literal exactLabel point (adaptForest terms)).2 := by
  cases terms with
  | nil => simp [fillForest, adaptForest, RecipeCompile.fillForest]
  | cons first rest =>
      simp only [fillForest, adaptForest, RecipeCompile.fillForest]
      rw [(adapt_fill literal exactLabel point first).1,
        (adapt_fill literal exactLabel point first).2]
      simpa only [List.cons.injEq, true_and] using adapt_fillForest literal exactLabel _ rest
termination_by sizeOf terms
end

theorem fill_remaining (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (term : Term (Label Symbol)) :
    (fill literal exactLabel point term).1 = point.drop (count term) := by
  rw [(adapt_fill literal exactLabel point term).1, RecipeCompile.fillTerm_remaining]
  rfl

theorem forest_remaining (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (terms : List (Term (Label Symbol))) :
    (fillForest literal exactLabel point terms).1 = point.drop (forestCount terms) := by
  rw [(adapt_fillForest literal exactLabel point terms).1, RecipeCompile.fillForest_remaining]
  rfl

mutual
/-- Typed shape validity supplies the reader's placeholder precondition. -/
theorem adapt_valid (term : Term (Label Symbol)) (valid : Valid term) :
    IntegerTermCodec.LeafHoles (adapt term) := by
  cases term with
  | node label children =>
      simp only [Valid] at valid
      cases label <;> simp only [adapt, adaptLabel, IntegerTermCodec.LeafHoles] <;>
        simp_all [adaptForest, adaptForest_valid children valid.2.2]
termination_by sizeOf term

theorem adaptForest_valid (terms : List (Term (Label Symbol)))
    (valid : ∀ term ∈ terms, Valid term) :
    ∀ term ∈ adaptForest terms, IntegerTermCodec.LeafHoles term := by
  cases terms with
  | nil => simp [adaptForest]
  | cons first rest =>
      intro term member
      simp only [adaptForest, List.mem_cons] at member
      rcases member with rfl | member
      · exact adapt_valid first (valid first (by simp))
      · exact adaptForest_valid rest (fun term member => valid term (by simp [member])) term member
termination_by sizeOf terms
end

/-- Child traversal splits at the same coordinate suffix when forests are joined. -/
theorem fill_append (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (left right : List (Term (Label Symbol))) :
    fillForest literal exactLabel point (left ++ right) =
      let front := fillForest literal exactLabel point left
      let tail := fillForest literal exactLabel front.1 right
      (tail.1, front.2 ++ tail.2) := by
  induction left generalizing point with
  | nil => simp [fillForest]
  | cons first rest ih => simp [fillForest, ih]

/-- The source function-side application view. -/
abbrev spine := @SupportTerms.applicationLeftChildren

/-- The source labelled view, before the enclosing user label is added. -/
def labelled : Term (Label Symbol) → List (Term (Label Symbol))
  | .node .joinN children => children
  | .node (.choice _) [child] => labelled child
  | .node .pure _ => []
  | term => spine term

/-- The typed labelled projection is exactly the existing source label adapter. -/
theorem labelled_source (symbol : Symbol) (term : Term (Label Symbol)) :
    SupportTerms.labelTerm symbol term = .node (.user symbol) (labelled term) := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms,
      SupportTerms.labelTerm symbol term = .node (.user symbol) (labelled term)) with
  | node label children ih =>
      cases label <;> cases children with
      | nil => simp [SupportTerms.labelTerm, labelled, spine,
          SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]
      | cons first rest => cases rest with
        | nil => simp [SupportTerms.labelTerm, labelled, ih first (by simp), spine,
            SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]
        | cons second rest => simp [SupportTerms.labelTerm, labelled, spine,
            SupportTerms.applicationLeftChildren]
  | nil => simp_all
  | cons first rest hf hr =>
      rename_i term member
      rcases List.mem_cons.mp member with rfl | member
      · exact hf
      · exact hr term member

/-- Filling commutes with the application view, including coordinate suffixes. -/
theorem spine_fill (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (term : Term (Label Symbol)) (valid : Valid term) :
    fillForest literal exactLabel point (spine term) =
      ((fill literal exactLabel point term).1, spine (fill literal exactLabel point term).2) := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ point : List Int, Valid term →
      fillForest literal exactLabel point (spine term) =
        ((fill literal exactLabel point term).1, spine (fill literal exactLabel point term).2)) generalizing point with
  | node label children ih =>
      simp only [Valid] at valid
      cases label with
      | pure =>
          have empty := valid.2.1 rfl
          subst children
          simp [spine, SupportTerms.applicationLeftChildren, fill, fillForest]
      | placeholder =>
          have empty := valid.1 rfl
          subst children
          cases point <;> simp [spine, SupportTerms.applicationLeftChildren,
            SupportTerms.applicationTermChildren, fill, fillForest]
      | apply =>
          cases children with
          | nil => simp [spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren, fill, fillForest]
          | cons first rest => cases rest with
            | nil => simp [spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren, fill, fillForest]
            | cons second rest => cases rest with
              | nil =>
                  simp only [spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren,
                    Option.getD, fill_append, fill, fillForest]
                  rw [ih first (by simp) point (valid.2.2 first (by simp))]
              | cons third rest =>
                  simp [spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren, fill, fillForest]
      | _ => simp [spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren, fill, fillForest]
  | nil => simp_all
  | cons first rest hf hr =>
      rename_i term member point valid
      rcases List.mem_cons.mp member with rfl | member
      · exact hf point valid
      · exact hr term member point valid

/-- Filling also commutes with choice removal and n-way join labelling. -/
theorem labelled_fill (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (term : Term (Label Symbol)) (valid : Valid term) :
    fillForest literal exactLabel point (labelled term) =
      ((fill literal exactLabel point term).1, labelled (fill literal exactLabel point term).2) := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ point : List Int, Valid term →
      fillForest literal exactLabel point (labelled term) =
        ((fill literal exactLabel point term).1, labelled (fill literal exactLabel point term).2)) generalizing point with
  | node label children ih =>
      have childrenValid := valid
      simp only [Valid] at childrenValid
      cases label with
      | pure =>
          have empty := childrenValid.2.1 rfl
          subst children
          simp [labelled, fill, fillForest]
      | placeholder =>
          have empty := childrenValid.1 rfl
          subst children
          cases point <;> simp [labelled, spine, SupportTerms.applicationLeftChildren,
            SupportTerms.applicationTermChildren, fill, fillForest]
      | joinN => simp [labelled, fill]
      | choice branch =>
          cases children with
          | nil => simp [labelled, spine, SupportTerms.applicationLeftChildren,
              SupportTerms.applicationTermChildren, fill, fillForest]
          | cons first rest => cases rest with
            | nil =>
                simpa [labelled, fill, fillForest] using
                  (ih first (by simp) point (childrenValid.2.2 first (by simp)))
            | cons second rest =>
                simpa [labelled, fill, fillForest] using
                  spine_fill literal exactLabel point (.node (.choice branch) (first :: second :: rest)) valid
      | _ => simpa [labelled, fill] using spine_fill literal exactLabel point (.node _ children) valid
  | nil => simp_all
  | cons first rest hf hr =>
      rename_i term member point valid
      rcases List.mem_cons.mp member with rfl | member
      · exact hf point valid
      · exact hr term member point valid

/-- The three `pointsStatic` request forms use these typed projections. -/
inductive View where
  | whole | spine | labelled
  deriving DecidableEq

def project (view : View) (term : Term (Label Symbol)) : List (Term (Label Symbol)) :=
  match view with
  | .whole => [term]
  | .spine => spine term
  | .labelled => labelled term

/-- Every source view preserves the filling order and all consumed coordinates. -/
theorem project_fill (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (view : View) (term : Term (Label Symbol)) (valid : Valid term) :
    fillForest literal exactLabel point (project view term) =
      ((fill literal exactLabel point term).1, project view (fill literal exactLabel point term).2) := by
  cases view with
  | whole => simp [project, fillForest]
  | spine => exact spine_fill literal exactLabel point term valid
  | labelled => exact labelled_fill literal exactLabel point term valid

/-- Projection preserves the number of integer positions, including empty views. -/
theorem project_count (literal : Int → Symbol) (view : View) (term : Term (Label Symbol)) (valid : Valid term) :
    forestCount (project view term) = count term := by
  let n := forestCount (project view term) + count term
  let point : List Int := List.replicate n 0
  have same := congrArg (fun result => result.1.length)
    (project_fill literal (fun _ symbol => symbol) point view term valid)
  simp only [forest_remaining, fill_remaining, List.length_drop, point, List.length_replicate] at same
  dsimp [n] at same
  omega

/-- An application view contains only valid source subtrees. -/
theorem spine_valid (term : Term (Label Symbol)) (valid : Valid term) :
    ∀ child ∈ spine term, Valid child := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, Valid term → ∀ child ∈ spine term, Valid child) with
  | node label children ih =>
      have all := valid
      simp only [Valid] at all
      cases label <;> cases children with
      | nil => simp_all [spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]
      | cons first rest => cases rest with
        | nil => simp_all [spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]
        | cons second rest => cases rest with
          | nil =>
              simp_all [spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren] <;> grind
          | cons third rest => simp_all [spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]
  | nil => simp_all
  | cons first rest hf hr =>
      rename_i term member valid child present
      rcases List.mem_cons.mp member with rfl | member
      · exact hf valid child present
      · exact hr term member valid child present

/-- A labelled view also contains only valid source subtrees. -/
theorem labelled_valid (term : Term (Label Symbol)) (valid : Valid term) :
    ∀ child ∈ labelled term, Valid child := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, Valid term → ∀ child ∈ labelled term, Valid child) with
  | node label children ih =>
      have all := valid
      simp only [Valid] at all
      cases label with
      | pure => simp [labelled]
      | joinN => exact all.2.2
      | choice branch =>
          cases children with
          | nil => simpa [labelled] using spine_valid (.node (.choice branch) []) valid
          | cons first rest => cases rest with
            | nil => exact ih first (by simp) (all.2.2 first (by simp))
            | cons second rest => simpa [labelled] using spine_valid (.node (.choice branch) (first :: second :: rest)) valid
      | _ => simpa [labelled] using spine_valid (.node _ children) valid
  | nil => simp_all
  | cons first rest hf hr =>
      rename_i term member valid child present
      rcases List.mem_cons.mp member with rfl | member
      · exact hf valid child present
      · exact hr term member valid child present

theorem project_valid (view : View) (term : Term (Label Symbol)) (valid : Valid term) :
    ∀ child ∈ project view term, Valid child := by
  cases view with
  | whole => simpa [project] using valid
  | spine => exact spine_valid term valid
  | labelled => exact labelled_valid term valid

/-- Source coordinate extraction from one selected private view. -/
def readView (read : Symbol → Option Int) (view : View) (original : Term (Label Symbol))
    (wanted : List (Term (Label Symbol))) : Option (List Int) := do
  let symbols ← IntegerTermCodec.holesIn (adaptForest (project view original)) (adaptForest wanted)
  IntegerTermCodec.readSymbols read symbols

/-- Every coordinate survives each private projection in its original order. -/
theorem view_symbols (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (point : List Int) (view : View) (term : Term (Label Symbol)) (valid : Valid term)
    (dimension : point.length = count term) :
    IntegerTermCodec.holesIn (adaptForest (project view term))
      (adaptForest (project view (fill literal exactLabel point term).2)) = some (point.map literal) := by
  have commutes := congrArg (fun result => adaptForest result.2)
    (project_fill literal exactLabel point view term valid)
  rw [← commutes, (adapt_fillForest literal exactLabel point (project view term)).2]
  have size : RecipeCompile.forestHoles (adaptForest (project view term)) = point.length :=
    (project_count literal view term valid).trans dimension.symm
  simpa [size] using IntegerTermCodec.holesIn_fill literal exactLabel point
    (adaptForest (project view term))
    (adaptForest_valid _ (project_valid view term valid)) (by omega)

/-- The source view reader is a left inverse of filling; projection injectivity is not assumed. -/
theorem readView_fill (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (point : List Int) (view : View) (term : Term (Label Symbol)) (valid : Valid term)
    (dimension : point.length = count term) :
    readView read view term (project view (fill literal exactLabel point term).2) = some point := by
  simp only [readView, view_symbols literal exactLabel point view term valid dimension,
    Bind.bind, Option.bind]
  exact IntegerTermCodec.read_literals literal read literalRead point

/-- Distinct integer points cannot merge inside any fixed outcome's view. -/
theorem view_fill_injective (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (view : View) (term : Term (Label Symbol)) (valid : Valid term) (left right : List Int)
    (leftSize : left.length = count term) (rightSize : right.length = count term)
    (same : project view (fill literal exactLabel left term).2 =
      project view (fill literal exactLabel right term).2) : left = right := by
  have equal := congrArg (readView read view term) same
  rw [readView_fill literal exactLabel read literalRead left view term valid leftSize,
    readView_fill literal exactLabel read literalRead right view term valid rightSize] at equal
  exact Option.some.inj equal

/-- Source final view matching checks every projected label and child. -/
theorem forestEq_exact [DecidableEq Symbol] (left right : List (Term (Label Symbol))) :
    Language.forestEq left right = true ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [Language.forestEq]
  | cons first rest ih =>
      cases right <;> simp [Language.forestEq, Language.termEq_correct, ih]

/-- One original outcome's tuple ranker for all source request views. -/
def rankView [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (points : LatticeAPI.Points) (view : View)
    (original : Term (Label Symbol)) (wanted : List (Term (Label Symbol))) : Option Nat := do
  let point ← readView read view original wanted
  let rank ← LatticeSelect.rankFrom points.levels points.dimension 0 (fun _ => 0) point
  if Language.forestEq (project view (fill literal exactLabel point original).2) wanted then
    some rank else none

/-- Project the filled term at the selected lattice rank. -/
def decodeView (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (points : LatticeAPI.Points) (view : View) (original : Term (Label Symbol))
    (rank : Fin (LatticeSelect.pointCount points.levels)) : List (Term (Label Symbol)) :=
  project view (fill literal exactLabel (LatticeSelect.decode points.dimension points.levels rank) original).2

/-- The actual source tuple decoder and projected-term reader are inverse at every rank. -/
theorem rank_decode [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (names : List FullSyntax.Name) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (success : LatticeAPI.points names (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (original : Term (Label Symbol)) (valid : Valid original)
    (dimension : count original = names.length) (rank : Fin (LatticeSelect.pointCount points.levels)) :
    rankView literal exactLabel read points view original (decodeView literal exactLabel points view original rank) =
      some rank.val := by
  have table := LatticeSelect.points_api_exact names formula points success
  have tupleSize : (LatticeSelect.decode points.dimension points.levels rank).length = count original :=
    ((table.2.2.1 _).mpr ⟨rank, rfl⟩).1.trans dimension.symm
  simp only [rankView, decodeView,
    readView_fill literal exactLabel read literalRead _ view original valid tupleSize, Bind.bind, Option.bind]
  rw [IntegerTermCodec.public_rank_decode names formula points success rank]
  simp [forestEq_exact]

/-- Each projected fixed-outcome language still has distinct ranks. -/
theorem decode_injective [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (names : List FullSyntax.Name) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (success : LatticeAPI.points names (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (original : Term (Label Symbol)) (valid : Valid original)
    (dimension : count original = names.length) :
    Function.Injective (decodeView literal exactLabel points view original) := by
  intro left right same
  have equal := congrArg (rankView literal exactLabel read points view original) same
  rw [rank_decode literal exactLabel read literalRead names formula points success view original valid dimension left,
    rank_decode literal exactLabel read literalRead names formula points success view original valid dimension right] at equal
  exact Fin.ext (Option.some.inj equal)

/-- A successful candidate includes exact tuple ranking and the final view check. -/
theorem rankView_success [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (points : LatticeAPI.Points) (view : View)
    (original : Term (Label Symbol)) (wanted : List (Term (Label Symbol))) (rank : Nat)
    (ranked : rankView literal exactLabel read points view original wanted = some rank) :
    ∃ point, readView read view original wanted = some point ∧
      LatticeSelect.rankFrom points.levels points.dimension 0 (fun _ => 0) point = some rank ∧
      project view (fill literal exactLabel point original).2 = wanted := by
  unfold rankView at ranked
  cases extracted : readView read view original wanted with
  | none => simp [extracted, Bind.bind, Option.bind] at ranked
  | some point =>
      cases found : LatticeSelect.rankFrom points.levels points.dimension 0 (fun _ => 0) point with
      | none => simp [extracted, found, Bind.bind, Option.bind] at ranked
      | some actual =>
          simp only [extracted, found, Bind.bind, Option.bind] at ranked
          split at ranked
          · rename_i checked
            cases ranked
            exact ⟨point, rfl, found, (forestEq_exact _ _).mp checked⟩
          · cases ranked

/-- No successful candidate can add a view outside the actual filled tuple language. -/
theorem rankView_sound [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (names : List FullSyntax.Name) (formula : FullSyntax.Formula)
    (points : LatticeAPI.Points) (success : LatticeAPI.points names (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (original : Term (Label Symbol)) (wanted : List (Term (Label Symbol))) (rank : Nat)
    (ranked : rankView literal exactLabel read points view original wanted = some rank) :
    ∃ validRank : Fin (LatticeSelect.pointCount points.levels), validRank.val = rank ∧
      decodeView literal exactLabel points view original validRank = wanted := by
  obtain ⟨point, _, pointRank, checked⟩ := rankView_success literal exactLabel read points view original wanted rank ranked
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
  simpa [decodeView, LatticeSelect.decode, dimension, validRank, decoded] using checked

/-- The candidate ranker recognizes exactly this outcome's projected tuple language. -/
theorem rankView_exact [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (names : List FullSyntax.Name) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (success : LatticeAPI.points names (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (original : Term (Label Symbol)) (valid : Valid original)
    (dimension : count original = names.length) (wanted : List (Term (Label Symbol))) :
    (∃ rank, rankView literal exactLabel read points view original wanted = some rank) ↔
      ∃ rank : Fin (LatticeSelect.pointCount points.levels), decodeView literal exactLabel points view original rank = wanted := by
  constructor
  · rintro ⟨rank, found⟩
    obtain ⟨validRank, _, decoded⟩ := rankView_sound literal exactLabel read names formula points success view original wanted rank found
    exact ⟨validRank, decoded⟩
  · rintro ⟨rank, rfl⟩
    exact ⟨rank.val, rank_decode literal exactLabel read literalRead names formula points success view original valid dimension rank⟩

/-- Source Pure and Placeholder terms satisfy both leaf requirements. -/
theorem pure_valid : Valid (.node (.pure : Label Symbol) []) := by simp [Valid]
theorem placeholder_valid : Valid (.node (.placeholder : Label Symbol) []) := by simp [Valid]

/-- Source applicative and choice wrappers preserve the required shape. -/
theorem apply_valid (left right : Term (Label Symbol)) (hl : Valid left) (hr : Valid right) :
    Valid (.node .apply [left, right]) := by simp [Valid, hl, hr]

theorem choice_valid (branch : Nat) (term : Term (Label Symbol)) (valid : Valid term) :
    Valid (.node (.choice branch) [term]) := by simp [Valid, valid]

/-- Closing a term with a user label preserves both source shape requirements. -/
theorem label_valid (symbol : Symbol) (term : Term (Label Symbol)) (valid : Valid term) :
    Valid (SupportTerms.labelTerm symbol term) := by
  rw [labelled_source]
  simpa [Valid] using labelled_valid term valid

/-- Closing a term cannot remove a coordinate through private-label projection. -/
theorem label_count (literal : Int → Symbol) (symbol : Symbol) (term : Term (Label Symbol)) (valid : Valid term) :
    count (SupportTerms.labelTerm symbol term) = count term := by
  rw [labelled_source]
  simpa [count, adapt, adaptLabel, RecipeCompile.holes, forestCount, project] using
    project_count literal .labelled term valid

/-- The typed private constructor tree produced by the existing bare-spine reader. -/
def template : OpenIntegerReaders.Reader α → Term (Label Symbol)
  | .pure _ => .node .pure []
  | .integer => .node .placeholder []
  | .map _ inner | .pay inner => template inner
  | .app functions arguments => .node .apply [template functions, template arguments]

/-- This typed template refines the earlier whole-term codec template. -/
theorem template_adapt (reader : OpenIntegerReaders.Reader α) :
    adapt (template (Symbol := Symbol) reader) = OpenIntegerReaders.template reader := by
  induction reader with
  | pure value => rfl
  | integer => rfl
  | map transform inner ih | pay inner ih => exact ih
  | app functions arguments left right => simp [template, adapt, adaptForest, adaptLabel,
      OpenIntegerReaders.template, left, right]

/-- The source reader constructs the shape needed by every view proof. -/
theorem template_valid (reader : OpenIntegerReaders.Reader α) : Valid (template (Symbol := Symbol) reader) := by
  induction reader with
  | pure value => exact pure_valid
  | integer => exact placeholder_valid
  | map transform inner ih | pay inner ih => exact ih
  | app functions arguments left right => exact apply_valid _ _ left right

/-- The actual key count is also the hole count of the typed source template. -/
theorem template_count (reader : OpenIntegerReaders.Reader α) :
    count (template (Symbol := Symbol) reader) = OpenIntegerReaders.width reader := by
  rw [count, template_adapt, OpenIntegerReaders.template_holes]

/-- Actual integer labels and the singleton reader give every source view an exact rank inverse. -/
theorem integer_rank_decode (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (names : List FullSyntax.Name) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (success : LatticeAPI.points names (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (original : Term (Label IntegerLabelCodec.Symbol)) (valid : Valid original)
    (dimension : count original = names.length) (rank : Fin (LatticeSelect.pointCount points.levels)) :
    rankView IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue points view original
      (decodeView IntegerLabelCodec.integerSymbol specialize points view original rank) = some rank.val :=
  rank_decode IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
    IntegerLabelCodec.leafValue_integer names formula points success view original valid dimension rank

/-- Bare open spines discharge the view shape and hole-count obligations from their constructors. -/
theorem reader_rank_decode (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (names : List FullSyntax.Name) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (success : LatticeAPI.points names (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (reader : OpenIntegerReaders.Reader α)
    (dimension : OpenIntegerReaders.width reader = names.length)
    (rank : Fin (LatticeSelect.pointCount points.levels)) :
    rankView IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue points view (template reader)
      (decodeView IntegerLabelCodec.integerSymbol specialize points view (template reader) rank) = some rank.val :=
  integer_rank_decode specialize names formula points success view (template reader) (template_valid reader)
    ((template_count reader).trans dimension) rank

/-- Different original members can intentionally have the same labelled view. -/
theorem labelled_not_globally_injective :
    let hole : Term (Label Unit) := .node .placeholder []
    let left := .node (.choice 0) [hole]
    let right := .node (.choice 1) [hole]
    left ≠ right ∧ labelled left = labelled right := by
  simp [labelled]

end MicroCFTA.IntegerTermViews
