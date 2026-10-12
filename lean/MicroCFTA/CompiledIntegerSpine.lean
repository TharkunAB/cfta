import MicroCFTA.OpenIntegerSource
import MicroCFTA.StaticCompositeCandidateRanks

/-!
# Actual keyed joins in a generated open integer spine

`compileOpenSpine` pairs its one-key buckets through `relateGroupsM`.
`pairBucket` uses a nullary Pure operation and two keyed JoinN arguments.
Singleton key and bucket operations retain the selected term unchanged.
-/
namespace MicroCFTA.CompiledIntegerSpine
open Language GeneratorCombinators IntegerTermViews OpenIntegerSource

/-- Each successful bare-spine product has one retained pair, with component index zero. -/
def template : Recipe α → Term (Label Symbol)
  | .pure _ => .node .pure []
  | .integer _ => .node .placeholder []
  | .map _ inner | .pay inner => template inner
  | .app functions arguments => SupportJoin.joinTerm 0 (.node .pure []) [template functions, template arguments]

/-- The exact keyed compiler template satisfies both leaf-shape requirements. -/
theorem template_valid (recipe : Recipe α) : Valid (template (Symbol := Symbol) recipe) := by
  induction recipe with
  | pure value => exact pure_valid
  | integer domain => exact placeholder_valid
  | map transform inner ih | pay inner ih => exact ih
  | app functions arguments left right =>
      simp [template, SupportJoin.joinTerm, SupportJoin.keys, SupportJoin.arguments, Valid, left, right]

/-- Private centre and argument keys consume no coordinates; child order is unchanged. -/
theorem template_count (recipe : Recipe α) :
    count (template (Symbol := Symbol) recipe) = OpenIntegerReaders.width (reader recipe) := by
  induction recipe with
  | pure value => simp [template, count, adapt, adaptLabel, adaptForest, RecipeCompile.holes,
      RecipeCompile.forestHoles, reader, OpenIntegerReaders.width, OpenIntegerReaders.counts]
  | integer domain => simp [template, count, adapt, adaptLabel, RecipeCompile.holes,
      reader, OpenIntegerReaders.width, OpenIntegerReaders.counts]
  | map transform inner ih | pay inner ih => exact ih
  | app functions arguments left right =>
      simp only [count] at left right
      simp [template, count, SupportJoin.joinTerm, SupportJoin.keys, SupportJoin.arguments,
        adapt, adaptLabel, adaptForest, RecipeCompile.holes, RecipeCompile.forestHoles,
        left, right, reader, OpenIntegerReaders.width, OpenIntegerReaders.counts]

/-- The nullary operation is followed by the exact two argument callback requests. -/
def pairChildren (functions arguments : Term (Label Symbol) → List Nat) :
    List (Term (Label Symbol)) → List Nat
  | [.node .centerKeyed (operation :: _), .node .argKeyed [_, function], .node .argKeyed [_, argument]] =>
      StaticCandidateRanks.productCandidates 1
        (StaticCandidateRanks.candidates .pure .whole [operation])
        (StaticCandidateRanks.productCandidates 1 (functions function)
          (StaticCandidateRanks.productCandidates 1 (arguments argument) [0]))
  | _ => []

/-- The source join callback accepts a whole JoinN term or its labelled child list. -/
def pairCandidates (functions arguments : Term (Label Symbol) → List Nat) :
    View → List (Term (Label Symbol)) → List Nat
  | .whole, [.node .joinN children] | .spine, [.node .joinN children] => pairChildren functions arguments children
  | .labelled, children => pairChildren functions arguments children
  | _, _ => []

/-- Execute the actual recursive callback tree of a one-group open spine. -/
def candidates : Recipe α → View → List (Term (Label Symbol)) → List Nat
  | .pure _, view, wanted => StaticCandidateRanks.candidates .pure view wanted
  | .integer _, view, wanted => StaticCandidateRanks.candidates .hole view wanted
  | .map _ inner, view, wanted | .pay inner, view, wanted => candidates inner view wanted
  | .app functions arguments, view, wanted =>
      pairCandidates (fun term => candidates functions .whole [term])
        (fun term => candidates arguments .whole [term]) view wanted

/-- The actual source selector has one original outcome, before its integer point is selected. -/
def select (recipe : Recipe α) (rank : Nat) : Option (Term (Label Symbol)) :=
  if rank = 0 then some (template recipe) else none

/-- Each side's recursive candidate is kept by the pair's exact source mixed-radix calculation. -/
theorem pair_complete (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (functions arguments : Term (Label Symbol) → List Nat) (point : List Int)
    (function argument : Term (Label Symbol))
    (left : 0 ∈ functions (fill literal exactLabel point function).2)
    (right : 0 ∈ arguments (fill literal exactLabel (fill literal exactLabel point function).1 argument).2)
    (view : View) :
    0 ∈ pairCandidates functions arguments view
      (project view (fill literal exactLabel point
        (SupportJoin.joinTerm 0 (.node .pure []) [function, argument])).2) := by
  rw [StaticCompositeCandidateRanks.fill_join]
  have tail := StaticCandidateRanks.product_member 1 _ [0] 0 0 right (by simp)
  have front := StaticCandidateRanks.product_member 1 _ _ 0 0 left (by simpa [Probability.pairRank] using tail)
  have operation := StaticCandidateRanks.product_member 1 [0] _ 0 0 (by simp)
    (by simpa [Probability.pairRank] using front)
  cases view <;> simpa [project, labelled, spine, SupportTerms.applicationLeftChildren,
    SupportTerms.applicationTermChildren, pairCandidates, pairChildren, SupportJoin.joinTerm,
    SupportJoin.keys, SupportJoin.arguments, fill, fillForest, StaticCandidateRanks.candidates,
    Probability.pairRank] using operation

/-- Every recursively generated keyed-join outcome is discovered after integer filling. -/
theorem candidate_complete (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (recipe : Recipe α) (point : List Int) (view : View) :
    0 ∈ candidates recipe view (project view (fill literal exactLabel point (template recipe)).2) := by
  induction recipe generalizing point view with
  | pure value =>
      exact StaticCandidateRanks.candidate_complete literal exactLabel .pure trivial point view
  | integer domain =>
      exact StaticCandidateRanks.candidate_complete literal exactLabel .hole trivial point view
  | map transform inner ih | pay inner ih => exact ih point view
  | app functions arguments left right =>
      exact pair_complete literal exactLabel _ _ point (template functions) (template arguments)
        (left point .whole) (right _ .whole) view

/-- Exact key and selected-term projection of the singleton grouped compiler path. -/
def compile : Recipe α → Except (LatticeAPI.Error String) (Option (List OpenIntegerKeys.Key × Term (Label Symbol)))
  | .pure _ => .ok (some ([], .node .pure []))
  | .integer domain => (integerGroup domain).map (Option.map (fun key => ([key], .node .placeholder [])))
  | .map _ inner | .pay inner => compile inner
  | .app functions arguments => do
      match ← compile functions with
      | none => pure none
      | some left =>
          match ← compile arguments with
          | none => pure none
          | some right => pure (some (left.1 ++ right.1,
              SupportJoin.joinTerm 0 (.node .pure []) [left.2, right.2]))

/-- The concrete keyed template and key traversal agree through every compiler branch. -/
theorem compile_exact (recipe : Recipe α) :
    compile (Symbol := Symbol) recipe =
      (compileKeys recipe).map (Option.map (fun keys => (keys, template recipe))) := by
  induction recipe with
  | pure value => rfl
  | integer domain =>
      simp only [compile, compileKeys, template]
      cases integerGroup domain with
      | error error => rfl
      | ok group => cases group <;> rfl
  | map transform inner ih | pay inner ih => exact ih
  | app functions arguments left right =>
      simp only [compile, compileKeys, left, right, template]
      cases compileKeys functions with
      | error error => rfl
      | ok group => cases group with
        | none => rfl
        | some functionKeys => cases compileKeys arguments with
          | error error => rfl
          | ok group => cases group <;> rfl

/-- Every retained concrete compiler term has exactly the variables of its constructed key. -/
theorem compile_dimension (recipe : Recipe α) (keys : List OpenIntegerKeys.Key) (term : Term (Label Symbol))
    (compiled : compile recipe = .ok (some (keys, term))) :
    count term = (OpenIntegerKeys.join keys).width ∧ term = template recipe := by
  rw [compile_exact] at compiled
  cases built : compileKeys recipe with
  | error error => simp [built, Except.map] at compiled
  | ok group => cases group with
    | none => simp [built, Except.map] at compiled
    | some actualKeys =>
        simp [built, Except.map] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        exact ⟨(template_count recipe).trans (compileKeys_width recipe actualKeys built).symm, rfl⟩

/-- The source pointsStatic callback, using the actual recursive keyed-join candidates. -/
def pointCandidates [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (points : LatticeAPI.Points) (recipe : Recipe α)
    (view : View) (wanted : List (Term (Label Symbol))) : List Nat :=
  (candidates recipe view wanted).flatMap fun originalRank =>
    match select recipe originalRank with
    | none => []
    | some original => match rankView literal exactLabel read points view original wanted with
      | none => []
      | some rank => [Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank rank]

/-- Every actual keyed-join point term is discovered and gets its exact point rank. -/
theorem points_complete [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (recipe : Recipe α) (names : List FullSyntax.Name) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (closed : LatticeAPI.points names (FullSyntax.lowerFormula formula) = .ok points)
    (dimension : OpenIntegerReaders.width (reader recipe) = names.length)
    (view : View) (rank : Fin (LatticeSelect.pointCount points.levels)) :
    rank.val ∈ pointCandidates literal exactLabel read points recipe view
      (decodeView literal exactLabel points view (template recipe) rank) := by
  apply List.mem_flatMap.mpr
  refine ⟨0, candidate_complete literal exactLabel recipe _ view, ?_⟩
  simp only [select, ↓reduceIte]
  rw [rank_decode literal exactLabel read literalRead names formula points closed view
    (template recipe) (template_valid recipe) ((template_count recipe).trans dimension) rank]
  simp [Probability.pairRank]

/-- The full view check rejects every candidate outside the concrete compiled template's filled language. -/
theorem points_sound [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (recipe : Recipe α)
    (names : List FullSyntax.Name) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (closed : LatticeAPI.points names (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (wanted : List (Term (Label Symbol))) (rank : Nat)
    (member : rank ∈ pointCandidates literal exactLabel read points recipe view wanted) :
    ∃ pointRank : Fin (LatticeSelect.pointCount points.levels), rank = pointRank.val ∧
      decodeView literal exactLabel points view (template recipe) pointRank = wanted := by
  obtain ⟨originalRank, _, accepted⟩ := List.mem_flatMap.mp member
  by_cases zero : originalRank = 0
  · subst originalRank
    simp only [select, ↓reduceIte] at accepted
    cases ranked : rankView literal exactLabel read points view (template recipe) wanted with
    | none => simp [ranked] at accepted
    | some pointRank =>
        have same : rank = pointRank := by simpa [ranked, Probability.pairRank] using accepted
        obtain ⟨validRank, value, decoded⟩ := rankView_sound literal exactLabel read names formula points closed
          view (template recipe) wanted pointRank ranked
        exact ⟨validRank, same.trans value.symm, decoded⟩
  · simp [select, zero] at accepted

/-- The actual singleton grouped compiler and all three source views have exact integer-closure ranks. -/
theorem compiled_ranks_exact
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (recipe : Recipe α) (keys : List OpenIntegerKeys.Key) (term : Term (Label IntegerLabelCodec.Symbol))
    (compiled : compile recipe = .ok (some (keys, term))) (points : LatticeAPI.Points)
    (closed : LatticeAPI.points (OpenIntegerKeys.names (OpenIntegerKeys.join keys).width)
      (FullSyntax.lowerFormula (OpenIntegerKeys.join keys).formula) = .ok points)
    (view : View) (wanted : List (Term (Label IntegerLabelCodec.Symbol))) (rank : Nat) :
    rank ∈ pointCandidates IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue points recipe view wanted ↔
      ∃ pointRank : Fin (LatticeSelect.pointCount points.levels), rank = pointRank.val ∧
        decodeView IntegerLabelCodec.integerSymbol specialize points view term pointRank = wanted := by
  have ⟨dimension, same⟩ := compile_dimension recipe keys term compiled
  subst term
  constructor
  · exact points_sound IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue recipe _ _ points closed view wanted rank
  · rintro ⟨pointRank, rfl, rfl⟩
    apply points_complete IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
      IntegerLabelCodec.leafValue_integer recipe _ _ points closed _ view pointRank
    simpa [OpenIntegerKeys.names, template_count] using dimension

/-- The concrete keyed compiler template has one distinct filled view per integer rank. -/
theorem compiled_decode_injective
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (recipe : Recipe α) (keys : List OpenIntegerKeys.Key) (term : Term (Label IntegerLabelCodec.Symbol))
    (compiled : compile recipe = .ok (some (keys, term))) (points : LatticeAPI.Points)
    (closed : LatticeAPI.points (OpenIntegerKeys.names (OpenIntegerKeys.join keys).width)
      (FullSyntax.lowerFormula (OpenIntegerKeys.join keys).formula) = .ok points) (view : View) :
    Function.Injective (decodeView IntegerLabelCodec.integerSymbol specialize points view term) := by
  have ⟨dimension, same⟩ := compile_dimension recipe keys term compiled
  subst term
  exact decode_injective IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
    IntegerLabelCodec.leafValue_integer _ _ points closed view _ (template_valid recipe)
    (by simpa [OpenIntegerKeys.names] using dimension)

end MicroCFTA.CompiledIntegerSpine
