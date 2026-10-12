import MicroCFTA.OpenIntegerKeys
import MicroCFTA.StaticCandidateRanks

/-!
# Open integer key control and reference applicative callbacks

This fragment compiles pure values, integer domains, maps, pays, and products.
It keeps actual lattice failures and empty groups separate. The ordinary Apply
callback tree is a reference shape. The grouped compiler uses keyed JoinN
wrappers. The concrete adapter is separate from this reference tree.
-/
namespace MicroCFTA.OpenIntegerSource
open Language GeneratorCombinators

attribute [local simp] LatticeLinear.except_map_ok LatticeLinear.except_map_error

/-- Bare open-spine syntax retains every integer leaf's source domain formula. -/
inductive Recipe : Type → Type 1 where
  | pure (value : α) : Recipe α
  | integer (domain : FullSyntax.Formula) : Recipe Int
  | map (transform : α → β) (inner : Recipe α) : Recipe β
  | pay (inner : Recipe α) : Recipe α
  | app (functions : Recipe (α → β)) (arguments : Recipe α) : Recipe β

/-- The source value reader has the same constructor structure. -/
def reader : Recipe α → OpenIntegerReaders.Reader α
  | .pure value => .pure value
  | .integer _ => .integer
  | .map transform inner => .map transform (reader inner)
  | .pay inner => .pay (reader inner)
  | .app functions arguments => .app (reader functions) (reader arguments)

/-- Ordinary applicative callbacks for the reference reader tree; not the grouped JoinN output. -/
def source : Recipe α → StaticCandidateRanks.Source Symbol
  | .pure _ => .pure
  | .integer _ => .hole
  | .map _ inner => .map (source inner)
  | .pay inner => .pay (source inner)
  | .app functions arguments => .app (source functions) (source arguments)

/-- An integer group's root variable is the reserved coordinate zero. -/
def integerKey (domain : FullSyntax.Formula) (points : Option Nat) : OpenIntegerKeys.Key :=
  ⟨1, SourceFormula.substitute [(SourceGuards.valueName, IntegerLabelCodec.integerName 0)] domain, points⟩

/-- Execute `integerGroup`'s counter branches; an unbounded leaf remains an open group. -/
def integerGroup (domain : FullSyntax.Formula) :
    Except (LatticeAPI.Error String) (Option OpenIntegerKeys.Key) :=
  match LatticeAPI.points [SourceGuards.valueName] (FullSyntax.lowerFormula domain) with
  | .ok points => if points.count = 0 then .ok none
      else .ok (some (integerKey domain (some points.count.toNat)))
  | .error (.elimination .unboundedVariable) => .ok (some (integerKey domain none))
  | .error error => .error error

/-- The source bare-spine compiler's key order and error/empty precedence. -/
def compileKeys : Recipe α → Except (LatticeAPI.Error String) (Option (List OpenIntegerKeys.Key))
  | .pure _ => .ok (some [])
  | .integer domain => (integerGroup domain).map (Option.map (fun key => [key]))
  | .map _ inner | .pay inner => compileKeys inner
  | .app functions arguments => do
      match ← compileKeys functions with
      | none => pure none
      | some left =>
          match ← compileKeys arguments with
          | none => pure none
          | some right => pure (some (left ++ right))

/-- Actual leaf compilation constructs width one in every retained branch. -/
theorem integerGroup_width (domain : FullSyntax.Formula) (key : OpenIntegerKeys.Key)
    (built : integerGroup domain = .ok (some key)) : key.width = 1 := by
  unfold integerGroup at built
  split at built
  · split at built
    · cases built
    · cases built; rfl
  · cases built; rfl
  · cases built

/-- An empty integer table removes its group, rather than creating an invalid rank zero. -/
theorem integerGroup_empty (domain : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points [SourceGuards.valueName] (FullSyntax.lowerFormula domain) = .ok points)
    (empty : points.count = 0) : integerGroup domain = .ok none := by
  simp [integerGroup, built, empty]

/-- Unbounded domains are retained for a later constructor condition. -/
theorem integerGroup_unbounded (domain : FullSyntax.Formula)
    (unbounded : LatticeAPI.points [SourceGuards.valueName] (FullSyntax.lowerFormula domain) =
      .error (.elimination .unboundedVariable)) : integerGroup domain = .ok (some (integerKey domain none)) := by
  simp [integerGroup, unbounded]

/-- A successful generated key list has exactly the width read by the source value function. -/
theorem compileKeys_width (recipe : Recipe α) (keys : List OpenIntegerKeys.Key)
    (built : compileKeys recipe = .ok (some keys)) :
    (keys.map OpenIntegerKeys.Key.width).sum = OpenIntegerReaders.width (reader recipe) := by
  induction recipe generalizing keys with
  | pure value => simp [compileKeys] at built; subst keys; rfl
  | integer domain =>
      cases grouped : integerGroup domain with
      | error error => simp [compileKeys, grouped, Except.map] at built
      | ok group => cases group with
        | none => simp [compileKeys, grouped, Except.map] at built
        | some key =>
            simp [compileKeys, grouped, Except.map] at built
            subst keys
            simp [integerGroup_width domain key grouped, reader, OpenIntegerReaders.width, OpenIntegerReaders.counts]
  | map transform inner ih | pay inner ih => exact ih keys built
  | app functions arguments ihf iha =>
      cases left : compileKeys functions with
      | error error => simp [compileKeys, left, Bind.bind, Except.bind] at built
      | ok group => cases group with
        | none => simp [compileKeys, left, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
        | some functionKeys => cases right : compileKeys arguments with
          | error error => simp [compileKeys, left, right, Bind.bind, Except.bind] at built
          | ok group => cases group with
            | none => simp [compileKeys, left, right, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
            | some argumentKeys =>
                have same : keys = functionKeys ++ argumentKeys := by
                  simpa [compileKeys, left, right, Bind.bind, Except.bind, Pure.pure, Except.pure] using built.symm
                subst keys
                simp [List.map_append, List.sum_append, ihf functionKeys left, iha argumentKeys right,
                  reader, OpenIntegerReaders.width, OpenIntegerReaders.counts]

/-- The generated open static source has one original outcome before point application. -/
theorem source_count (recipe : Recipe α) : StaticCandidateRanks.cardinality (source (Symbol := Symbol) recipe) = 1 := by
  induction recipe with
  | pure value | integer domain => rfl
  | map transform inner ih | pay inner ih => exact ih
  | app functions arguments ihf iha => simp [source, StaticCandidateRanks.cardinality, ihf, iha]

/-- Rank zero selects the typed ordinary-application reference template. -/
theorem source_select (recipe : Recipe α) :
    StaticCandidateRanks.select (source (Symbol := Symbol) recipe) 0 = some (IntegerTermViews.template (reader recipe)) := by
  induction recipe with
  | pure value | integer domain => rfl
  | map transform inner ih | pay inner ih => exact ih
  | app functions arguments ihf iha =>
      simp [source, StaticCandidateRanks.select, source_count, ihf, iha,
        reader, IntegerTermViews.template, Bind.bind, Option.bind]

/-- Every generated callback accepts the filling of its original term. -/
theorem source_compatible (specialize : List Int → Symbol → Symbol) (recipe : Recipe α) :
    StaticCandidateRanks.Compatible specialize (source recipe) := by
  induction recipe with
  | pure value | integer domain => trivial
  | map transform inner ih | pay inner ih => exact ih
  | app functions arguments ihf iha => exact ⟨ihf, iha⟩

/-- Source selection and key construction derive the required dimension for every candidate. -/
theorem source_dimension (recipe : Recipe α) (keys : List OpenIntegerKeys.Key)
    (built : compileKeys recipe = .ok (some keys)) (rank : Nat) (term : Term (Label Symbol))
    (found : StaticCandidateRanks.select (source recipe) rank = some term) :
    IntegerTermViews.count term = (OpenIntegerKeys.join keys).width := by
  have bound := StaticCandidateRanks.selected_bound (StaticCandidateRanks.select_sound _ _ _ found)
  rw [source_count] at bound
  have zero : rank = 0 := by omega
  subst rank
  rw [source_select] at found
  cases found
  exact (IntegerTermViews.template_count _).trans (compileKeys_width recipe keys built).symm

/-- Closing the reference applicative tree gives exact ranks with constructor-derived dimensions. -/
theorem compiled_ranks_exact
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (recipe : Recipe α) (keys : List OpenIntegerKeys.Key)
    (compiled : compileKeys recipe = .ok (some keys)) (points : LatticeAPI.Points)
    (closed : LatticeAPI.points (OpenIntegerKeys.names (OpenIntegerKeys.join keys).width)
      (FullSyntax.lowerFormula (OpenIntegerKeys.join keys).formula) = .ok points)
    (view : IntegerTermViews.View) (wanted : List (Term (Label IntegerLabelCodec.Symbol))) (rank : Nat) :
    rank ∈ StaticCandidateRanks.pointCandidates IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
      points (source recipe) view wanted ↔
      ∃ pointRank : Fin (LatticeSelect.pointCount points.levels), rank = pointRank.val ∧
        IntegerTermViews.decodeView IntegerLabelCodec.integerSymbol specialize points view
          (IntegerTermViews.template (reader recipe)) pointRank = wanted := by
  constructor
  · intro member
    obtain ⟨originalRank, original, found, pointRank, same, decoded, _⟩ :=
      StaticCandidateRanks.pointCandidates_sound IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
        _ _ points closed (source recipe) view wanted rank member
    have bound := StaticCandidateRanks.selected_bound (StaticCandidateRanks.select_sound _ _ _ found)
    rw [source_count] at bound
    have zero : originalRank = 0 := by omega
    subst originalRank
    rw [source_select] at found
    cases found
    exact ⟨pointRank, by simpa [Probability.pairRank] using same, decoded⟩
  · rintro ⟨pointRank, rfl, rfl⟩
    have member := StaticCandidateRanks.pointCandidates_complete
      IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue IntegerLabelCodec.leafValue_integer
      _ _ points closed (source recipe) (source_compatible specialize recipe)
      0 (IntegerTermViews.template (reader recipe)) (source_select recipe)
      (by simpa [OpenIntegerKeys.names] using source_dimension recipe keys compiled 0 _ (source_select recipe)) view pointRank
    simpa [Probability.pairRank] using member

/-- Every rank in the reference applicative tree gives a distinct term under every source view. -/
theorem compiled_decode_injective
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (recipe : Recipe α) (keys : List OpenIntegerKeys.Key)
    (compiled : compileKeys recipe = .ok (some keys)) (points : LatticeAPI.Points)
    (closed : LatticeAPI.points (OpenIntegerKeys.names (OpenIntegerKeys.join keys).width)
      (FullSyntax.lowerFormula (OpenIntegerKeys.join keys).formula) = .ok points)
    (view : IntegerTermViews.View) :
    Function.Injective (IntegerTermViews.decodeView IntegerLabelCodec.integerSymbol specialize points view
      (IntegerTermViews.template (reader recipe))) := by
  exact IntegerTermViews.decode_injective IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
    IntegerLabelCodec.leafValue_integer _ _ points closed view _ (IntegerTermViews.template_valid _)
    (by simpa [OpenIntegerKeys.names] using source_dimension recipe keys compiled 0 _ (source_select recipe))

/-- The generated value reader never reaches an empty integer access at a valid closure rank. -/
theorem compiled_value_total (recipe : Recipe α) (keys : List OpenIntegerKeys.Key)
    (compiled : compileKeys recipe = .ok (some keys)) (points : LatticeAPI.Points)
    (closed : LatticeAPI.points (OpenIntegerKeys.names (OpenIntegerKeys.join keys).width)
      (FullSyntax.lowerFormula (OpenIntegerKeys.join keys).formula) = .ok points)
    (rank : Fin (LatticeSelect.pointCount points.levels)) :
    ∃ value, OpenIntegerReaders.evaluate (reader recipe)
      (LatticeSelect.decode points.dimension points.levels rank) = some value := by
  have exactness := LatticeSelect.points_api_exact _ _ points closed
  have dimension := ((exactness.2.2.1 _).mpr ⟨rank, rfl⟩).1
  apply OpenIntegerReaders.evaluate_total
  simpa [OpenIntegerKeys.names, OpenIntegerKeys.join, compileKeys_width recipe keys compiled] using dimension

/-- The source callback's hole-count invariant is preserved by local static combinators. -/
inductive Shape : Nat → StaticCandidateRanks.Source Symbol → Prop where
  | pure : Shape 0 .pure
  | hole : Shape 1 .hole
  | indexed (members : Nat) : Shape 0 (.indexed members)
  | map {width inner} : Shape width inner → Shape width (.map inner)
  | pay {width inner} : Shape width inner → Shape width (.pay inner)
  | app {left right functions arguments} : Shape left functions → Shape right arguments →
      Shape (left + right) (.app functions arguments)
  | choice {width left right} : Shape width left → Shape width right → Shape width (.choice left right)
  | label {width inner} (symbol : Symbol) (acceptsLabel : Symbol → Bool) : Shape width inner →
      Shape width (.label symbol acceptsLabel inner)

/-- Every source-selected member inherits its dimension from the generating constructors. -/
theorem shape_selected (literal : Int → Symbol) {width : Nat} {plan : StaticCandidateRanks.Source Symbol}
    (shape : Shape width plan) (rank : Nat) (term : Term (Label Symbol))
    (selected : StaticCandidateRanks.Selected plan rank term) : IntegerTermViews.count term = width := by
  induction shape generalizing rank term with
  | pure => cases selected; simp [IntegerTermViews.count, IntegerTermViews.adapt, IntegerTermViews.adaptForest,
      IntegerTermViews.adaptLabel, RecipeCompile.holes, RecipeCompile.forestHoles]
  | hole => cases selected; simp [IntegerTermViews.count, IntegerTermViews.adapt, IntegerTermViews.adaptLabel, RecipeCompile.holes]
  | indexed members => cases selected; simp [IntegerTermViews.count, IntegerTermViews.adapt, IntegerTermViews.adaptForest,
      IntegerTermViews.adaptLabel, RecipeCompile.holes, RecipeCompile.forestHoles]
  | map shape ih => cases selected with | map child => exact ih _ _ child
  | pay shape ih => cases selected with | pay child => exact ih _ _ child
  | app left right ihl ihr =>
      cases selected with
      | app first second =>
          have firstCount := ihl _ _ first
          have secondCount := ihr _ _ second
          simp only [IntegerTermViews.count, IntegerTermViews.adapt, IntegerTermViews.adaptForest,
            IntegerTermViews.adaptLabel, RecipeCompile.holes, RecipeCompile.forestHoles] at firstCount secondCount ⊢
          omega
  | choice left right ihl ihr =>
      cases selected with
      | left chosen => simpa [IntegerTermViews.count, IntegerTermViews.adapt, IntegerTermViews.adaptForest,
          IntegerTermViews.adaptLabel, RecipeCompile.holes, RecipeCompile.forestHoles] using ihl _ _ chosen
      | right chosen => simpa [IntegerTermViews.count, IntegerTermViews.adapt, IntegerTermViews.adaptForest,
          IntegerTermViews.adaptLabel, RecipeCompile.holes, RecipeCompile.forestHoles] using ihr _ _ chosen
  | label symbol acceptsLabel inner ih =>
      cases selected with
      | label _ _ chosen =>
          rw [IntegerTermViews.label_count literal symbol _ (StaticCandidateRanks.selected_valid chosen)]
          exact ih _ _ chosen

/-- The generated recipe supplies the callback shape without an output invariant premise. -/
theorem source_shape (recipe : Recipe α) :
    Shape (OpenIntegerReaders.width (reader recipe)) (source (Symbol := Symbol) recipe) := by
  induction recipe with
  | pure value => exact .pure
  | integer domain => exact .hole
  | map transform inner ih => exact .map ih
  | pay inner ih => exact .pay ih
  | app functions arguments ihf iha =>
      simpa [reader, source, OpenIntegerReaders.width, OpenIntegerReaders.counts] using Shape.app ihf iha

/-- The decoder's sequential assignment reads exactly the tuple positions that it wrote. -/
theorem assignTuple_read (assignment : Nat → Int) (start : Nat) (tuple : List Int) (index : Nat) :
    LatticeSelect.assignTuple assignment start tuple index =
      if start ≤ index then tuple[index - start]?.getD (assignment index) else assignment index := by
  induction tuple generalizing assignment start with
  | nil => simp [LatticeSelect.assignTuple]
  | cons first rest ih =>
      rw [LatticeSelect.assignTuple, ih]
      by_cases before : index < start
      · simp [show ¬start ≤ index by omega, show ¬start + 1 ≤ index by omega,
          LatticeBound.update, show index ≠ start by omega]
      · by_cases same : index = start
        · subst index
          simp [LatticeBound.update, show ¬start + 1 ≤ start by omega]
        · have after : start + 1 ≤ index := by omega
          have distance : index - start = (index - (start + 1)) + 1 := by omega
          simp [after, show start ≤ index by omega, distance, LatticeBound.update, same]

/-- The public decoder's zero assignment is exactly optional tuple indexing with zero outside the tuple. -/
theorem assignTuple_zero (tuple : List Int) :
    LatticeSelect.assignTuple (fun _ => 0) 0 tuple = fun index => tuple[index]?.getD 0 := by
  funext index
  simp [assignTuple_read]

/-- Enumerate the actual public point decoder's finite rank interval. -/
def pointDomain (points : LatticeAPI.Points) : List (List Int) :=
  List.ofFn (LatticeSelect.decode points.dimension points.levels)

/-- Public lattice success derives the exact distinct tuple domain of a child record. -/
theorem pointDomain_exact (width : Nat) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points (OpenIntegerKeys.names width) (FullSyntax.lowerFormula formula) = .ok points)
    (tuple : List Int) :
    tuple ∈ pointDomain points ↔ tuple.length = width ∧
      FullSyntax.Holds FullSyntax.integerModel (OpenIntegerKeys.tupleEnv tuple) formula := by
  have exactness := LatticeSelect.points_api_exact _ _ points built
  simp only [pointDomain, List.mem_ofFn]
  constructor
  · intro member
    have admitted := (exactness.2.2.1 tuple).mpr member
    have dimension : tuple.length = width := by simpa [OpenIntegerKeys.names] using admitted.1
    refine ⟨dimension, ?_⟩
    simpa [OpenIntegerKeys.tupleEnv, dimension, assignTuple_zero] using admitted.2
  · rintro ⟨dimension, admitted⟩
    apply (exactness.2.2.1 tuple).mp
    refine ⟨by simpa [OpenIntegerKeys.names] using dimension, ?_⟩
    simpa [OpenIntegerKeys.tupleEnv, dimension, assignTuple_zero] using admitted

/-- The actual lattice decoder yields distinct child tuples. -/
theorem pointDomain_distinct (width : Nat) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points (OpenIntegerKeys.names width) (FullSyntax.lowerFormula formula) = .ok points) :
    (pointDomain points).Nodup := by
  have exactness := LatticeSelect.points_api_exact _ _ points built
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj before same
  simp only [pointDomain, List.length_ofFn] at hi hj
  have ranks : (⟨i, hi⟩ : Fin (LatticeSelect.pointCount points.levels)) = ⟨j, hj⟩ :=
    exactness.2.2.2 (by simpa [pointDomain] using same)
  have equal : i = j := congrArg Fin.val ranks
  omega

/-- The source stored count is derived from its successful public decoder table. -/
theorem pointDomain_count (width : Nat) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points (OpenIntegerKeys.names width) (FullSyntax.lowerFormula formula) = .ok points) :
    (pointDomain points).length = points.count.toNat := by
  simpa [pointDomain] using (LatticeSelect.points_api_exact _ _ points built).1.symm

/-- A local grouping merge combines only callback sources with the same key width. -/
theorem merged_shape (key : OpenIntegerKeys.Key) (left right : StaticCandidateRanks.Source Symbol)
    (leftShape : Shape key.width left) (rightShape : Shape key.width right) :
    Shape key.width (.choice left right) := .choice leftShape rightShape

/-- Source application derives its new width from the actual joined keys. -/
theorem joined_shape (leftKey rightKey : OpenIntegerKeys.Key)
    (functions arguments : StaticCandidateRanks.Source Symbol)
    (leftShape : Shape leftKey.width functions) (rightShape : Shape rightKey.width arguments) :
    Shape (OpenIntegerKeys.join [leftKey, rightKey]).width (.app functions arguments) := by
  simpa [OpenIntegerKeys.join] using Shape.app leftShape rightShape

/-- Actual successful constructor-label specialization supplies compatibility, while labelling preserves the key width. -/
theorem labelled_shape_compatible
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (key : OpenIntegerKeys.Key) (inner : StaticCandidateRanks.Source IntegerLabelCodec.Symbol)
    (symbol : IntegerLabelCodec.Symbol) (shape : Shape key.width inner)
    (compatible : StaticCandidateRanks.Compatible specialize inner)
    (specialized : ∀ point, IntegerLabelCodec.exactLabel point symbol = .ok (specialize point symbol)) :
    Shape key.width (.label symbol (IntegerLabelCodec.fills symbol) inner) ∧
      StaticCandidateRanks.Compatible specialize (.label symbol (IntegerLabelCodec.fills symbol) inner) :=
  ⟨.label symbol _ shape, StaticCandidateRanks.integer_label_compatible specialize symbol inner specialized compatible⟩

/-- Integer leaf domains bind the source value name and have no other free name. -/
def LeafScoped (domain : FullSyntax.Formula) : Prop :=
  ∀ name ∈ FullSyntax.formulaNames domain, name = SourceGuards.valueName

/-- Actual leaf renaming preserves its one-variable formula meaning. -/
theorem integerKey_formula (domain : FullSyntax.Formula) (within : LeafScoped domain)
    (stored : Option Nat) (value : Int) :
    FullSyntax.Holds FullSyntax.integerModel (OpenIntegerKeys.tupleEnv [value]) (integerKey domain stored).formula ↔
      LatticeSingleton.Admits SourceGuards.valueName domain value := by
  unfold integerKey
  rw [SourceFormula.substitute_semantics FullSyntax.integerModel (by intro value; rfl)]
  apply FormulaSemantics.formula_ext
  intro name member
  rw [within name member]
  have coordinate := OpenIntegerKeys.tupleEnv_at [value] 0 (by simp)
  simp only [List.getElem?_cons_zero, Option.getD_some] at coordinate
  have filtered :
      ((SourceFormula.replacements [(SourceGuards.valueName, IntegerLabelCodec.integerName 0)]).filter
        fun entry => !FullSyntax.identityReplacement entry) =
        [(SourceGuards.valueName, FullSyntax.Term.var (IntegerLabelCodec.integerName 0))] := by decide +kernel
  rw [filtered]
  simpa [FormulaSubstitution.assignment, FullSyntax.lookup, FullSyntax.evaluateTerm,
    LatticeInput.nameValues, LatticeInput.variableOf, assignTuple_zero] using coordinate

/-- A finite integerGroup record contains exactly the actual decoder's renamed singleton tuples. -/
theorem integerGroup_domain (domain : FullSyntax.Formula) (within : LeafScoped domain)
    (points : LatticeAPI.Points)
    (built : LatticeAPI.points [SourceGuards.valueName] (FullSyntax.lowerFormula domain) = .ok points)
    (tuple : List Int) :
    tuple ∈ pointDomain points ↔ tuple.length = 1 ∧
      FullSyntax.Holds FullSyntax.integerModel (OpenIntegerKeys.tupleEnv tuple)
        (integerKey domain (some points.count.toNat)).formula := by
  have exactness := LatticeSelect.points_api_exact _ _ points built
  have member : tuple ∈ pointDomain points ↔ tuple.length = 1 ∧
      FullSyntax.Holds FullSyntax.integerModel
        (LatticeInput.nameValues [SourceGuards.valueName] (LatticeSelect.assignTuple (fun _ => 0) 0 tuple)) domain := by
    simpa [pointDomain] using (exactness.2.2.1 tuple).symm
  rw [member]
  apply and_congr_right
  intro dimension
  cases tuple with
  | nil => simp at dimension
  | cons value rest =>
      have empty : rest = [] := by simpa using dimension
      subst rest
      exact (integerKey_formula domain within _ value).symm

/-- A retained finite leaf stores its actual public point count, with no assumed cardinality equation. -/
theorem integerGroup_finite (domain : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points [SourceGuards.valueName] (FullSyntax.lowerFormula domain) = .ok points)
    (nonempty : points.count ≠ 0) :
    integerGroup domain = .ok (some (integerKey domain (some (pointDomain points).length))) := by
  have count : (pointDomain points).length = points.count.toNat := by
    simpa [pointDomain] using (LatticeSelect.points_api_exact _ _ points built).1.symm
  simp [integerGroup, built, nonempty, count]

/-- A finite integer leaf has no duplicate tuple in its actual decoder domain. -/
theorem integerGroup_distinct (domain : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points [SourceGuards.valueName] (FullSyntax.lowerFormula domain) = .ok points) :
    (pointDomain points).Nodup := by
  have exactness := LatticeSelect.points_api_exact _ _ points built
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj before same
  simp only [pointDomain, List.length_ofFn] at hi hj
  have ranks : (⟨i, hi⟩ : Fin (LatticeSelect.pointCount points.levels)) = ⟨j, hj⟩ :=
    exactness.2.2.2 (by simpa [pointDomain] using same)
  have equal : i = j := congrArg Fin.val ranks
  omega

end MicroCFTA.OpenIntegerSource
