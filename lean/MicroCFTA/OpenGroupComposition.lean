import MicroCFTA.OpenChoiceRouting
import MicroCFTA.ParentIntegerSettlement
import MicroCFTA.CompiledIntegerSpine
import MicroCFTA.MassRetention

/-!
# Repeated finite open keys and heterogeneous point closure

The compiler groups original static members before it closes their integer
coordinates. A group has one formula and width. Different groups can have
different formulas and widths. Repeated keys retain all original occurrences.
-/
namespace MicroCFTA.OpenGroupComposition
open Language GeneratorCombinators IntegerTermViews OpenIntegerKeys OpenIntegerSource

/-- A retained original comes from the executable bare-spine compiler. -/
structure Original (Value : Type) where
  recipe : Recipe Value
  keys : List Key
  compiled : compileKeys recipe = .ok (some keys)
  observation : Nat
  origin : Nat
  mass : Rat

/-- Compile the original record rather than assuming a template or reader dimension. -/
def compileOriginal (recipe : Recipe Value) (observation origin : Nat) (mass : Rat) :
    Except (LatticeAPI.Error String) (Option (Original Value)) :=
  match found : compileKeys recipe with
  | .error error => .error error
  | .ok none => .ok none
  | .ok (some keys) => .ok (some ⟨recipe, keys, found, observation, origin, mass⟩)

/-- Equality of source open keys includes the point record as well as formula and width. -/
structure Signature where
  observation : Nat
  width : Nat
  formula : FullSyntax.Formula
  points : Option Nat
  deriving DecidableEq

/-- The original's actual joined key, with its opaque observation identity. -/
def signature (original : Original Value) : Signature :=
  let key := join original.keys
  ⟨original.observation, key.width, key.formula, key.points⟩

/-- Recover the coordinate fields of an actual open-key signature. -/
def openKey (key : Signature) : Key := ⟨key.width, key.formula, key.points⟩

/-- Source groupOutcomes preserves input order inside equal keys and sorts the groups. -/
def groups (before : Signature → Signature → Bool) (originals : List (Original Value)) :
    List (List (Original Value)) := groupOutcomes before signature originals

/-- Every original occurrence survives grouping, including repeated recipes and repeated keys. -/
theorem groups_perm (before : Signature → Signature → Bool) (originals : List (Original Value)) :
    (groups before originals).flatten.Perm originals := groupOutcomes_perm before signature originals

/-- A returned source group has one actual key and at least one original member. -/
theorem groups_homogeneous (before : Signature → Signature → Bool) (originals group : List (Original Value))
    (present : group ∈ groups before originals) :
    ∃ first rest, group = first :: rest ∧ ∀ original ∈ group, signature original = signature first :=
  groupOutcomes_key before signature originals group present

/-- Successful source compilation derives each original template's coordinate width. -/
theorem original_width (original : Original Value) :
    count (CompiledIntegerSpine.template (Symbol := Symbol) original.recipe) = (signature original).width :=
  (CompiledIntegerSpine.template_count original.recipe).trans
    (compileKeys_width original.recipe original.keys original.compiled).symm

/-- Positive singleton bucket merging keeps the original term; other groups use local Choice indexes. -/
def selected (group : List (Original Value)) (rank : Fin group.length) : Term (Label Symbol) :=
  let term := CompiledIntegerSpine.template group[rank.val].recipe
  if group.length = 1 then term else .node (.choice rank.val) [term]

/-- Choice wrappers add no integer coordinate. -/
theorem choice_count (branch : Nat) (term : Term (Label Symbol)) :
    count (.node (.choice branch) [term]) = count term := by
  simp [count, adapt, adaptLabel, adaptForest, RecipeCompile.holes, RecipeCompile.forestHoles]

/-- Private frequency wrappers preserve the source fill-shape invariant. -/
theorem selected_valid (group : List (Original Value)) (rank : Fin group.length) :
    Valid (selected (Symbol := Symbol) group rank) := by
  have valid := CompiledIntegerSpine.template_valid (Symbol := Symbol) group[rank.val].recipe
  simp only [selected]
  split
  · exact valid
  · simpa [Valid] using valid

/-- Grouping derives a common width, without requiring all input groups to share one width. -/
theorem selected_width (group : List (Original Value)) (key : Signature)
    (sameKey : ∀ original ∈ group, signature original = key) (rank : Fin group.length) :
    count (selected (Symbol := Symbol) group rank) = key.width := by
  have same := congrArg Signature.width (sameKey group[rank.val] (List.getElem_mem rank.isLt))
  simp only [selected]
  split
  · exact (original_width _).trans same
  · exact (choice_count _ _).trans ((original_width _).trans same)

/-- The actual original-selector lookup retains the singleton fast path. -/
def select (group : List (Original Value)) (rank : Nat) : Option (Term (Label Symbol)) :=
  if bound : rank < group.length then some (selected group ⟨rank, bound⟩) else none

/-- Each local source selector index is valid and returns its constructed term. -/
theorem select_selected (group : List (Original Value)) (rank : Fin group.length) :
    select (Symbol := Symbol) group rank.val = some (selected group rank) := by simp [select, rank.isLt]

/-- The original callback for one merged branch follows source private-label matching. -/
def branchCandidates (recipe : Recipe Value) (branch : Nat) :
    View → List (Term (Label Symbol)) → List Nat
  | .labelled, wanted => (CompiledIntegerSpine.candidates recipe .labelled wanted).map (branch + ·)
  | _, [.node (.choice found) [term]] =>
      if found = branch then (CompiledIntegerSpine.candidates recipe .whole [term]).map (branch + ·) else []
  | _, _ => []

/-- Every bare-spine original has cardinality one before point closure. -/
def frequencyCandidates (first : Nat) (group : List (Original Value))
    (view : View) (wanted : List (Term (Label Symbol))) : List Nat :=
  match group with
  | [] => []
  | original :: rest => branchCandidates original.recipe first view wanted ++
      frequencyCandidates (first + 1) rest view wanted

/-- Source singleton merging bypasses frequencyStatic entirely. -/
def candidates (group : List (Original Value)) (view : View) (wanted : List (Term (Label Symbol))) : List Nat :=
  match group with
  | [original] => CompiledIntegerSpine.candidates original.recipe view wanted
  | _ => frequencyCandidates 0 group view wanted

/-- A source frequency branch discovers its original after point filling in all views. -/
theorem branch_complete (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (original : Original Value) (point : List Int) (view : View) (branch : Nat) :
    branch ∈ branchCandidates original.recipe branch view
      (project view (fill literal exactLabel point
        (.node (.choice branch) [CompiledIntegerSpine.template original.recipe])).2) := by
  have whole := CompiledIntegerSpine.candidate_complete literal exactLabel original.recipe point .whole
  have labelled := CompiledIntegerSpine.candidate_complete literal exactLabel original.recipe point .labelled
  simp only [project] at whole labelled
  cases view <;> simp [branchCandidates, project, fill, fillForest, IntegerTermViews.labelled, spine,
    SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren, whole, labelled]

/-- The local branch occurrence index survives any number of preceding equal-key originals. -/
theorem frequency_complete (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (before after : List (Original Value)) (original : Original Value)
    (point : List Int) (view : View) (first : Nat) :
    first + before.length ∈ frequencyCandidates first (before ++ original :: after) view
      (project view (fill literal exactLabel point
        (.node (.choice (first + before.length)) [CompiledIntegerSpine.template original.recipe])).2) := by
  induction before generalizing first with
  | nil =>
      simpa [frequencyCandidates] using List.mem_append_left
        (frequencyCandidates (first + 1) after view _)
        (branch_complete literal exactLabel original point view first)
  | cons head rest ih =>
      apply List.mem_append_right
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (first + 1)

/-- The merged source callbacks preserve every original occurrence, even when visible views coincide. -/
theorem candidates_complete (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (group : List (Original Value)) (rank : Fin group.length) (point : List Int) (view : View) :
    rank.val ∈ candidates group view (project view (fill literal exactLabel point (selected group rank)).2) := by
  by_cases singleton : group.length = 1
  · have zero : rank.val = 0 := by have bound := rank.isLt; omega
    cases group with
    | nil => simp at singleton
    | cons first rest =>
        have emptyRest : rest = [] := by simpa using singleton
        subst rest
        simpa [candidates, selected, zero] using
          CompiledIntegerSpine.candidate_complete literal exactLabel first.recipe point view
  · have decomposition : group = group.take rank.val ++ group[rank.val] :: group.drop (rank.val + 1) := by
      rw [← List.drop_eq_getElem_cons rank.isLt, List.take_append_drop]
    have member := frequency_complete literal exactLabel (group.take rank.val) (group.drop (rank.val + 1))
      group[rank.val] point view 0
    have length : (group.take rank.val).length = rank.val := List.length_take_of_le (Nat.le_of_lt rank.isLt)
    rw [length, Nat.zero_add, ← decomposition] at member
    cases group with
    | nil => exact Fin.elim0 rank
    | cons first rest =>
        cases rest with
        | nil => simp at singleton
        | cons next later => simpa [candidates, selected, singleton] using member

/-- Execute pointsStatic after the actual equal-key static merge. -/
def pointCandidates [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (group : List (Original Value)) (points : LatticeAPI.Points)
    (view : View) (wanted : List (Term (Label Symbol))) : List Nat :=
  (candidates group view wanted).flatMap fun originalRank =>
    match select group originalRank with
    | none => []
    | some original =>
        match rankView literal exactLabel read points view original wanted with
        | none => []
        | some pointRank => [Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank pointRank]

/-- Every original occurrence and every point get their actual mixed-radix rank. -/
theorem points_complete [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (group : List (Original Value)) (key : Signature)
    (sameKey : ∀ original ∈ group, signature original = key)
    (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names key.width) (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (originalRank : Fin group.length) (pointRank : Fin (LatticeSelect.pointCount points.levels)) :
    Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank.val pointRank.val ∈
      pointCandidates literal exactLabel read group points view
        (decodeView literal exactLabel points view (selected group originalRank) pointRank) := by
  apply List.mem_flatMap.mpr
  refine ⟨originalRank.val, candidates_complete literal exactLabel group originalRank _ view, ?_⟩
  rw [select_selected]
  simp only []
  rw [rank_decode literal exactLabel read literalRead (names key.width) formula points built view
    (selected group originalRank) (selected_valid group originalRank)
    (by simpa [names] using selected_width group key sameKey originalRank) pointRank]
  simp

/-- The final source view check rejects every candidate outside a selected original's point language. -/
theorem points_sound [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (group : List (Original Value)) (declared : List FullSyntax.Name)
    (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points declared (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (wanted : List (Term (Label Symbol))) (rank : Nat)
    (accepted : rank ∈ pointCandidates literal exactLabel read group points view wanted) :
    ∃ originalRank : Fin group.length, ∃ pointRank : Fin (LatticeSelect.pointCount points.levels),
      rank = Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank.val pointRank.val ∧
      decodeView literal exactLabel points view (selected group originalRank) pointRank = wanted := by
  obtain ⟨originalRank, _, accepted⟩ := List.mem_flatMap.mp accepted
  by_cases bound : originalRank < group.length
  · simp only [select, bound, ↓reduceDIte] at accepted
    cases ranked : rankView literal exactLabel read points view (selected group ⟨originalRank, bound⟩) wanted with
    | none => simp [ranked] at accepted
    | some pointRank =>
        have same : rank = Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank pointRank := by
          simpa [ranked] using accepted
        obtain ⟨validRank, value, decoded⟩ := rankView_sound literal exactLabel read declared formula points built
          view (selected group ⟨originalRank, bound⟩) wanted pointRank ranked
        exact ⟨⟨originalRank, bound⟩, validRank, by simpa [value] using same, decoded⟩
  · simp [select, bound] at accepted

/-- The merged group has exactly its original occurrences times its own point table. -/
theorem group_ranks_exact [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (group : List (Original Value)) (key : Signature)
    (sameKey : ∀ original ∈ group, signature original = key)
    (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names key.width) (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (wanted : List (Term (Label Symbol))) (rank : Nat) :
    rank ∈ pointCandidates literal exactLabel read group points view wanted ↔
      ∃ originalRank : Fin group.length, ∃ pointRank : Fin (LatticeSelect.pointCount points.levels),
        rank = Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank.val pointRank.val ∧
        decodeView literal exactLabel points view (selected group originalRank) pointRank = wanted := by
  constructor
  · exact points_sound literal exactLabel read group _ formula points built view wanted rank
  · rintro ⟨originalRank, pointRank, rfl, rfl⟩
    exact points_complete literal exactLabel read literalRead group key sameKey formula points built view originalRank pointRank

/-- Every accepted rank lies in the source group's closed cardinality interval. -/
theorem points_rank_bound [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (group : List (Original Value)) (declared : List FullSyntax.Name)
    (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points declared (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (wanted : List (Term (Label Symbol))) (rank : Nat)
    (accepted : rank ∈ pointCandidates literal exactLabel read group points view wanted) :
    rank < group.length * LatticeSelect.pointCount points.levels := by
  obtain ⟨originalRank, pointRank, rfl, _⟩ := points_sound literal exactLabel read group declared formula points built view wanted rank accepted
  exact Probability.pairRank_lt originalRank.isLt pointRank.isLt

/-- Actual group partitioning discharges the common-width and common-key premises for closure. -/
theorem grouped_ranks_exact (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (before : Signature → Signature → Bool) (originals : List (Original Value))
    (first : Original Value) (rest : List (Original Value))
    (present : first :: rest ∈ groups before originals) (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (signature first).width)
      (FullSyntax.lowerFormula (signature first).formula) = .ok points)
    (view : View) (wanted : List (Term (Label IntegerLabelCodec.Symbol))) (rank : Nat) :
    rank ∈ pointCandidates IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
      (first :: rest) points view wanted ↔
      ∃ originalRank : Fin (first :: rest).length, ∃ pointRank : Fin (LatticeSelect.pointCount points.levels),
        rank = Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank.val pointRank.val ∧
        decodeView IntegerLabelCodec.integerSymbol specialize points view (selected (first :: rest) originalRank) pointRank = wanted := by
  obtain ⟨head, tail, same, homogeneous⟩ := groups_homogeneous before originals (first :: rest) present
  have headSame : head = first := (List.cons.inj same).1.symm
  subst head
  exact group_ranks_exact IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
    IntegerLabelCodec.leafValue_integer (first :: rest) (signature first) homogeneous
    (signature first).formula points built view wanted rank

/-- Grouping commutes with expansion by each group's own tuple table, up to occurrence order. -/
theorem expanded_groups_perm (before : Signature → Signature → Bool) (originals : List (Original Value))
    (points : Original Value → List Point) :
    ((groups before originals).flatMap (fun group => group.flatMap points)).Perm (originals.flatMap points) := by
  have same := (groups_perm before originals).flatMap_right points
  rw [List.flatten_eq_flatMap, List.flatMap_assoc] at same
  exact same

/-- The merge retains each original's incoming mass before conditional normalization. -/
def originalMasses (group : List (Original Value)) : Probability.Distribution Nat :=
  group.map (fun original => (original.mass, original.origin))

/-- The actual finite group merge uses a conditional original sampler and the uniform point sampler. -/
def settledDistribution (group : List (Original Value)) (kept : Rat) (points : LatticeAPI.Points) :
    Probability.Distribution (Nat × List Int) :=
  Probability.scale (Probability.total (originalMasses group) * kept)
    (Probability.product (Probability.normalize (originalMasses group))
      (Probability.normalize (Probability.counting (pointDomain points))))

/-- Expand the same closed members in original-major order with their retained masses. -/
def contributions (group : List (Original Value)) (kept : Rat) (tuples : List (List Int)) :
    Probability.Distribution (Nat × List Int) :=
  group.flatMap fun original => Probability.map (fun tuple => (original.origin, tuple))
    (Probability.scale (original.mass * kept) (Probability.normalize (Probability.counting tuples)))

/-- Bucket mass and its conditional static weights cancel exactly before integer closure. -/
theorem settled_expands (group : List (Original Value)) (kept : Rat) (points : LatticeAPI.Points)
    (positive : Probability.total (originalMasses group) ≠ 0) :
    settledDistribution group kept points = contributions group kept (pointDomain points) := by
  let source := originalMasses group
  let tupleDist := Probability.normalize (Probability.counting (pointDomain points))
  have scaled := MassRetention.product_scale (Probability.total source)⁻¹ 1 source tupleDist
  rw [Probability.scale_one, Rat.mul_one] at scaled
  change Probability.scale (Probability.total source * kept)
    (Probability.product (Probability.scale (Probability.total source)⁻¹ source) tupleDist) = _
  rw [scaled, Probability.scale_scale]
  have cancel : (Probability.total source * kept) * (Probability.total source)⁻¹ = kept := by
    calc
      _ = (Probability.total source * (Probability.total source)⁻¹) * kept := by
        rw [Rat.mul_assoc, Rat.mul_comm kept, ← Rat.mul_assoc]
      _ = kept := by rw [Rat.mul_inv_cancel _ positive, Rat.one_mul]
  rw [cancel]
  simp [source, tupleDist, originalMasses, contributions, Probability.scale, Probability.product,
    Probability.map, List.flatMap_map, List.map_flatMap, List.map_map, Rat.mul_assoc,
    Rat.mul_comm kept, Function.comp_def]

/-- Positive source bucket masses derive the nonzero normalization denominator. -/
theorem originalMasses_positive (group : List (Original Value)) (nonempty : group ≠ [])
    (positive : ∀ original ∈ group, 0 < original.mass) : 0 < Probability.total (originalMasses group) := by
  apply Sized.total_positive _ (by simpa [originalMasses] using nonempty)
  intro entry present
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
  exact positive original member

/-- Closing a merged group counts every original against every surviving integer point. -/
theorem settled_count (group : List (Original Value)) (kept : Rat) (points : LatticeAPI.Points)
    (key : Signature) (formula : FullSyntax.Formula)
    (built : LatticeAPI.points (names key.width) (FullSyntax.lowerFormula formula) = .ok points) :
    (settledDistribution group kept points).length = group.length * points.count.toNat := by
  simp only [settledDistribution, Probability.scale, List.length_map, Probability.product,
    List.length_flatMap, Probability.normalize, originalMasses]
  have count := pointDomain_count _ _ points built
  simp only [List.length_map, Probability.counting] at count ⊢
  rw [count]
  have constantSum (items : List (Original Value)) (count : Nat) :
      (items.map (fun _ => count)).sum = items.length * count := by
    induction items with
    | nil => simp
    | cons first rest ih => simp [ih, Nat.add_mul, Nat.add_comm]
  simpa [Function.comp_def] using constantSum group points.count.toNat

/-- One parent counter derives the restricted cardinality for the complete merged group. -/
theorem parent_group_count (group : List (Original Value)) (key : Signature) (parents : List FullSyntax.Formula)
    (child parent : LatticeAPI.Points)
    (childBuilt : LatticeAPI.points (names key.width) (FullSyntax.lowerFormula key.formula) = .ok child)
    (parentBuilt : LatticeAPI.points (names key.width)
      (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula [openKey key] parents)) = .ok parent) :
    group.length * parent.count.toNat = group.length *
      (ParentIntegerSettlement.retainedTuples (fun _ => pointDomain child) [openKey key] parents).length := by
  congr 1
  apply ParentIntegerSettlement.counted_parent_cardinality [openKey key] parents (fun _ => child)
  · intro childKey member
    have same : childKey = openKey key := by simpa using member
    subst childKey
    exact childBuilt
  · simpa [OpenIntegerKeys.join, openKey] using parentBuilt

/-- The source's uniform child tuples are retained separately from the original member weights. -/
noncomputable def priorRestricted (group : List (Original Value)) (key : Signature)
    (parents : List FullSyntax.Formula) (child : LatticeAPI.Points) :
    Probability.Distribution (Nat × List Int) :=
  group.flatMap fun original => Probability.map (fun tuple => (original.origin, tuple))
    (Probability.restrict (ParentIntegerSettlement.parentAllows parents)
      (Probability.scale original.mass (Probability.normalize
        (Probability.counting (joinedTuples (fun _ => pointDomain child) [openKey key])))))

/-- Actual child and parent counters derive each retained group's full value-event contribution. -/
theorem parent_group_event (group : List (Original Value)) (key : Signature) (parents : List FullSyntax.Formula)
    (child parent : LatticeAPI.Points)
    (childBuilt : LatticeAPI.points (names key.width) (FullSyntax.lowerFormula key.formula) = .ok child)
    (stored : key.points = some child.count.toNat)
    (parentBuilt : LatticeAPI.points (names key.width)
      (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula [openKey key] parents)) = .ok parent)
    (nonzero : Probability.total (originalMasses group) ≠ 0)
    (event : Nat × List Int → Bool) :
    Probability.eventMass event
      (settledDistribution group
        (RecipeCompile.retainedShare parent.count.toNat [ParentIntegerSettlement.childInfo (openKey key)]) parent) =
      Probability.eventMass event (priorRestricted group key parents child) := by
  rw [settled_expands group _ parent nonzero]
  clear nonzero
  induction group with
  | nil => rfl
  | cons first rest ih =>
      simp only [contributions, priorRestricted, List.flatMap_cons, Probability.eventMass_append,
        Probability.eventMass_map]
      have firstEvent := ParentIntegerSettlement.counted_parent_event [openKey key] parents (fun _ => child)
        (by
          intro childKey member
          have same : childKey = openKey key := by simpa using member
          subst childKey
          exact childBuilt)
        (by
          intro childKey member
          have same : childKey = openKey key := by simpa using member
          subst childKey
          exact stored)
        parent (by simpa [OpenIntegerKeys.join, openKey] using parentBuilt) first.mass (fun tuple => event (first.origin, tuple))
      simp only [List.map_cons, List.map_nil] at firstEvent
      simp only [Function.comp_def]
      rw [firstEvent]
      exact congrArg (_ + ·) ih

/-- Empty groups do not occur in groupOutcomes. The fallback makes the table projection total. -/
def groupKey : List (Original Value) → Signature
  | [] => ⟨0, 0, .top, some 1⟩
  | first :: _ => signature first

/-- Source settlement uses the table for this group's formula and width. -/
def groupDistribution (tables : Signature → LatticeAPI.Points)
    (group : List (Original Value)) : Probability.Distribution (Nat × List Int) :=
  let key := groupKey group
  let points := tables key
  settledDistribution group
    (RecipeCompile.retainedShare points.count.toNat [ParentIntegerSettlement.childInfo (openKey key)]) points

/-- The reference keeps each original weight and applies only its own key's parent restriction. -/
noncomputable def restrictedContribution (parents : Signature → List FullSyntax.Formula)
    (children : Signature → LatticeAPI.Points) (original : Original Value) :
    Probability.Distribution (Nat × List Int) :=
  Probability.map (fun tuple => (original.origin, tuple))
    (Probability.restrict (ParentIntegerSettlement.parentAllows (parents (signature original)))
      (Probability.scale original.mass (Probability.normalize
        (Probability.counting (joinedTuples (fun _ => pointDomain (children (signature original)))
          [openKey (signature original)])))))

/-- Homogeneous source keys derive the exact reference contribution for every member of a group. -/
theorem restricted_group (parents : Signature → List FullSyntax.Formula)
    (children : Signature → LatticeAPI.Points) (group : List (Original Value)) (key : Signature)
    (homogeneous : ∀ original ∈ group, signature original = key) :
    priorRestricted group key (parents key) (children key) =
      group.flatMap (restrictedContribution parents children) := by
  apply congrArg List.flatten
  apply List.map_congr_left
  intro original present
  simp [restrictedContribution, homogeneous original present]

/-- Event equality composes through the actual source-order concatenation of groups. -/
theorem event_flatMap (groups : List Group) (left right : Group → Probability.Distribution Output)
    (event : Output → Bool) (same : ∀ group ∈ groups,
      Probability.eventMass event (left group) = Probability.eventMass event (right group)) :
    Probability.eventMass event (groups.flatMap left) = Probability.eventMass event (groups.flatMap right) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      simp only [List.flatMap_cons, Probability.eventMass_append]
      rw [same group (by simp), ih (fun group present => same group (by simp [present]))]

/-- Heterogeneous grouping, per-group point counting, and settlement preserve every weighted event. -/
theorem heterogeneous_event (before : Signature → Signature → Bool) (originals : List (Original Value))
    (parents : Signature → List FullSyntax.Formula) (children tables : Signature → LatticeAPI.Points)
    (childBuilt : ∀ original ∈ originals,
      LatticeAPI.points (names (signature original).width) (FullSyntax.lowerFormula (signature original).formula) =
        .ok (children (signature original)))
    (stored : ∀ original ∈ originals, (signature original).points = some (children (signature original)).count.toNat)
    (parentBuilt : ∀ original ∈ originals,
      LatticeAPI.points (names (signature original).width)
        (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula
          [openKey (signature original)] (parents (signature original)))) = .ok (tables (signature original)))
    (positive : ∀ original ∈ originals, 0 < original.mass) (event : Nat × List Int → Bool) :
    Probability.eventMass event ((groups before originals).flatMap (groupDistribution tables)) =
      Probability.eventMass event (originals.flatMap (restrictedContribution parents children)) := by
  have each (group : List (Original Value)) (present : group ∈ groups before originals) :
      Probability.eventMass event (groupDistribution tables group) =
        Probability.eventMass event (group.flatMap (restrictedContribution parents children)) := by
    obtain ⟨first, rest, rfl, homogeneous⟩ := groups_homogeneous before originals group present
    have originalMember (original : Original Value) (member : original ∈ first :: rest) : original ∈ originals :=
      (groups_perm before originals).mem_iff.mp (List.mem_flatten.mpr ⟨first :: rest, present, member⟩)
    have firstMember := originalMember first (by simp)
    have nonzero := Rat.ne_of_gt (originalMasses_positive (first :: rest) (by simp)
      (fun original member => positive original (originalMember original member)))
    rw [groupDistribution, groupKey,
      parent_group_event (first :: rest) (signature first) (parents (signature first))
        (children (signature first)) (tables (signature first)) (childBuilt first firstMember)
        (stored first firstMember) (parentBuilt first firstMember) nonzero event,
      restricted_group parents children (first :: rest) (signature first) homogeneous]
  rw [event_flatMap _ _ _ event each]
  exact Probability.eventMass_perm event (expanded_groups_perm before originals (restrictedContribution parents children))

/-- Equality of every raw event also preserves the final source normalization. -/
theorem normalize_events (left right : Probability.Distribution Value)
    (same : ∀ event, Probability.eventMass event left = Probability.eventMass event right)
    (event : Value → Bool) :
    Probability.eventMass event (Probability.normalize left) =
      Probability.eventMass event (Probability.normalize right) := by
  have allTotal (distribution : Probability.Distribution Value) :
      Probability.eventMass (fun _ => true) distribution = Probability.total distribution := by
    induction distribution with
    | nil => rfl
    | cons entry rest ih => simp [Probability.eventMass, Probability.total, ih]
  have totals := same (fun _ => true)
  rw [allTotal, allTotal] at totals
  simp only [Probability.normalize, Probability.eventMass_scale, totals, same event]

/-- The normalized finite output is the original weighted stream conditioned by its key-specific guards. -/
theorem heterogeneous_conditioned (before : Signature → Signature → Bool) (originals : List (Original Value))
    (parents : Signature → List FullSyntax.Formula) (children tables : Signature → LatticeAPI.Points)
    (childBuilt : ∀ original ∈ originals,
      LatticeAPI.points (names (signature original).width) (FullSyntax.lowerFormula (signature original).formula) =
        .ok (children (signature original)))
    (stored : ∀ original ∈ originals, (signature original).points = some (children (signature original)).count.toNat)
    (parentBuilt : ∀ original ∈ originals,
      LatticeAPI.points (names (signature original).width)
        (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula
          [openKey (signature original)] (parents (signature original)))) = .ok (tables (signature original)))
    (positive : ∀ original ∈ originals, 0 < original.mass) (event : Nat × List Int → Bool) :
    Probability.eventMass event (Probability.normalize
      ((groups before originals).flatMap (groupDistribution tables))) =
      Probability.eventMass event (Probability.normalize
        (originals.flatMap (restrictedContribution parents children))) :=
  normalize_events _ _ (heterogeneous_event before originals parents children tables
    childBuilt stored parentBuilt positive) event

/-- A successful per-group settlement stores the actual table and source retained share. -/
structure Settlement (Value : Type) where
  key : Signature
  originals : List (Original Value)
  points : LatticeAPI.Points
  kept : Rat

/-- The finite one-child settlement executes its point query and drops zero-count groups. -/
def settleOne (parents : Signature → List FullSyntax.Formula) (group : List (Original Value)) :
    Except (LatticeAPI.Error String) (Option (Settlement Value)) :=
  match group with
  | [] => .ok none
  | first :: rest =>
      let key := signature first
      match LatticeAPI.points (names key.width)
        (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula [openKey key] (parents key))) with
      | .error error => .error error
      | .ok points =>
          if points.count = 0 then .ok none
          else .ok (some ⟨key, first :: rest, points,
            RecipeCompile.retainedShare points.count.toNat [ParentIntegerSettlement.childInfo (openKey key)]⟩)

/-- Traverse the ordered groups and retain successful nonempty settlements. -/
def settleAll (parents : Signature → List FullSyntax.Formula) :
    List (List (Original Value)) → Except (LatticeAPI.Error String) (List (Settlement Value))
  | [] => .ok []
  | group :: rest =>
      match settleOne parents group with
      | .error error => .error error
      | .ok current =>
          match settleAll parents rest with
          | .error error => .error error
          | .ok later => .ok (current.toList ++ later)

/-- Source counter errors are preserved before the empty-group decision. -/
theorem settle_error (parents : Signature → List FullSyntax.Formula) (first : Original Value)
    (rest : List (Original Value)) (error : LatticeAPI.Error String)
    (failed : LatticeAPI.points (names (signature first).width)
      (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula [openKey (signature first)]
        (parents (signature first)))) = .error error) :
    settleOne parents (first :: rest) = .error error := by simp [settleOne, failed]

/-- Every retained record uses the actual successful point table and its exact source mass update. -/
theorem settle_kept (parents : Signature → List FullSyntax.Formula) (first : Original Value)
    (rest : List (Original Value)) (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (signature first).width)
      (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula [openKey (signature first)]
        (parents (signature first)))) = .ok points) (nonempty : points.count ≠ 0) :
    settleOne parents (first :: rest) = .ok (some ⟨signature first, first :: rest, points,
      RecipeCompile.retainedShare points.count.toNat [ParentIntegerSettlement.childInfo (openKey (signature first))]⟩) := by
  simp [settleOne, built, nonempty]

/-- A zero table contains no decoded points, so dropping its group removes no replay outcome or mass. -/
theorem empty_settlement (group : List (Original Value)) (key : Signature) (formula : FullSyntax.Formula)
    (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names key.width) (FullSyntax.lowerFormula formula) = .ok points)
    (zero : points.count = 0) (kept : Rat) : settledDistribution group kept points = [] := by
  have length := pointDomain_count _ _ points built
  have noPoints : pointDomain points = [] := List.length_eq_zero_iff.mp (by simpa [zero] using length)
  simp [settledDistribution, noPoints, Probability.counting, Probability.normalize, Probability.scale,
    Probability.product, Probability.total]

/-- Successful traversal cannot silently discard a retained settlement from any source position. -/
theorem settleAll_complete (parents : Signature → List FullSyntax.Formula)
    (groups : List (List (Original Value))) (results : List (Settlement Value))
    (success : settleAll parents groups = .ok results) (group : List (Original Value)) (present : group ∈ groups)
    (record : Settlement Value) (kept : settleOne parents group = .ok (some record)) : record ∈ results := by
  induction groups generalizing results with
  | nil => simp at present
  | cons first rest ih =>
      cases current : settleOne parents first with
      | error error => simp [settleAll, current] at success
      | ok decision =>
          cases later : settleAll parents rest with
          | error error => simp [settleAll, current, later] at success
          | ok remaining =>
              have same : results = decision.toList ++ remaining := by simpa [settleAll, current, later] using success.symm
              rw [same]
              rcases List.mem_cons.mp present with rfl | member
              · have selected : decision = some record := Except.ok.inj (current.symm.trans kept)
                simp [selected]
              · exact List.mem_append_right _ (ih remaining later member)

/-- Every output settlement came from a successful nonempty input query. -/
theorem settleAll_sound (parents : Signature → List FullSyntax.Formula)
    (groups : List (List (Original Value))) (results : List (Settlement Value))
    (success : settleAll parents groups = .ok results) (record : Settlement Value) (present : record ∈ results) :
    ∃ group ∈ groups, settleOne parents group = .ok (some record) := by
  induction groups generalizing results with
  | nil => simp [settleAll] at success; subst results; simp at present
  | cons first rest ih =>
      cases current : settleOne parents first with
      | error error => simp [settleAll, current] at success
      | ok decision =>
          cases later : settleAll parents rest with
          | error error => simp [settleAll, current, later] at success
          | ok remaining =>
              have same : results = decision.toList ++ remaining := by simpa [settleAll, current, later] using success.symm
              rw [same, List.mem_append] at present
              rcases present with selected | present
              · have selected : decision = some record := by simpa using selected
                exact ⟨first, by simp, by rw [current, selected]⟩
              · obtain ⟨group, member, kept⟩ := ih remaining later present
                exact ⟨group, by simp [member], kept⟩

/-- Read the actual parent table. Failure has a total fallback that successful settlement never uses. -/
def countedTable (parents : Signature → List FullSyntax.Formula) (key : Signature) : LatticeAPI.Points :=
  match LatticeAPI.points (names key.width)
    (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula [openKey key] (parents key))) with
  | .ok points => points
  | .error _ => ⟨0, [], 0⟩

/-- Each emitted settlement expands the exact original records stored by the driver. -/
def settlementDistribution (record : Settlement Value) : Probability.Distribution (Nat × List Int) :=
  settledDistribution record.originals record.kept record.points

/-- A successful per-group query agrees with its complete table expansion, including the zero-count drop. -/
theorem settleOne_stream (parents : Signature → List FullSyntax.Formula) (group : List (Original Value))
    (record : Option (Settlement Value)) (success : settleOne parents group = .ok record) :
    record.toList.flatMap settlementDistribution = groupDistribution (countedTable parents) group := by
  cases group with
  | nil =>
      have empty : record = none := by simpa [settleOne] using success.symm
      simp [empty, groupDistribution, settledDistribution, originalMasses, Probability.normalize,
        Probability.scale, Probability.product]
  | cons first rest =>
      cases query : LatticeAPI.points (names (signature first).width)
        (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula [openKey (signature first)]
          (parents (signature first)))) with
      | error error => simp [settleOne, query] at success
      | ok points =>
          by_cases zero : points.count = 0
          · have empty : record = none := by simpa [settleOne, query, zero] using success.symm
            simp only [empty, Option.toList_none, List.flatMap_nil, groupDistribution, groupKey,
              countedTable, query]
            exact (empty_settlement (first :: rest) (signature first) _ points query zero _).symm
          · have same : record = some ⟨signature first, first :: rest, points,
                RecipeCompile.retainedShare points.count.toNat [ParentIntegerSettlement.childInfo (openKey (signature first))]⟩ := by
              simpa [settleOne, query, zero] using success.symm
            simp [same, settlementDistribution, groupDistribution, groupKey, countedTable, query]

/-- The exact error/drop traversal has the same complete weighted stream as all successful tables. -/
theorem settleAll_stream (parents : Signature → List FullSyntax.Formula)
    (groups : List (List (Original Value))) (results : List (Settlement Value))
    (success : settleAll parents groups = .ok results) :
    results.flatMap settlementDistribution = groups.flatMap (groupDistribution (countedTable parents)) := by
  induction groups generalizing results with
  | nil =>
      have empty : results = [] := by simpa [settleAll] using success.symm
      simp [empty]
  | cons first rest ih =>
      cases current : settleOne parents first with
      | error error => simp [settleAll, current] at success
      | ok decision =>
          cases later : settleAll parents rest with
          | error error => simp [settleAll, current, later] at success
          | ok remaining =>
              have same : results = decision.toList ++ remaining := by simpa [settleAll, current, later] using success.symm
              rw [same, List.flatMap_append, settleOne_stream parents first decision current, ih remaining later]
              rfl

/-- Successful traversal proves that every original group query returned successfully. -/
theorem settleAll_queries (parents : Signature → List FullSyntax.Formula)
    (groups : List (List (Original Value))) (results : List (Settlement Value))
    (success : settleAll parents groups = .ok results) :
    ∀ group ∈ groups, ∃ record, settleOne parents group = .ok record := by
  induction groups generalizing results with
  | nil => simp
  | cons first rest ih =>
      cases current : settleOne parents first with
      | error error => simp [settleAll, current] at success
      | ok decision =>
          cases later : settleAll parents rest with
          | error error => simp [settleAll, current, later] at success
          | ok remaining =>
              intro group member
              rcases List.mem_cons.mp member with rfl | member
              · exact ⟨decision, current⟩
              · exact ih remaining later group member

/-- For a nonempty group, successful settlement certifies the actual parent counter result. -/
theorem settleOne_counter (parents : Signature → List FullSyntax.Formula)
    (first : Original Value) (rest : List (Original Value)) (record : Option (Settlement Value))
    (success : settleOne parents (first :: rest) = .ok record) :
    LatticeAPI.points (names (signature first).width)
      (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula [openKey (signature first)]
        (parents (signature first)))) = .ok (countedTable parents (signature first)) := by
  cases query : LatticeAPI.points (names (signature first).width)
    (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula [openKey (signature first)]
      (parents (signature first)))) with
  | error error => simp [settleOne, query] at success
  | ok points => simp [countedTable, query]

/-- Partition preservation and successful settlement derive every parent table used by the source. -/
theorem settled_parent_tables (before : Signature → Signature → Bool) (originals : List (Original Value))
    (parents : Signature → List FullSyntax.Formula) (results : List (Settlement Value))
    (success : settleAll parents (groups before originals) = .ok results) :
    ∀ original ∈ originals,
      LatticeAPI.points (names (signature original).width)
        (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula
          [openKey (signature original)] (parents (signature original)))) = .ok (countedTable parents (signature original)) := by
  intro original member
  have regrouped := (groups_perm before originals).mem_iff.mpr member
  obtain ⟨group, present, included⟩ := List.mem_flatten.mp regrouped
  obtain ⟨first, rest, rfl, homogeneous⟩ := groups_homogeneous before originals group present
  obtain ⟨record, computed⟩ := settleAll_queries parents _ results success _ present
  rw [homogeneous original included]
  exact settleOne_counter parents first rest record computed

/-- The actual successful finite settlement driver preserves the conditioned mass of every original occurrence. -/
theorem settled_conditioned (before : Signature → Signature → Bool) (originals : List (Original Value))
    (parents : Signature → List FullSyntax.Formula) (children : Signature → LatticeAPI.Points)
    (childBuilt : ∀ original ∈ originals,
      LatticeAPI.points (names (signature original).width) (FullSyntax.lowerFormula (signature original).formula) =
        .ok (children (signature original)))
    (stored : ∀ original ∈ originals, (signature original).points = some (children (signature original)).count.toNat)
    (positive : ∀ original ∈ originals, 0 < original.mass)
    (results : List (Settlement Value)) (success : settleAll parents (groups before originals) = .ok results)
    (event : Nat × List Int → Bool) :
    Probability.eventMass event (Probability.normalize (results.flatMap settlementDistribution)) =
      Probability.eventMass event (Probability.normalize
        (originals.flatMap (restrictedContribution parents children))) := by
  rw [settleAll_stream parents _ results success]
  exact heterogeneous_conditioned before originals parents children (countedTable parents)
    childBuilt stored (settled_parent_tables before originals parents results success) positive event

/-- A retained record contains its exact input group and the counter for that group's parent formula. -/
theorem settleOne_fields (parents : Signature → List FullSyntax.Formula) (group : List (Original Value))
    (record : Settlement Value) (success : settleOne parents group = .ok (some record)) :
    record.originals = group ∧ record.key = groupKey group ∧ group ≠ [] ∧
      LatticeAPI.points (names record.key.width)
        (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula [openKey record.key]
          (parents record.key))) = .ok record.points := by
  cases group with
  | nil => simp [settleOne] at success
  | cons first rest =>
      cases query : LatticeAPI.points (names (signature first).width)
        (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula [openKey (signature first)]
          (parents (signature first)))) with
      | error error => simp [settleOne, query] at success
      | ok points =>
          by_cases zero : points.count = 0
          · simp [settleOne, query, zero] at success
          · have same : record = ⟨signature first, first :: rest, points,
                RecipeCompile.retainedShare points.count.toNat [ParentIntegerSettlement.childInfo (openKey (signature first))]⟩ := by
              simpa [settleOne, query, zero] using success.symm
            subst record
            simp [groupKey, query]

/-- Every retained current driver record has exact combined ranks in all three source views. -/
theorem settled_ranks_exact (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (before : Signature → Signature → Bool) (originals : List (Original Value))
    (parents : Signature → List FullSyntax.Formula) (results : List (Settlement Value))
    (success : settleAll parents (groups before originals) = .ok results)
    (record : Settlement Value) (present : record ∈ results)
    (view : View) (wanted : List (Term (Label IntegerLabelCodec.Symbol))) (rank : Nat) :
    rank ∈ pointCandidates IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
      record.originals record.points view wanted ↔
      ∃ originalRank : Fin record.originals.length, ∃ pointRank : Fin (LatticeSelect.pointCount record.points.levels),
        rank = Probability.pairRank (LatticeSelect.pointCount record.points.levels) originalRank.val pointRank.val ∧
        decodeView IntegerLabelCodec.integerSymbol specialize record.points view (selected record.originals originalRank) pointRank = wanted := by
  obtain ⟨group, groupPresent, settled⟩ := settleAll_sound parents _ results success record present
  have fields := settleOne_fields parents group record settled
  obtain ⟨first, rest, shape, homogeneous⟩ := groups_homogeneous before originals group groupPresent
  have key : record.key = signature first := by rw [fields.2.1, shape]; rfl
  have sameKey : ∀ original ∈ record.originals, signature original = record.key := by
    intro original member
    rw [fields.1] at member
    exact (homogeneous original member).trans key.symm
  exact group_ranks_exact IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
    IntegerLabelCodec.leafValue_integer record.originals record.key sameKey
    (ParentIntegerSettlement.restrictedFormula [openKey record.key] (parents record.key)) record.points fields.2.2.2 view wanted rank

/-- The source cardinality field equals the complete emitted closed member stream. -/
theorem settled_cardinality (parents : Signature → List FullSyntax.Formula)
    (groups : List (List (Original Value))) (results : List (Settlement Value))
    (success : settleAll parents groups = .ok results) :
    (results.flatMap settlementDistribution).length =
      (results.map (fun record => record.originals.length * record.points.count.toNat)).sum := by
  rw [List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro record present
  obtain ⟨group, _, kept⟩ := settleAll_sound parents groups results success record present
  have fields := settleOne_fields parents group record kept
  exact settled_count record.originals record.kept record.points record.key _ fields.2.2.2

/-- Group cardinalities count original occurrences, not distinct recipes or decoded values. -/
theorem group_cardinality_sum (before : Signature → Signature → Bool) (originals : List (Original Value))
    (counts : Signature → Nat) :
    ((groups before originals).map (fun group => group.length * counts (groupKey group))).sum =
      (originals.map (fun original => counts (signature original))).sum := by
  have localCount (group : List (Original Value)) (present : group ∈ groups before originals) :
      group.length * counts (groupKey group) = (group.map (fun original => counts (signature original))).sum := by
    obtain ⟨first, rest, rfl, homogeneous⟩ := groups_homogeneous before originals group present
    have mapped : (first :: rest).map (fun original => counts (signature original)) =
        (first :: rest).map (fun _ => counts (signature first)) := by
      apply List.map_congr_left
      intro original member
      rw [homogeneous original member]
    rw [mapped]
    have constantSum (items : List (Original Value)) (count : Nat) :
        (items.map (fun _ => count)).sum = items.length * count := by
      induction items with
      | nil => simp
      | cons first rest ih => simp [ih, Nat.add_mul, Nat.add_comm]
    rw [constantSum]
    rfl
  have combined (blocks : List (List (Original Value))) :
      (blocks.map (fun group => (group.map (fun original => counts (signature original))).sum)).sum =
        (blocks.flatten.map (fun original => counts (signature original))).sum := by
    induction blocks with
    | nil => rfl
    | cons first rest ih => simp [List.map_append, List.sum_append, ih]
  have sameMaps : (groups before originals).map (fun group => group.length * counts (groupKey group)) =
      (groups before originals).map (fun group => (group.map (fun original => counts (signature original))).sum) :=
    List.map_congr_left localCount
  rw [sameMaps, combined]
  exact ((groups_perm before originals).map (fun original => counts (signature original))).sum_nat

/-- The cardinalities view of one repeated open key records its full original count. -/
def choiceBucket (group : List (Original Value)) : OpenChoiceRouting.Bucket :=
  ⟨openKey (groupKey group), group.length⟩

/-- All finite group point records are inherited from an original with the same complete key. -/
theorem grouped_point_records (before : Signature → Signature → Bool) (originals : List (Original Value))
    (counts : Signature → Nat) (stored : ∀ original ∈ originals, (signature original).points = some (counts (signature original))) :
    ∀ group ∈ groups before originals, (choiceBucket group).key.points = some (counts (groupKey group)) := by
  intro group present
  obtain ⟨first, rest, rfl, _⟩ := groups_homogeneous before originals group present
  have member : first ∈ originals := (groups_perm before originals).mem_iff.mp
    (List.mem_flatten.mpr ⟨first :: rest, present, by simp⟩)
  exact stored first member

/-- Uniform's actual members calculation derives the complete count across heterogeneous repeated keys. -/
theorem choice_members (recount : Key → Except (OpenChoiceRouting.Error Cause) Nat)
    (before : Signature → Signature → Bool) (originals : List (Original Value))
    (counts : Signature → Nat) (stored : ∀ original ∈ originals, (signature original).points = some (counts (signature original))) :
    OpenChoiceRouting.members recount
      ⟨false, .ok ((groups before originals).map choiceBucket)⟩ =
      .ok (((originals.map (fun original => counts (signature original))).sum : Nat) : Int) := by
  have records := grouped_point_records before originals counts stored
  have countLoop (blocks : List (List (Original Value)))
      (known : ∀ group ∈ blocks, (choiceBucket group).key.points = some (counts (groupKey group))) :
      OpenChoiceRouting.sumPoints recount (blocks.map choiceBucket) =
        .ok ((blocks.map (fun group => group.length * counts (groupKey group))).sum) := by
    induction blocks with
    | nil => rfl
    | cons first rest ih =>
        simp only [List.map_cons, OpenChoiceRouting.sumPoints, OpenChoiceRouting.pointsOf,
          known first (by simp), ih (fun group member => known group (by simp [member])),
          LatticeLinear.except_bind_ok, List.sum_cons]
        rfl
  simp only [OpenChoiceRouting.members, OpenChoiceRouting.cardinalities, Bool.false_eq_true,
    ↓reduceIte, countLoop _ records, Except.map, group_cardinality_sum before originals counts]
  rfl

/-- Actual child counters and their primitive records derive the joined key's stored point count. -/
theorem original_record_from_parts (original : Original Value) (parts : Key → LatticeAPI.Points)
    (partBuilt : ∀ key ∈ original.keys,
      LatticeAPI.points (names key.width) (FullSyntax.lowerFormula key.formula) = .ok (parts key))
    (partRecords : ∀ key ∈ original.keys, key.points = some (parts key).count.toNat)
    (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (signature original).width)
      (FullSyntax.lowerFormula (signature original).formula) = .ok points) :
    (signature original).points = some points.count.toNat := by
  let domains := fun key => pointDomain (parts key)
  have parentBuilt : LatticeAPI.points (names (OpenIntegerKeys.join original.keys).width)
      (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula original.keys [])) = .ok points := by
    simpa [ParentIntegerSettlement.restrictedFormula, signature, OpenIntegerKeys.join] using built
  have cardinality := ParentIntegerSettlement.counted_parent_cardinality original.keys [] parts partBuilt points parentBuilt
  have allows : ParentIntegerSettlement.parentAllows [] = (fun _ => true) := by
    funext tuple
    simp [ParentIntegerSettlement.parentAllows]
  have unchanged : (joinedTuples domains original.keys).filter (ParentIntegerSettlement.parentAllows []) =
      joinedTuples domains original.keys := List.filter_eq_self.mpr (fun _ _ => by rw [allows])
  have count : points.count.toNat = (joinedTuples domains original.keys).length := by
    change points.count.toNat = ((joinedTuples domains original.keys).filter (ParentIntegerSettlement.parentAllows [])).length at cardinality
    rw [unchanged] at cardinality
    exact cardinality
  have records : ∀ key ∈ original.keys, key.points = some (domains key).length := by
    intro key member
    rw [show (domains key).length = (parts key).count.toNat from pointDomain_count _ _ _ (partBuilt key member)]
    exact partRecords key member
  change productPoints original.keys = some points.count.toNat
  rw [productPoints_exact domains original.keys records, count]

/-- The full finite mass bridge derives joined count records from the actual component point tables. -/
theorem settled_conditioned_from_parts (before : Signature → Signature → Bool) (originals : List (Original Value))
    (parents : Signature → List FullSyntax.Formula) (children : Signature → LatticeAPI.Points)
    (parts : Original Value → Key → LatticeAPI.Points)
    (partBuilt : ∀ original ∈ originals, ∀ key ∈ original.keys,
      LatticeAPI.points (names key.width) (FullSyntax.lowerFormula key.formula) = .ok (parts original key))
    (partRecords : ∀ original ∈ originals, ∀ key ∈ original.keys,
      key.points = some (parts original key).count.toNat)
    (childBuilt : ∀ original ∈ originals,
      LatticeAPI.points (names (signature original).width) (FullSyntax.lowerFormula (signature original).formula) =
        .ok (children (signature original)))
    (positive : ∀ original ∈ originals, 0 < original.mass)
    (results : List (Settlement Value)) (success : settleAll parents (groups before originals) = .ok results)
    (event : Nat × List Int → Bool) :
    Probability.eventMass event (Probability.normalize (results.flatMap settlementDistribution)) =
      Probability.eventMass event (Probability.normalize
        (originals.flatMap (restrictedContribution parents children))) :=
  settled_conditioned before originals parents children childBuilt
    (fun original member => original_record_from_parts original (parts original)
      (partBuilt original member) (partRecords original member) (children (signature original)) (childBuilt original member))
    positive results success event

/-- labelOutcomeTerms keeps the parent root and asks the inner source for its labelled children. -/
def parentCandidates (acceptsLabel : Symbol → Bool) (group : List (Original Value))
    (_view : View) (wanted : List (Term (Label Symbol))) : List Nat :=
  match wanted with
  | [.node (.user found) children] => if acceptsLabel found then candidates group .labelled children else []
  | _ => []

/-- The actual parent label removes private choice roots without changing original ranks. -/
def parentSelected (symbol : Symbol) (group : List (Original Value)) (rank : Fin group.length) : Term (Label Symbol) :=
  SupportTerms.labelTerm symbol (selected group rank)

/-- The parent label callback discovers every retained original after source specialization. -/
theorem parent_candidates_complete (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (symbol : Symbol) (acceptsLabel : Symbol → Bool)
    (compatible : ∀ point, acceptsLabel (exactLabel point symbol) = true)
    (group : List (Original Value)) (rank : Fin group.length) (point : List Int) (view : View) :
    rank.val ∈ parentCandidates acceptsLabel group view
      (project view (fill literal exactLabel point (parentSelected symbol group rank)).2) := by
  rw [parentSelected, labelled_source]
  simp only [fill, StaticCandidateRanks.project_user, parentCandidates, compatible point, ↓reduceIte]
  have same := congrArg Prod.snd (labelled_fill literal exactLabel point (selected group rank) (selected_valid group rank))
  rw [same]
  exact candidates_complete literal exactLabel group rank point .labelled

/-- Parent labelling derives the exact same coordinate count as the actual merged group. -/
theorem parent_selected_width (literal : Int → Symbol) (symbol : Symbol)
    (group : List (Original Value)) (key : Signature)
    (sameKey : ∀ original ∈ group, signature original = key) (rank : Fin group.length) :
    count (parentSelected symbol group rank) = key.width := by
  rw [parentSelected, label_count literal symbol _ (selected_valid group rank), selected_width group key sameKey rank]

/-- Execute pointsStatic after labelStaticMatching for the finite parent branch. -/
def parentPointCandidates [DecidableEq Symbol] (literal : Int → Symbol)
    (exactLabel : List Int → Symbol → Symbol) (read : Symbol → Option Int)
    (symbol : Symbol) (acceptsLabel : Symbol → Bool) (group : List (Original Value)) (points : LatticeAPI.Points)
    (view : View) (wanted : List (Term (Label Symbol))) : List Nat :=
  (parentCandidates acceptsLabel group view wanted).flatMap fun originalRank =>
    if bound : originalRank < group.length then
      match rankView literal exactLabel read points view (parentSelected symbol group ⟨originalRank, bound⟩) wanted with
      | none => []
      | some pointRank => [Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank pointRank]
    else []

/-- Parent closure retains every original and point rank, even when labelling identifies visible terms. -/
theorem parent_points_complete [DecidableEq Symbol] (literal : Int → Symbol)
    (exactLabel : List Int → Symbol → Symbol) (read : Symbol → Option Int)
    (literalRead : ∀ value, read (literal value) = some value)
    (symbol : Symbol) (acceptsLabel : Symbol → Bool)
    (compatible : ∀ point, acceptsLabel (exactLabel point symbol) = true)
    (group : List (Original Value)) (key : Signature)
    (sameKey : ∀ original ∈ group, signature original = key)
    (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names key.width) (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (originalRank : Fin group.length) (pointRank : Fin (LatticeSelect.pointCount points.levels)) :
    Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank.val pointRank.val ∈
      parentPointCandidates literal exactLabel read symbol acceptsLabel group points view
        (decodeView literal exactLabel points view (parentSelected symbol group originalRank) pointRank) := by
  apply List.mem_flatMap.mpr
  refine ⟨originalRank.val, parent_candidates_complete literal exactLabel symbol acceptsLabel compatible group originalRank _ view, ?_⟩
  simp only [originalRank.isLt, ↓reduceDIte]
  rw [rank_decode literal exactLabel read literalRead (names key.width) formula points built view
    (parentSelected symbol group originalRank) (label_valid symbol _ (selected_valid group originalRank))
    (by simpa [names] using parent_selected_width literal symbol group key sameKey originalRank) pointRank]
  simp

/-- The final parent view check accepts only the filled term at its reported mixed-radix rank. -/
theorem parent_points_sound [DecidableEq Symbol] (literal : Int → Symbol)
    (exactLabel : List Int → Symbol → Symbol) (read : Symbol → Option Int)
    (symbol : Symbol) (acceptsLabel : Symbol → Bool) (group : List (Original Value))
    (declared : List FullSyntax.Name) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points declared (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (wanted : List (Term (Label Symbol))) (rank : Nat)
    (accepted : rank ∈ parentPointCandidates literal exactLabel read symbol acceptsLabel group points view wanted) :
    ∃ originalRank : Fin group.length, ∃ pointRank : Fin (LatticeSelect.pointCount points.levels),
      rank = Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank.val pointRank.val ∧
      decodeView literal exactLabel points view (parentSelected symbol group originalRank) pointRank = wanted := by
  obtain ⟨originalRank, _, accepted⟩ := List.mem_flatMap.mp accepted
  by_cases bound : originalRank < group.length
  · simp only [bound, ↓reduceDIte] at accepted
    cases ranked : rankView literal exactLabel read points view (parentSelected symbol group ⟨originalRank, bound⟩) wanted with
    | none => simp [ranked] at accepted
    | some pointRank =>
        have same : rank = Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank pointRank := by
          simpa [ranked] using accepted
        obtain ⟨validRank, value, decoded⟩ := rankView_sound literal exactLabel read declared formula points built
          view (parentSelected symbol group ⟨originalRank, bound⟩) wanted pointRank ranked
        exact ⟨⟨originalRank, bound⟩, validRank, by simpa [value] using same, decoded⟩
  · simp [bound] at accepted

/-- Actual source exactLabel successes discharge the parent matcher condition. -/
theorem parent_integer_match (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (symbol : IntegerLabelCodec.Symbol)
    (computed : ∀ point, IntegerLabelCodec.exactLabel point symbol = .ok (specialize point symbol)) :
    ∀ point, IntegerLabelCodec.fills symbol (specialize point symbol) = true :=
  fun point => IntegerLabelCodec.exactLabel_matches point symbol _ (computed point)

/-- Actual integer parent labels and successful settlement give all and only combined replay ranks. -/
theorem settled_parent_ranks_exact
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (symbol : IntegerLabelCodec.Symbol)
    (specialized : ∀ point, IntegerLabelCodec.exactLabel point symbol = .ok (specialize point symbol))
    (before : Signature → Signature → Bool) (originals : List (Original Value))
    (parents : Signature → List FullSyntax.Formula) (results : List (Settlement Value))
    (success : settleAll parents (groups before originals) = .ok results)
    (record : Settlement Value) (present : record ∈ results)
    (view : View) (wanted : List (Term (Label IntegerLabelCodec.Symbol))) (rank : Nat) :
    rank ∈ parentPointCandidates IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue symbol
      (IntegerLabelCodec.fills symbol) record.originals record.points view wanted ↔
      ∃ originalRank : Fin record.originals.length, ∃ pointRank : Fin (LatticeSelect.pointCount record.points.levels),
        rank = Probability.pairRank (LatticeSelect.pointCount record.points.levels) originalRank.val pointRank.val ∧
        decodeView IntegerLabelCodec.integerSymbol specialize record.points view
          (parentSelected symbol record.originals originalRank) pointRank = wanted := by
  obtain ⟨group, groupPresent, settled⟩ := settleAll_sound parents _ results success record present
  have fields := settleOne_fields parents group record settled
  obtain ⟨first, rest, shape, homogeneous⟩ := groups_homogeneous before originals group groupPresent
  have key : record.key = signature first := by rw [fields.2.1, shape]; rfl
  have sameKey : ∀ original ∈ record.originals, signature original = record.key := by
    intro original member
    rw [fields.1] at member
    exact (homogeneous original member).trans key.symm
  constructor
  · exact parent_points_sound IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue symbol
      (IntegerLabelCodec.fills symbol) record.originals _ _ record.points fields.2.2.2 view wanted rank
  · rintro ⟨originalRank, pointRank, rfl, rfl⟩
    exact parent_points_complete IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
      IntegerLabelCodec.leafValue_integer symbol (IntegerLabelCodec.fills symbol)
      (parent_integer_match specialize symbol specialized) record.originals record.key sameKey
      (ParentIntegerSettlement.restrictedFormula [openKey record.key] (parents record.key))
      record.points fields.2.2.2 view originalRank pointRank

/-- Every integer in the complete source product interval has a decoded parent view and its inverse rank. -/
theorem settled_parent_every_rank
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (symbol : IntegerLabelCodec.Symbol)
    (specialized : ∀ point, IntegerLabelCodec.exactLabel point symbol = .ok (specialize point symbol))
    (before : Signature → Signature → Bool) (originals : List (Original Value))
    (parents : Signature → List FullSyntax.Formula) (results : List (Settlement Value))
    (success : settleAll parents (groups before originals) = .ok results)
    (record : Settlement Value) (present : record ∈ results) (view : View) (rank : Nat)
    (bound : rank < record.originals.length * LatticeSelect.pointCount record.points.levels) :
    ∃ wanted, rank ∈ parentPointCandidates IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue symbol
      (IntegerLabelCodec.fills symbol) record.originals record.points view wanted := by
  let count := LatticeSelect.pointCount record.points.levels
  have bounds := Probability.split_lt bound
  let originalRank : Fin record.originals.length := ⟨(Probability.splitRank count rank).1, bounds.1⟩
  let pointRank : Fin count := ⟨(Probability.splitRank count rank).2, bounds.2⟩
  refine ⟨decodeView IntegerLabelCodec.integerSymbol specialize record.points view
    (parentSelected symbol record.originals originalRank) pointRank, ?_⟩
  rw [settled_parent_ranks_exact specialize symbol specialized before originals parents results success record present view _ rank]
  exact ⟨originalRank, pointRank, (Probability.pair_split count rank).symm, rfl⟩

end MicroCFTA.OpenGroupComposition
