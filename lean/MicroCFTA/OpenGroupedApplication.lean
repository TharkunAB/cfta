import MicroCFTA.OpenGroupComposition
import MicroCFTA.CompositeCheckedRanks

/-!
# Finite multi-group applicative compilation

compileOpenSpine pairs bucket maps in left-major order. Every bucket has the
same number of key positions as its family's spine arity. Widths can differ.
The result key concatenation is therefore injective on distinct bucket pairs.
-/
namespace MicroCFTA.OpenGroupedApplication
open Language GeneratorCombinators IntegerTermViews OpenIntegerKeys OpenIntegerSource OpenGroupComposition

/-- The actual bare compiler derives its complete list of coordinate widths. -/
theorem compileKeys_positions (recipe : Recipe Value) (keys : List Key)
    (built : compileKeys recipe = .ok (some keys)) :
    keys.map Key.width = OpenIntegerReaders.counts (reader recipe) := by
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
            simp [integerGroup_width domain key grouped, reader, OpenIntegerReaders.counts]
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
                simp [ihf functionKeys left, iha argumentKeys right, reader, OpenIntegerReaders.counts]

/-- A repeated-key source stores the homogeneous group produced by the actual partition. -/
structure Repeated (Value : Type) where
  key : Signature
  originals : List (Original Value)
  sameKey : ∀ original ∈ originals, signature original = key

/-- The finite static source constructors produced by bare compilation, regrouping, and bucket pairing. -/
inductive Source : Type → Type 1 where
  | generated (original : Original Value) : Source Value
  | repeated (group : Repeated Value) : Source Value
  | app (component : Nat) (functions : Source (α → β)) (arguments : Source α) : Source β

/-- Integer leaf observations share the same primitive root. Other observed groups retain their source identity. -/
def primitiveKey (key : Key) : Signature := ⟨0, key.width, key.formula, key.points⟩

/-- Source keys are full position lists. A grouped fallback contributes one key position. -/
def keys : Source Value → List Signature
  | .generated original => original.keys.map primitiveKey
  | .repeated group => [group.key]
  | .app _ functions arguments => keys functions ++ keys arguments

/-- The independent source arity follows bare syntax and treats an observed group as one spine operand. -/
def arity : Source Value → Nat
  | .generated original => (OpenIntegerReaders.counts (reader original.recipe)).length
  | .repeated _ => 1
  | .app _ functions arguments => arity functions + arity arguments

/-- Each source constructor derives exactly one key position per spine operand. -/
theorem keys_arity (source : Source Value) : (keys source).length = arity source := by
  induction source with
  | generated original =>
      have counts := congrArg List.length (compileKeys_positions original.recipe original.keys original.compiled)
      simpa [keys, arity] using counts
  | repeated group => rfl
  | app component functions arguments left right => simp [keys, arity, left, right]

/-- The coordinate width is the sum of the counts in the source key positions. -/
def width (source : Source Value) : Nat := ((keys source).map Signature.width).sum

/-- The concrete key formula and stored count are composed by joinOpenKeys. -/
def joinedKey (source : Source Value) : Key := OpenIntegerKeys.join ((keys source).map openKey)

/-- Source applyReader's key-position split is exactly the function-side coordinate width. -/
theorem reader_split (component : Nat) (functions : Source (α → β)) (arguments : Source α) :
    (((keys (.app component functions arguments)).take (arity functions)).map Signature.width).sum = width functions := by
  rw [← keys_arity functions]
  simp [keys, width]

/-- Pairing adds coordinate widths; it does not confuse them with key-position arity. -/
theorem width_app (component : Nat) (functions : Source (α → β)) (arguments : Source α) :
    width (.app component functions arguments) = width functions + width arguments := by
  simp [width, keys, List.map_append, List.sum_append]

/-- Count original outcomes before any integer point is selected. -/
def cardinality : Source Value → Nat
  | .generated _ => 1
  | .repeated group => group.originals.length
  | .app _ functions arguments => cardinality functions * cardinality arguments

/-- Independent source selection uses the concrete pairBucket JoinN constructor. -/
inductive Selected : {Value : Type} → Source Value → Nat → Term (Label Symbol) → Prop where
  | generated (original : Original Value) : Selected (.generated original) 0 (CompiledIntegerSpine.template original.recipe)
  | repeated (group : Repeated Value) (rank : Fin group.originals.length) :
      Selected (.repeated group) rank.val (OpenGroupComposition.selected group.originals rank)
  | app {functions : Source (α → β)} {arguments : Source α} {leftRank rightRank : Nat}
      {left right : Term (Label Symbol)} (component : Nat)
      (leftSelected : Selected functions leftRank left) (rightSelected : Selected arguments rightRank right) :
      Selected (.app component functions arguments) (Probability.pairRank (cardinality arguments) leftRank rightRank)
        (SupportJoin.joinTerm component (.node .pure []) [left, right])

/-- Source selection cannot construct an out-of-range original rank. -/
theorem selected_bound {source : Source Value} {rank : Nat} {term : Term (Label Symbol)}
    (selected : Selected source rank term) : rank < cardinality source := by
  induction selected with
  | generated original => simp [cardinality]
  | repeated group rank => exact rank.isLt
  | app component left right leftBound rightBound => exact Probability.pairRank_lt leftBound rightBound

/-- Every generated bucket-pair term satisfies the fill traversal's shape requirements. -/
theorem selected_valid {source : Source Value} {rank : Nat} {term : Term (Label Symbol)}
    (selected : Selected source rank term) : Valid term := by
  induction selected with
  | generated original => exact CompiledIntegerSpine.template_valid original.recipe
  | repeated group rank => exact OpenGroupComposition.selected_valid group.originals rank
  | app component left right leftValid rightValid =>
      simp [SupportJoin.joinTerm, SupportJoin.keys, SupportJoin.arguments, Valid, leftValid, rightValid]

/-- Private pairBucket wrappers preserve the sum of both child placeholder counts. -/
theorem pair_count (component : Nat) (left right : Term (Label Symbol)) :
    count (SupportJoin.joinTerm component (.node .pure []) [left, right]) = count left + count right := by
  simp [SupportJoin.joinTerm, SupportJoin.keys, SupportJoin.arguments, count, adapt, adaptLabel,
    adaptForest, RecipeCompile.holes, RecipeCompile.forestHoles]

/-- Selected multi-group product terms have exactly their own source key width. -/
theorem selected_width {source : Source Value} {rank : Nat} {term : Term (Label Symbol)}
    (selected : Selected source rank term) : count term = width source := by
  induction selected with
  | generated original =>
      simpa [width, keys, primitiveKey, signature, OpenIntegerKeys.join, List.map_map, Function.comp_def]
        using original_width original
  | repeated group rank =>
      simpa [width, keys] using OpenGroupComposition.selected_width
        group.originals group.key group.sameKey rank
  | app component left right leftWidth rightWidth => rw [pair_count, leftWidth, rightWidth, width_app]

/-- Every original product position is selectable, without materializing a product list. -/
theorem selected_exists (source : Source Value) (rank : Nat) (bound : rank < cardinality source) :
    ∃ term : Term (Label Symbol), Selected source rank term := by
  induction source generalizing rank with
  | generated original =>
      have zero : rank = 0 := by simp only [cardinality] at bound; omega
      subst rank
      exact ⟨_, .generated original⟩
  | repeated group => exact ⟨_, .repeated group ⟨rank, bound⟩⟩
  | app component functions arguments left right =>
      have bounds := Probability.split_lt bound
      obtain ⟨leftTerm, leftSelected⟩ := left _ bounds.1
      obtain ⟨rightTerm, rightSelected⟩ := right _ bounds.2
      have selected := Selected.app component leftSelected rightSelected
      rw [Probability.pair_split] at selected
      exact ⟨_, selected⟩

/-- The actual finite selector follows product radices and retains the assigned component index. -/
def select : Source Value → Nat → Option (Term (Label Symbol))
  | .generated original, rank => if rank = 0 then some (CompiledIntegerSpine.template original.recipe) else none
  | .repeated group, rank => OpenGroupComposition.select group.originals rank
  | .app component functions arguments, rank =>
      if rank < cardinality functions * cardinality arguments then do
        let left ← select functions (rank / cardinality arguments)
        let right ← select arguments (rank % cardinality arguments)
        pure (SupportJoin.joinTerm component (.node .pure []) [left, right])
      else none

/-- Every independently constructed original selection is returned by the executable decoder. -/
theorem selected_select {source : Source Value} {rank : Nat} {term : Term (Label Symbol)}
    (selected : Selected source rank term) : select source rank = some term := by
  induction selected with
  | generated original => simp [select]
  | repeated group rank => exact OpenGroupComposition.select_selected group.originals rank
  | @app _ _ _ functions arguments leftRank rightRank leftTerm rightTerm component left right ihl ihr =>
      have bound := Probability.pairRank_lt (selected_bound left) (selected_bound right)
      have split := Probability.split_pair (left := leftRank) (selected_bound right)
      simp only [Probability.splitRank, Prod.mk.injEq] at split
      simp [select, bound, split.1, split.2, ihl, ihr]

/-- The executable decoder rejects every rank outside the counted source interval. -/
theorem select_bound (source : Source Value) (rank : Nat) (term : Term (Label Symbol))
    (found : select source rank = some term) : rank < cardinality source := by
  cases source with
  | generated original =>
      by_cases zero : rank = 0
      · simp [cardinality, zero]
      · simp [select, zero] at found
  | repeated group =>
      by_cases bound : rank < group.originals.length
      · exact bound
      · simp [select, OpenGroupComposition.select, bound] at found
  | app component functions arguments =>
      by_cases bound : rank < cardinality functions * cardinality arguments
      · exact bound
      · simp [select, bound] at found

/-- The executable selected terms are exactly the concrete source derivations. -/
theorem select_exact (source : Source Value) (rank : Nat) (term : Term (Label Symbol)) :
    select source rank = some term ↔ Selected source rank term := by
  constructor
  · intro found
    obtain ⟨actual, selected⟩ := selected_exists source rank (select_bound source rank term found)
    have same := Option.some.inj ((selected_select selected).symm.trans found)
    exact same ▸ selected
  · exact selected_select

/-- The source value callback partitions coordinates by key positions, then applies the selected function. -/
def evaluate : Source Value → Nat → List Int → Option Value
  | .generated original, rank, point =>
      if rank = 0 then OpenIntegerReaders.evaluate (reader original.recipe) point else none
  | .repeated group, rank, point =>
      group.originals[rank]?.bind (fun original => OpenIntegerReaders.evaluate (reader original.recipe) point)
  | .app _ functions arguments, rank, point =>
      if rank < cardinality functions * cardinality arguments then do
        let function ← evaluate functions (rank / cardinality arguments) (point.take (width functions))
        let argument ← evaluate arguments (rank % cardinality arguments) (point.drop (width functions))
        pure (function argument)
      else none

/-- Every admitted coordinate tuple gives a value for every original multi-group product rank. -/
theorem evaluate_total {source : Source Value} {rank : Nat} {term : Term (Label Symbol)}
    (selected : Selected source rank term) (point : List Int) (dimension : point.length = width source) :
    ∃ value, evaluate source rank point = some value := by
  induction selected generalizing point with
  | generated original =>
      have widthSame : width (.generated original) = OpenIntegerReaders.width (reader original.recipe) := by
        simpa [width, keys, primitiveKey, List.map_map, Function.comp_def] using
          compileKeys_width original.recipe original.keys original.compiled
      simpa [evaluate] using OpenIntegerReaders.evaluate_total (reader original.recipe) point (dimension.trans widthSame)
  | repeated group rank =>
      let original := group.originals[rank.val]
      have member : original ∈ group.originals := List.getElem_mem rank.isLt
      have keySame := congrArg Signature.width (group.sameKey original member)
      have widthSame : width (.repeated group) = OpenIntegerReaders.width (reader original.recipe) := by
        rw [width, keys]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        rw [← keySame]
        exact compileKeys_width original.recipe original.keys original.compiled
      obtain ⟨value, found⟩ := OpenIntegerReaders.evaluate_total (reader original.recipe) point (dimension.trans widthSame)
      exact ⟨value, by simpa [evaluate, List.getElem?_eq_getElem rank.isLt] using found⟩
  | @app _ _ _ functions arguments leftRank rightRank leftTerm rightTerm component left right ihl ihr =>
      have totalWidth : point.length = width functions + width arguments := by simpa [width_app] using dimension
      have front : (point.take (width functions)).length = width functions := by simp [totalWidth]
      have suffix : (point.drop (width functions)).length = width arguments := by simp [totalWidth]
      obtain ⟨function, functionRead⟩ := ihl _ front
      obtain ⟨argument, argumentRead⟩ := ihr _ suffix
      have bound := Probability.pairRank_lt (selected_bound left) (selected_bound right)
      have split := Probability.split_pair (left := leftRank) (selected_bound right)
      simp only [Probability.splitRank, Prod.mk.injEq] at split
      exact ⟨function argument, by simp [evaluate, bound, split.1, split.2, functionRead, argumentRead]⟩

/-- Filling the function member consumes precisely the front used by applyReader. -/
theorem fill_reader_split (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    {source : Source Value} {rank : Nat} {term : Term (Label Symbol)}
    (selected : Selected source rank term) (point : List Int) :
    (fill literal exactLabel point term).1 = point.drop (width source) := by
  rw [fill_remaining, selected_width selected]

/-- Source concatenation is injective when the left key-position count is fixed. -/
theorem append_injective (left right otherLeft otherRight : List Signature)
    (sameLength : left.length = otherLeft.length) (same : left ++ right = otherLeft ++ otherRight) :
    left = otherLeft ∧ right = otherRight := by
  have front := congrArg (List.take left.length) same
  have sameLeft : left = otherLeft := by simpa [sameLength] using front
  subst otherLeft
  exact ⟨rfl, List.append_cancel_left same⟩

/-- A finite source bucket keeps its complete static source and its outer mass. -/
structure Bucket (Value : Type) where
  source : Source Value
  mass : Rat

/-- The source list comprehension lists every ordered bucket pair in left-major order. -/
def pairs (left : List (Bucket (α → β))) (right : List (Bucket α)) : List (Bucket (α → β) × Bucket α) :=
  left.flatMap fun function => right.map (fun argument => (function, argument))

/-- Every input bucket pair occurs in the source comprehension. -/
theorem pairs_member (left : List (Bucket (α → β))) (right : List (Bucket α))
    (function : Bucket (α → β)) (argument : Bucket α) :
    (function, argument) ∈ pairs left right ↔ function ∈ left ∧ argument ∈ right := by
  simp [pairs, List.mem_flatMap, List.mem_map]

/-- Pair enumeration has one slot for every pair of input map entries. -/
theorem pairs_count (left : List (Bucket (α → β))) (right : List (Bucket α)) :
    (pairs left right).length = left.length * right.length := by
  have same : pairs left right = Decoder.applyValues (left.map Prod.mk) right := by
    simp [pairs, Decoder.applyValues, List.flatMap_map]
  rw [same, Decoder.length_applyValues, List.length_map]

/-- Source pairBucket multiplies outer masses and uses the actual list-position component index. -/
def component (index : Nat) (pair : Bucket (α → β) × Bucket α) : Bucket β :=
  ⟨.app index pair.1.source pair.2.source, pair.1.mass * pair.2.mass⟩

/-- relateGroupsM's all-True applicative relation keeps every pair before assigning component indexes. -/
def applyBuckets (left : List (Bucket (α → β))) (right : List (Bucket α)) : List (Bucket β) :=
  ((pairs left right).zipIdx).map (fun entry => component entry.2 entry.1)

/-- The source never loses a bucket-pair occurrence during component assignment. -/
theorem applyBuckets_count (left : List (Bucket (α → β))) (right : List (Bucket α)) :
    (applyBuckets left right).length = left.length * right.length := by simp [applyBuckets, pairs_count]

/-- Each family has one spine arity even when its buckets have different coordinate widths. -/
def FixedArity (count : Nat) (buckets : List (Bucket Value)) : Prop :=
  ∀ bucket ∈ buckets, arity bucket.source = count

/-- Pairing preserves the independent source arity invariant. -/
theorem applyBuckets_arity (left : List (Bucket (α → β))) (right : List (Bucket α))
    (leftArity rightArity : Nat) (leftFixed : FixedArity leftArity left) (rightFixed : FixedArity rightArity right) :
    FixedArity (leftArity + rightArity) (applyBuckets left right) := by
  intro bucket present
  obtain ⟨entry, member, rfl⟩ := List.mem_map.mp present
  have pairMember : entry.1 ∈ pairs left right := List.fst_mem_of_mem_zipIdx member
  obtain ⟨leftMember, rightMember⟩ := (pairs_member left right entry.1.1 entry.1.2).mp pairMember
  simp [component, arity, leftFixed _ leftMember, rightFixed _ rightMember]

/-- The exact result-key list before any metadata normalization. -/
theorem applyBuckets_keys (left : List (Bucket (α → β))) (right : List (Bucket α)) :
    (applyBuckets left right).map (fun bucket => keys bucket.source) =
      (pairs left right).map (fun pair => keys pair.1.source ++ keys pair.2.source) := by
  simp only [applyBuckets, List.map_map, component, keys, Function.comp_def]
  have projection (items : List (Bucket (α → β) × Bucket α)) (first : Nat) :
      (items.zipIdx first).map (fun entry => keys entry.1.1.source ++ keys entry.1.2.source) =
        items.map (fun pair => keys pair.1.source ++ keys pair.2.source) := by
    induction items generalizing first with
    | nil => rfl
    | cons pair rest ih => simp [List.zipIdx_cons, ih]
  exact projection (pairs left right) 0

/-- The raw pair list uses exactly the mixed-radix input-map order. -/
theorem pairs_get (left : List (Bucket (α → β))) (right : List (Bucket α))
    (function : Fin left.length) (argument : Fin right.length) :
    (pairs left right)[Probability.pairRank right.length function.val argument.val]? =
      some (left[function.val], right[argument.val]) := by
  have same : pairs left right = Decoder.applyValues (left.map Prod.mk) right := by
    simp [pairs, Decoder.applyValues, List.flatMap_map]
  rw [same, Decoder.get_applyValues]
  have bounded := Probability.pairRank_lt function.isLt argument.isLt
  have split := Probability.split_pair (left := function.val) argument.isLt
  simp only [Probability.splitRank, Prod.mk.injEq] at split
  simp [List.length_map, bounded, split.1, split.2]

/-- The source component identifier is the pair's position among all retained key pairs. -/
theorem applyBuckets_get (left : List (Bucket (α → β))) (right : List (Bucket α))
    (function : Fin left.length) (argument : Fin right.length) :
    (applyBuckets left right)[Probability.pairRank right.length function.val argument.val]? =
      some (component (Probability.pairRank right.length function.val argument.val) (left[function.val], right[argument.val])) := by
  simp [applyBuckets, List.getElem?_map, List.getElem?_zipIdx, pairs_get]

/-- Fixed source arity makes distinct input map keys remain distinct under concatenation. -/
theorem applyBuckets_keys_unique (left : List (Bucket (α → β))) (right : List (Bucket α))
    (leftArity : Nat) (fixed : FixedArity leftArity left)
    (leftUnique : (left.map (fun bucket => keys bucket.source)).Nodup)
    (rightUnique : (right.map (fun bucket => keys bucket.source)).Nodup) :
    ((applyBuckets left right).map (fun bucket => keys bucket.source)).Nodup := by
  rw [applyBuckets_keys]
  simp only [pairs, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.pairwise_flatMap.mpr
  constructor
  · intro function _
    apply List.pairwise_map.mpr
    have rightDifferent := List.pairwise_map.mp rightUnique
    exact rightDifferent.imp (fun different same => different (List.append_cancel_left same))
  · have leftDifferent := List.pairwise_map.mp leftUnique
    apply leftDifferent.imp_of_mem
    intro first second firstMember secondMember different leftKey leftMember rightKey rightMember same
    obtain ⟨firstArgument, _, rfl⟩ := List.mem_map.mp leftMember
    obtain ⟨secondArgument, _, rfl⟩ := List.mem_map.mp rightMember
    have length : (keys first.source).length = (keys second.source).length := by
      rw [keys_arity, keys_arity, fixed first firstMember, fixed second secondMember]
    exact different (append_injective _ _ _ _ length same).1

/-- The unsorted first-occurrence partition emits no repeated group identity. -/
theorem partition_keys_unique (originals : List (Original Value)) :
    ((Sized.groups signature originals).map groupKey).Nodup := by
  induction originals using Sized.groups.induct signature with
  | case1 => simp [Sized.groups]
  | case2 first rest ih =>
      rw [List.unattach_filter (g := fun other => decide (signature other ≠ signature first))
        (hf := fun _ _ => rfl), List.unattach_attach] at ih
      rw [Sized.groups]
      simp only [List.map_cons, List.nodup_cons, groupKey]
      refine ⟨?_, ih⟩
      intro present
      obtain ⟨group, member, same⟩ := List.mem_map.mp present
      obtain ⟨head, tail, rfl, _⟩ := Sized.groups_constant signature _ group member
      have originalMember : head ∈ rest.filter (fun other => decide (signature other ≠ signature first)) :=
        (Sized.groups_perm signature (rest.filter (fun other => decide (signature other ≠ signature first)))).mem_iff.mp
        (List.mem_flatten.mpr ⟨head :: tail, member, by simp⟩)
      have different := of_decide_eq_true (List.mem_filter.mp originalMember).2
      exact different same

/-- Sorting the actual key groups retains their unique map-key representation. -/
theorem grouped_keys_unique (before : Signature → Signature → Bool) (originals : List (Original Value)) :
    ((OpenGroupComposition.groups before originals).map groupKey).Nodup := by
  have ordered := (List.mergeSort_perm (Sized.groups signature originals) (groupBefore before signature)).map groupKey
  exact ordered.nodup_iff.mpr (partition_keys_unique originals)

/-- A partition member becomes one actual grouped fallback source, with its complete key certificate. -/
def repeatedBucket (before : Signature → Signature → Bool) (originals : List (Original Value))
    (group : { group // group ∈ OpenGroupComposition.groups before originals }) : Bucket Value :=
  let homogeneous : ∀ original ∈ group.val, signature original = groupKey group.val := by
    obtain ⟨first, rest, shape, same⟩ := groups_homogeneous before originals group.val group.property
    rw [shape]
    simpa [shape, groupKey] using same
  ⟨.repeated ⟨groupKey group.val, group.val, homogeneous⟩, Probability.total (originalMasses group.val)⟩

/-- The source map produced by equal-key regrouping, as the compileOpenSpine fallback sees it. -/
def repeatedBuckets (before : Signature → Signature → Bool) (originals : List (Original Value)) : List (Bucket Value) :=
  (OpenGroupComposition.groups before originals).attach.map (repeatedBucket before originals)

/-- Every fallback group contributes exactly one spine position. -/
theorem repeatedBuckets_arity (before : Signature → Signature → Bool) (originals : List (Original Value)) :
    FixedArity 1 (repeatedBuckets before originals) := by
  intro bucket present
  obtain ⟨group, _, rfl⟩ := List.mem_map.mp present
  rfl

/-- The fallback's key map is unique because the actual grouping algorithm emitted each key once. -/
theorem repeatedBuckets_keys (before : Signature → Signature → Bool) (originals : List (Original Value)) :
    (repeatedBuckets before originals).map (fun bucket => keys bucket.source) =
      (OpenGroupComposition.groups before originals).map (fun group => [groupKey group]) := by
  simp [repeatedBuckets, repeatedBucket, keys, List.map_map]

/-- Repeated original keys become one map entry, with all their original outcomes retained inside it. -/
theorem repeatedBuckets_unique (before : Signature → Signature → Bool) (originals : List (Original Value)) :
    ((repeatedBuckets before originals).map (fun bucket => keys bucket.source)).Nodup := by
  rw [repeatedBuckets_keys]
  have unique := grouped_keys_unique before originals
  have injected : ((OpenGroupComposition.groups before originals).map groupKey |>.map (fun key => [key])).Nodup := by
    apply List.pairwise_map.mpr
    exact unique.imp (fun different same => different (List.cons.inj same).1)
  simpa [List.map_map, Function.comp_def] using injected

/-- Joining applicative positions concatenates their actual coordinate keys. -/
theorem joinedKey_app (component : Nat) (functions : Source (α → β)) (arguments : Source α) :
    joinedKey (.app component functions arguments) =
      OpenIntegerKeys.join (((keys functions).map openKey) ++ ((keys arguments).map openKey)) := by
  simp [joinedKey, keys]

/-- The source optional point count multiplies across concatenated position lists. -/
theorem productPoints_append (left right : List Key) :
    productPoints (left ++ right) = (do
      let first ← productPoints left
      let second ← productPoints right
      pure (first * second)) := by
  induction left with
  | nil => simp [productPoints]
  | cons key rest ih =>
      cases keyPoints : key.points <;> cases restPoints : productPoints rest <;> cases rightPoints : productPoints right <;>
        simp [productPoints, ih, keyPoints, restPoints, rightPoints, Nat.mul_assoc]

/-- Source count metadata for each paired bucket is derived from the two actual child records. -/
theorem joinedKey_points (component : Nat) (functions : Source (α → β)) (arguments : Source α) :
    (joinedKey (.app component functions arguments)).points = (do
      let left ← (joinedKey functions).points
      let right ← (joinedKey arguments).points
      pure (left * right)) := by
  rw [joinedKey_app]
  exact productPoints_append _ _

/-- The independent Cartesian block enumerator follows the source position concatenation. -/
theorem products_append (domains : Key → List (List Int)) (left right : List Key) :
    Language.products domains (left ++ right) =
      (Language.products domains left).flatMap fun first =>
        (Language.products domains right).map (fun second => first ++ second) := by
  induction left with
  | nil => simp [Language.products]
  | cons key rest ih =>
      simp only [List.cons_append, Language.products, ih]
      simp [List.flatMap_assoc, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

/-- Complete tuple domains concatenate the function coordinates before the argument coordinates. -/
theorem joinedTuples_append (domains : Key → List (List Int)) (left right : List Key) :
    joinedTuples domains (left ++ right) =
      (joinedTuples domains left).flatMap fun first =>
        (joinedTuples domains right).map (fun second => first ++ second) := by
  simp [joinedTuples, products_append, List.map_flatMap, List.flatMap_map, List.map_map, List.flatten_append,
    Function.comp_def]

/-- Actual successful primitive tables derive the exact applicative formula domain and its stored product count. -/
theorem application_domain (component : Nat) (functions : Source (α → β)) (arguments : Source α)
    (tables : Key → LatticeAPI.Points)
    (built : ∀ key ∈ (keys (.app component functions arguments)).map openKey,
      LatticeAPI.points (names key.width) (FullSyntax.lowerFormula key.formula) = .ok (tables key))
    (stored : ∀ key ∈ (keys (.app component functions arguments)).map openKey,
      key.points = some (tables key).count.toNat) :
    let domains := fun key => pointDomain (tables key)
    let tuples := (joinedTuples domains ((keys functions).map openKey)).flatMap fun first =>
      (joinedTuples domains ((keys arguments).map openKey)).map (fun second => first ++ second)
    tuples.Nodup ∧ (joinedKey (.app component functions arguments)).points = some tuples.length ∧
      ∀ tuple, tuple ∈ tuples ↔ tuple.length = width (.app component functions arguments) ∧
        FullSyntax.Holds FullSyntax.integerModel (tupleEnv tuple) (joinedKey (.app component functions arguments)).formula := by
  dsimp only
  have exact := OpenIntegerKeys.join_finite_exact FullSyntax.integerModel ParentIntegerSettlement.integer_laws
    (by intro value; rfl) ((keys (.app component functions arguments)).map openKey)
    (fun key member => LatticeDeclaredNames.points_scoped _ _ _ (built key member))
    (fun key => pointDomain (tables key))
    (fun key member tuple => pointDomain_exact _ _ _ (built key member) tuple)
    (fun key member => pointDomain_distinct _ _ _ (built key member))
    (fun key member => by rw [pointDomain_count _ _ _ (built key member)]; exact stored key member)
  simpa [joinedKey, keys, List.map_append, joinedTuples_append, width, OpenIntegerKeys.join,
    List.map_map, openKey, Function.comp_def] using exact

/-- The actual binary chain callback uses the right source cardinality as its mixed radix. -/
def pairChildren (leftCount rightCount : Nat)
    (left right : Term (Label Symbol) → List Nat) : List (Term (Label Symbol)) → List Nat
  | [.node .centerKeyed (operation :: _), .node .argKeyed [_, function], .node .argKeyed [_, argument]] =>
      StaticCandidateRanks.productCandidates (leftCount * rightCount)
        (StaticCandidateRanks.candidates .pure .whole [operation])
        (StaticCandidateRanks.productCandidates rightCount (left function)
          (StaticCandidateRanks.productCandidates 1 (right argument) [0]))
  | _ => []

/-- Source joinNBucketStatic dispatches whole and spine views through JoinN, and labelled views through its children. -/
def pairCandidates (leftCount rightCount : Nat)
    (left right : Term (Label Symbol) → List Nat) : View → List (Term (Label Symbol)) → List Nat
  | .whole, [.node .joinN children] | .spine, [.node .joinN children] => pairChildren leftCount rightCount left right children
  | .labelled, children => pairChildren leftCount rightCount left right children
  | _, _ => []

/-- The original source callbacks are built recursively by the actual grouped constructors. -/
def candidates : Source Value → View → List (Term (Label Symbol)) → List Nat
  | .generated original, view, wanted => CompiledIntegerSpine.candidates original.recipe view wanted
  | .repeated group, view, wanted => OpenGroupComposition.candidates group.originals view wanted
  | .app _ functions arguments, view, wanted =>
      pairCandidates (cardinality functions) (cardinality arguments)
        (fun term => candidates functions .whole [term]) (fun term => candidates arguments .whole [term]) view wanted

/-- Each actual pairBucket term keeps both child candidates in the source rank-product order. -/
theorem pair_candidates_complete (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (leftCount rightCount leftRank rightRank component : Nat)
    (left right : Term (Label Symbol)) (leftCandidates rightCandidates : Term (Label Symbol) → List Nat)
    (point : List Int) (view : View)
    (leftFound : leftRank ∈ leftCandidates (fill literal exactLabel point left).2)
    (rightFound : rightRank ∈ rightCandidates (fill literal exactLabel (fill literal exactLabel point left).1 right).2) :
    Probability.pairRank rightCount leftRank rightRank ∈
      pairCandidates leftCount rightCount leftCandidates rightCandidates view
        (project view (fill literal exactLabel point (SupportJoin.joinTerm component (.node .pure []) [left, right])).2) := by
  rw [StaticCompositeCandidateRanks.fill_join]
  have tail := StaticCandidateRanks.product_member 1 _ [0] rightRank 0 rightFound (by simp)
  have front := StaticCandidateRanks.product_member rightCount _ _ leftRank rightRank leftFound
    (by simpa [Probability.pairRank] using tail)
  have operation := StaticCandidateRanks.product_member (leftCount * rightCount) [0] _ 0 _ (by simp) front
  cases view <;> simpa [project, labelled, spine, SupportTerms.applicationLeftChildren,
    SupportTerms.applicationTermChildren, pairCandidates, pairChildren, SupportJoin.joinTerm,
    SupportJoin.keys, SupportJoin.arguments, fill, fillForest, StaticCandidateRanks.candidates,
    Probability.pairRank] using operation

/-- No generated, grouped, or applicative source loses an original candidate after integer filling. -/
theorem candidates_complete (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    {source : Source Value} {rank : Nat} {term : Term (Label Symbol)} (selected : Selected source rank term)
    (point : List Int) (view : View) :
    rank ∈ candidates source view (project view (fill literal exactLabel point term).2) := by
  induction selected generalizing point view with
  | generated original => exact CompiledIntegerSpine.candidate_complete literal exactLabel original.recipe point view
  | repeated group rank => exact OpenGroupComposition.candidates_complete literal exactLabel group.originals rank point view
  | @app _ _ _ functions arguments leftRank rightRank leftTerm rightTerm component left right ihl ihr =>
      exact pair_candidates_complete literal exactLabel (cardinality functions) (cardinality arguments)
        leftRank rightRank component leftTerm rightTerm _ _ point view (ihl literal exactLabel point .whole) (ihr literal exactLabel _ .whole)

/-- The source's global outcome masses, indexed by local original rank. Size-conditioned weights remain separate. -/
def rankDistribution : Source Value → Probability.Distribution Nat
  | .generated _ => [(1, 0)]
  | .repeated group => Probability.normalize
      (group.originals.zipIdx.map (fun entry => (entry.1.mass, entry.2)))
  | .app _ functions arguments => Probability.map
      (fun ranks => Probability.pairRank (cardinality arguments) ranks.1 ranks.2)
      (Probability.product (rankDistribution functions) (rankDistribution arguments))

/-- Complete positive original groups are the source-success domain for finite bucket merging. -/
def ValidMass : Source Value → Prop
  | .generated _ => True
  | .repeated group => group.originals ≠ [] ∧ ∀ original ∈ group.originals, 0 < original.mass
  | .app _ functions arguments => ValidMass functions ∧ ValidMass arguments

/-- The global outcome record has exactly one mass slot per original replay rank. -/
theorem rankDistribution_count (source : Source Value) : (rankDistribution source).length = cardinality source := by
  induction source with
  | generated original => rfl
  | repeated group => simp [rankDistribution, Probability.normalize, Probability.scale, cardinality]
  | app component functions arguments left right =>
      simp [rankDistribution, Probability.map, SizeMass.product_length, left, right, cardinality]

/-- Value mapping preserves a probability distribution without requiring an injective map. -/
theorem map_probability (transform : α → β) (distribution : Probability.Distribution α)
    (valid : Probability.IsProbability distribution) : Probability.IsProbability (Probability.map transform distribution) := by
  constructor
  · intro entry present
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
    exact valid.1 original member
  · rw [Probability.total_map]
    exact valid.2

/-- Generated, repeated-key, and applicative global samplers are normalized from their source records. -/
theorem rankDistribution_probability (source : Source Value) (valid : ValidMass source) :
    Probability.IsProbability (rankDistribution source) := by
  induction source with
  | generated original =>
      constructor
      · intro entry present
        have same : entry = (1, 0) := by simpa [rankDistribution] using present
        subst entry
        decide
      · simp [rankDistribution, Probability.total, Rat.add_zero]
  | repeated group =>
      apply Probability.normalize_probability
      · intro entry present
        obtain ⟨indexed, member, rfl⟩ := List.mem_map.mp present
        exact Rat.le_of_lt (valid.2 indexed.1 (List.fst_mem_of_mem_zipIdx member))
      · apply Sized.total_positive
        · intro empty
          have count := congrArg List.length empty
          simp at count
          exact valid.1 count
        · intro entry present
          obtain ⟨indexed, member, rfl⟩ := List.mem_map.mp present
          exact valid.2 indexed.1 (List.fst_mem_of_mem_zipIdx member)
  | app component functions arguments left right =>
      exact map_probability _ _ (Probability.product_probability _ _ (left valid.1) (right valid.2))

/-- Component indexes do not affect their global outcome weights. -/
theorem pair_global_distribution (component : Nat) (functions : Source (α → β)) (arguments : Source α) :
    rankDistribution (.app component functions arguments) = Probability.map
      (fun ranks => Probability.pairRank (cardinality arguments) ranks.1 ranks.2)
      (Probability.product (rankDistribution functions) (rankDistribution arguments)) := rfl

/-- Sum the actual outer bucket mass fields. -/
def totalMass (buckets : List (Bucket Value)) : Rat := (buckets.map Bucket.mass).sum

/-- Zipped source component indexes do not change a projection that reads only the underlying pair. -/
theorem map_zipIdx {Item : Type u} {Output : Type v} (items : List Item) (transform : Item → Output) :
    (items.zipIdx.map (fun entry => transform entry.1)) = items.map transform := by
  have same := congrArg (List.map transform) (List.zipIdx_map_fst 0 items)
  simpa only [List.map_map, Function.comp_def] using same

/-- A finite pair bucket has the product of the two incoming outer masses. -/
theorem applyBuckets_masses (left : List (Bucket (α → β))) (right : List (Bucket α)) :
    (applyBuckets left right).map Bucket.mass =
      (pairs left right).map (fun pair => pair.1.mass * pair.2.mass) := by
  simp only [applyBuckets, List.map_map, component, Function.comp_def]
  exact map_zipIdx (pairs left right) (fun pair => pair.1.mass * pair.2.mass)

/-- Summing all pair masses gives exactly the product of the complete child totals. -/
theorem applyBuckets_totalMass (left : List (Bucket (α → β))) (right : List (Bucket α)) :
    totalMass (applyBuckets left right) = totalMass left * totalMass right := by
  rw [totalMass, applyBuckets_masses]
  have rowMass (mass : Rat) : (right.map (fun bucket => mass * bucket.mass)).sum = mass * totalMass right := by
    induction right with
    | nil => simp [totalMass]
    | cons first rest ih => simp [totalMass] at ih ⊢; rw [ih, Rat.mul_add]
  induction left with
  | nil => simp [pairs, totalMass]
  | cons first rest ih =>
      simp only [pairs, List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
        Function.comp_def, rowMass]
      simp only [pairs] at ih
      rw [ih]
      simp [totalMass, Rat.add_mul]

/-- mergeComponentsByKey normalizes outer fields without altering static sources. -/
def normalizeBuckets (buckets : List (Bucket Value)) : List (Bucket Value) :=
  buckets.map (fun bucket => {bucket with mass := bucket.mass / totalMass buckets})

/-- Outer mass normalization leaves every private term, original rank, and key list unchanged. -/
theorem normalize_sources (buckets : List (Bucket Value)) :
    (normalizeBuckets buckets).map Bucket.source = buckets.map Bucket.source := by
  simp [normalizeBuckets, List.map_map]

/-- The actual product normalizer assigns each bucket pair its exact share of the child totals. -/
theorem normalized_pair_mass (left : List (Bucket (α → β))) (right : List (Bucket α))
    (function : Fin left.length) (argument : Fin right.length) :
    ((normalizeBuckets (applyBuckets left right))[Probability.pairRank right.length function.val argument.val]?).map Bucket.mass =
      some (left[function.val].mass * right[argument.val].mass / (totalMass left * totalMass right)) := by
  simp [normalizeBuckets, List.getElem?_map, applyBuckets_get, component, applyBuckets_totalMass]

/-- For normalized child families, the outer product mass is already the final pair mass. -/
theorem normalized_pair_probability (left : List (Bucket (α → β))) (right : List (Bucket α))
    (leftNormalized : totalMass left = 1) (rightNormalized : totalMass right = 1)
    (function : Fin left.length) (argument : Fin right.length) :
    ((normalizeBuckets (applyBuckets left right))[Probability.pairRank right.length function.val argument.val]?).map Bucket.mass =
      some (left[function.val].mass * right[argument.val].mass) := by
  rw [normalized_pair_mass, leftNormalized, rightNormalized]
  simp [Rat.div_def]

/-- Source key grouping has singleton buckets when its input keys are already unique. -/
theorem unique_groups_singletons (before : List Signature → List Signature → Bool) (buckets : List (Bucket Value))
    (unique : (buckets.map (fun bucket => keys bucket.source)).Nodup)
    (group : List (Bucket Value)) (present : group ∈ groupOutcomes before (fun bucket => keys bucket.source) buckets) :
    ∃ bucket, group = [bucket] := by
  have perm := groupOutcomes_perm before (fun bucket => keys bucket.source) buckets
  have allUnique := (perm.map (fun bucket => keys bucket.source)).nodup_iff.mpr unique
  have groupUnique := allUnique.sublist ((List.sublist_flatten_of_mem present).map (fun bucket => keys bucket.source))
  obtain ⟨first, rest, rfl, homogeneous⟩ := groupOutcomes_key before (fun bucket => keys bucket.source) buckets group present
  cases rest with
  | nil => exact ⟨first, rfl⟩
  | cons second rest =>
      have different : keys first.source ≠ keys second.source := by
        have pairwise := List.pairwise_map.mp groupUnique
        exact (List.pairwise_cons.mp pairwise).1 second (by simp)
      exact False.elim (different (homogeneous second (by simp)).symm)

/-- Only the exact source singleton fast-path case is represented here; None requests its general merge branch. -/
def singletonPath : List (Bucket Value) → Option (Bucket Value)
  | [bucket] => if 0 < bucket.mass then some bucket else none
  | _ => none

/-- Every actual applicative key group takes mergeBucketGroup's payload-preserving singleton branch. -/
theorem applicative_singleton_path (before : List Signature → List Signature → Bool)
    (left : List (Bucket (α → β))) (right : List (Bucket α))
    (leftArity : Nat) (fixed : FixedArity leftArity left)
    (leftUnique : (left.map (fun bucket => keys bucket.source)).Nodup)
    (rightUnique : (right.map (fun bucket => keys bucket.source)).Nodup)
    (leftPositive : ∀ bucket ∈ left, 0 < bucket.mass) (rightPositive : ∀ bucket ∈ right, 0 < bucket.mass)
    (group : List (Bucket β)) (present : group ∈ groupOutcomes before (fun bucket => keys bucket.source) (applyBuckets left right)) :
    ∃ bucket, group = [bucket] ∧ singletonPath group = some bucket := by
  obtain ⟨bucket, shape⟩ := unique_groups_singletons before (applyBuckets left right)
    (applyBuckets_keys_unique left right leftArity fixed leftUnique rightUnique) group present
  have member : bucket ∈ applyBuckets left right :=
    (groupOutcomes_perm before (fun bucket => keys bucket.source) _).mem_iff.mp
      (List.mem_flatten.mpr ⟨group, present, by simp [shape]⟩)
  obtain ⟨entry, indexed, same⟩ := List.mem_map.mp member
  have pairMember := List.fst_mem_of_mem_zipIdx indexed
  obtain ⟨firstMember, secondMember⟩ := (pairs_member left right entry.1.1 entry.1.2).mp pairMember
  have positive : 0 < bucket.mass := by
    rw [← same]
    exact Rat.mul_pos (leftPositive _ firstMember) (rightPositive _ secondMember)
  exact ⟨bucket, shape, by simp [shape, singletonPath, positive]⟩

/-- Integer closure uses the recursively built actual original callbacks and exact whole-view validation. -/
def pointCandidates [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (source : Source Value) (points : LatticeAPI.Points)
    (view : View) (wanted : List (Term (Label Symbol))) : List Nat :=
  (candidates source view wanted).flatMap fun originalRank =>
    match select source originalRank with
    | none => []
    | some term =>
        match rankView literal exactLabel read points view term wanted with
        | none => []
        | some pointRank => [Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank pointRank]

/-- Every concrete multi-group original and point pair reaches its actual combined rank. -/
theorem points_complete [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    {source : Source Value} {rank : Nat} {term : Term (Label Symbol)} (selected : Selected source rank term)
    (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (width source)) (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (pointRank : Fin (LatticeSelect.pointCount points.levels)) :
    Probability.pairRank (LatticeSelect.pointCount points.levels) rank pointRank.val ∈
      pointCandidates literal exactLabel read source points view (decodeView literal exactLabel points view term pointRank) := by
  apply List.mem_flatMap.mpr
  refine ⟨rank, candidates_complete literal exactLabel selected _ view, ?_⟩
  rw [selected_select selected]
  simp only []
  rw [rank_decode literal exactLabel read literalRead (names (width source)) formula points built view term
    (selected_valid selected) (by simpa [names] using selected_width selected) pointRank]
  simp

/-- No accepted closure rank can refer to a missing original or an absent lattice point. -/
theorem points_sound [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (source : Source Value) (declared : List FullSyntax.Name)
    (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points declared (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (wanted : List (Term (Label Symbol))) (rank : Nat)
    (accepted : rank ∈ pointCandidates literal exactLabel read source points view wanted) :
    ∃ originalRank term, Selected source originalRank term ∧
      ∃ pointRank : Fin (LatticeSelect.pointCount points.levels),
        rank = Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank pointRank.val ∧
        decodeView literal exactLabel points view term pointRank = wanted := by
  obtain ⟨originalRank, _, accepted⟩ := List.mem_flatMap.mp accepted
  cases chosen : select (Symbol := Symbol) source originalRank with
  | none => simp [chosen] at accepted
  | some term =>
      simp only [chosen] at accepted
      cases ranked : rankView literal exactLabel read points view term wanted with
      | none => simp [ranked] at accepted
      | some pointRank =>
          have same : rank = Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank pointRank := by
            simpa [ranked] using accepted
          obtain ⟨validRank, value, decoded⟩ := rankView_sound literal exactLabel read declared formula points built
            view term wanted pointRank ranked
          exact ⟨originalRank, term, (select_exact source originalRank term).mp chosen, validRank,
            by simpa [value] using same, decoded⟩

/-- The complete recursively built source has no holes in its original-times-point rank interval. -/
theorem every_closed_rank [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (source : Source Value) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (width source)) (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (rank : Nat) (bound : rank < cardinality source * LatticeSelect.pointCount points.levels) :
    ∃ wanted, rank ∈ pointCandidates literal exactLabel read source points view wanted := by
  have bounds := Probability.split_lt bound
  obtain ⟨term, selected⟩ := selected_exists source _ bounds.1
  let pointRank : Fin (LatticeSelect.pointCount points.levels) := ⟨(Probability.splitRank _ rank).2, bounds.2⟩
  refine ⟨decodeView literal exactLabel points view term pointRank, ?_⟩
  have present := points_complete literal exactLabel read literalRead selected formula points built view pointRank
  simpa [pointRank, Probability.pair_split] using present

/-- Actual lattice points provide exactly the coordinate length required by the source value reader. -/
theorem closed_value_total (source : Source Value) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (width source)) (FullSyntax.lowerFormula formula) = .ok points)
    (originalRank : Fin (cardinality source)) (pointRank : Fin (LatticeSelect.pointCount points.levels)) :
    ∃ value, evaluate source originalRank.val (LatticeSelect.decode points.dimension points.levels pointRank) = some value := by
  obtain ⟨term, selected⟩ := selected_exists (Symbol := Unit) source originalRank.val originalRank.isLt
  apply evaluate_total selected
  have present : LatticeSelect.decode points.dimension points.levels pointRank ∈ pointDomain points :=
    List.mem_ofFn.mpr ⟨pointRank, rfl⟩
  have dimension := (pointDomain_exact _ _ points built _).mp present
  simpa [names] using dimension.1

/-- The public counter sees the same total coordinate width as the source reader and term. -/
theorem joined_width (source : Source Value) : (joinedKey source).width = width source := by
  simp [joinedKey, OpenIntegerKeys.join, width, List.map_map, openKey, Function.comp_def]

/-- The parent appends its translated conditions to all concrete source position formulas. -/
def parentFormula (source : Source Value) (parents : List FullSyntax.Formula) : FullSyntax.Formula :=
  ParentIntegerSettlement.restrictedFormula ((keys source).map openKey) parents

/-- A closed source record retains the original source, actual point table, and computed retained share. -/
structure ClosedBucket (Value : Type) where
  original : Bucket Value
  points : LatticeAPI.Points
  kept : Rat

/-- Execute the finite closed-parent counting and empty-group decision for this source. -/
def settle (parents : List FullSyntax.Formula) (bucket : Bucket Value) :
    Except (LatticeAPI.Error String) (Option (ClosedBucket Value)) :=
  match LatticeAPI.points (names (width bucket.source)) (FullSyntax.lowerFormula (parentFormula bucket.source parents)) with
  | .error error => .error error
  | .ok points =>
      if points.count = 0 then .ok none
      else .ok (some ⟨bucket, points, RecipeCompile.retainedShare points.count.toNat
        (((keys bucket.source).map openKey).map ParentIntegerSettlement.childInfo)⟩)

/-- Every retained closed record comes from the actual query, with unchanged original metadata. -/
theorem settle_fields (parents : List FullSyntax.Formula) (bucket : Bucket Value) (closed : ClosedBucket Value)
    (success : settle parents bucket = .ok (some closed)) :
    closed.original = bucket ∧ closed.points.count ≠ 0 ∧
      LatticeAPI.points (names (width bucket.source)) (FullSyntax.lowerFormula (parentFormula bucket.source parents)) = .ok closed.points ∧
      closed.kept = RecipeCompile.retainedShare closed.points.count.toNat
        (((keys bucket.source).map openKey).map ParentIntegerSettlement.childInfo) := by
  cases query : LatticeAPI.points (names (width bucket.source)) (FullSyntax.lowerFormula (parentFormula bucket.source parents)) with
  | error error => simp [settle, query] at success
  | ok points =>
      by_cases zero : points.count = 0
      · simp [settle, query, zero] at success
      · have same : closed = ⟨bucket, points, RecipeCompile.retainedShare points.count.toNat
            (((keys bucket.source).map openKey).map ParentIntegerSettlement.childInfo)⟩ := by
          simpa [settle, query, zero] using success.symm
        subst closed
        simp [zero]

/-- Parent closure pairs the actual original rank masses with uniform retained points. -/
def closedDistribution (closed : ClosedBucket Value) : Probability.Distribution (Nat × List Int) :=
  Probability.scale (closed.original.mass * closed.kept)
    (Probability.product (rankDistribution closed.original.source)
      (Probability.normalize (Probability.counting (pointDomain closed.points))))

/-- The source closed cardinality counts each original member at every retained point. -/
theorem closed_count (parents : List FullSyntax.Formula) (bucket : Bucket Value) (closed : ClosedBucket Value)
    (success : settle parents bucket = .ok (some closed)) :
    (closedDistribution closed).length = cardinality bucket.source * closed.points.count.toNat := by
  have fields := settle_fields parents bucket closed success
  simp only [closedDistribution, Probability.scale, List.length_map, SizeMass.product_length,
    Probability.normalize, Probability.counting, rankDistribution_count, fields.1]
  rw [pointDomain_count _ _ _ fields.2.2.1]

/-- A successful source settlement derives its complete original-times-point replay interval. -/
theorem settled_every_rank
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (parents : List FullSyntax.Formula) (bucket : Bucket Value) (closed : ClosedBucket Value)
    (success : settle parents bucket = .ok (some closed)) (view : View) (rank : Nat)
    (bound : rank < cardinality bucket.source * LatticeSelect.pointCount closed.points.levels) :
    ∃ wanted, rank ∈ pointCandidates IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
      bucket.source closed.points view wanted :=
  every_closed_rank IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
    IntegerLabelCodec.leafValue_integer bucket.source (parentFormula bucket.source parents) closed.points
    (settle_fields parents bucket closed success).2.2.1 view rank bound

/-- A successful settlement also derives total decoding of every source value. -/
theorem settled_value_total (parents : List FullSyntax.Formula) (bucket : Bucket Value) (closed : ClosedBucket Value)
    (success : settle parents bucket = .ok (some closed))
    (originalRank : Fin (cardinality bucket.source)) (pointRank : Fin (LatticeSelect.pointCount closed.points.levels)) :
    ∃ value, evaluate bucket.source originalRank.val
      (LatticeSelect.decode closed.points.dimension closed.points.levels pointRank) = some value :=
  closed_value_total bucket.source (parentFormula bucket.source parents) closed.points
    (settle_fields parents bucket closed success).2.2.1 originalRank pointRank

/-- Scaling a product distributes the outer source mass over each original rank. -/
theorem scale_product (mass : Rat) (left : Probability.Distribution α) (right : Probability.Distribution β) :
    Probability.scale mass (Probability.product left right) =
      left.flatMap (fun entry => Probability.map (fun value => (entry.2, value)) (Probability.scale (mass * entry.1) right)) := by
  simp [Probability.scale, Probability.product, Probability.map, List.map_flatMap, List.map_map,
    Function.comp_def, Rat.mul_assoc]

/-- A guard on coordinates filters each original rank without inspecting or changing its weight. -/
theorem restrict_product (mass : Rat) (left : Probability.Distribution α) (right : Probability.Distribution β)
    (accepted : β → Bool) :
    Probability.restrict (fun pair => accepted pair.2) (Probability.scale mass (Probability.product left right)) =
      left.flatMap (fun entry => Probability.map (fun value => (entry.2, value))
        (Probability.restrict accepted (Probability.scale (mass * entry.1) right))) := by
  rw [scale_product]
  simp [Probability.restrict, Probability.map, List.filter_flatMap, List.filter_map, Function.comp_def]

/-- The complete source rank distribution keeps exactly the mass of the actual parent tuple restriction. -/
theorem parent_event (source : Source Value) (parents : List FullSyntax.Formula)
    (tables : Key → LatticeAPI.Points)
    (built : ∀ key ∈ (keys source).map openKey,
      LatticeAPI.points (names key.width) (FullSyntax.lowerFormula key.formula) = .ok (tables key))
    (stored : ∀ key ∈ (keys source).map openKey, key.points = some (tables key).count.toNat)
    (points : LatticeAPI.Points)
    (parentBuilt : LatticeAPI.points (names (width source)) (FullSyntax.lowerFormula (parentFormula source parents)) = .ok points)
    (mass : Rat) (event : Nat × List Int → Bool) :
    Probability.eventMass event
      (Probability.scale (mass * RecipeCompile.retainedShare points.count.toNat
          (((keys source).map openKey).map ParentIntegerSettlement.childInfo))
        (Probability.product (rankDistribution source) (Probability.normalize (Probability.counting (pointDomain points))))) =
      Probability.eventMass event (Probability.restrict (fun pair => ParentIntegerSettlement.parentAllows parents pair.2)
        (Probability.scale mass (Probability.product (rankDistribution source)
          (Probability.normalize (Probability.counting (joinedTuples (fun key => pointDomain (tables key)) ((keys source).map openKey))))))) := by
  rw [scale_product, restrict_product]
  have counter : LatticeAPI.points (names (OpenIntegerKeys.join ((keys source).map openKey)).width)
      (FullSyntax.lowerFormula (ParentIntegerSettlement.restrictedFormula ((keys source).map openKey) parents)) = .ok points := by
    change LatticeAPI.points (names (joinedKey source).width)
      (FullSyntax.lowerFormula (parentFormula source parents)) = .ok points
    rw [joined_width]
    exact parentBuilt
  apply OpenGroupComposition.event_flatMap
  intro entry _
  simp only [Probability.eventMass_map, Function.comp_def]
  have factor : (mass * RecipeCompile.retainedShare points.count.toNat
      (((keys source).map openKey).map ParentIntegerSettlement.childInfo)) * entry.1 =
      (mass * entry.1) * RecipeCompile.retainedShare points.count.toNat
        (((keys source).map openKey).map ParentIntegerSettlement.childInfo) := by
    rw [Rat.mul_assoc, Rat.mul_comm _ entry.1, ← Rat.mul_assoc]
  rw [factor]
  exact ParentIntegerSettlement.counted_parent_event ((keys source).map openKey) parents tables built stored
    points counter (mass * entry.1) (fun tuple => event (entry.2, tuple))

/-- The retained source record has exactly the finite conditioned distribution required by its constructor. -/
theorem settled_conditioned (parents : List FullSyntax.Formula) (bucket : Bucket Value) (closed : ClosedBucket Value)
    (success : settle parents bucket = .ok (some closed)) (tables : Key → LatticeAPI.Points)
    (built : ∀ key ∈ (keys bucket.source).map openKey,
      LatticeAPI.points (names key.width) (FullSyntax.lowerFormula key.formula) = .ok (tables key))
    (stored : ∀ key ∈ (keys bucket.source).map openKey, key.points = some (tables key).count.toNat)
    (event : Nat × List Int → Bool) :
    Probability.eventMass event (Probability.normalize (closedDistribution closed)) =
      Probability.eventMass event (Probability.condition (fun pair => ParentIntegerSettlement.parentAllows parents pair.2)
        (Probability.scale bucket.mass (Probability.product (rankDistribution bucket.source)
          (Probability.normalize (Probability.counting (joinedTuples (fun key => pointDomain (tables key)) ((keys bucket.source).map openKey))))))) := by
  have fields := settle_fields parents bucket closed success
  apply OpenGroupComposition.normalize_events
  intro queryEvent
  simpa [closedDistribution, fields.1, fields.2.2.2] using
    parent_event bucket.source parents tables built stored closed.points fields.2.2.1 bucket.mass queryEvent

/-- The parent source callback validates its root and forwards labelled children to the actual recursive source. -/
def parentCandidates (acceptsLabel : Symbol → Bool) (source : Source Value)
    (_view : View) (wanted : List (Term (Label Symbol))) : List Nat :=
  match wanted with
  | [.node (.user found) children] => if acceptsLabel found then candidates source .labelled children else []
  | _ => []

/-- Parent root construction preserves every original callback, including nested multi-group JoinN sources. -/
theorem parent_candidates_complete (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (symbol : Symbol) (acceptsLabel : Symbol → Bool)
    (compatible : ∀ point, acceptsLabel (exactLabel point symbol) = true)
    {source : Source Value} {rank : Nat} {term : Term (Label Symbol)} (selected : Selected source rank term)
    (point : List Int) (view : View) :
    rank ∈ parentCandidates acceptsLabel source view
      (project view (fill literal exactLabel point (SupportTerms.labelTerm symbol term)).2) := by
  rw [labelled_source]
  simp only [fill, StaticCandidateRanks.project_user, parentCandidates, compatible point, ↓reduceIte]
  have same := congrArg Prod.snd (labelled_fill literal exactLabel point term (selected_valid selected))
  rw [same]
  exact candidates_complete literal exactLabel selected point .labelled

/-- Exact pointsStatic after the actual parent label adapter. -/
def parentPointCandidates [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (symbol : Symbol) (acceptsLabel : Symbol → Bool)
    (source : Source Value) (points : LatticeAPI.Points)
    (view : View) (wanted : List (Term (Label Symbol))) : List Nat :=
  (parentCandidates acceptsLabel source view wanted).flatMap fun originalRank =>
    match select source originalRank with
    | none => []
    | some term =>
        match rankView literal exactLabel read points view (SupportTerms.labelTerm symbol term) wanted with
        | none => []
        | some pointRank => [Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank pointRank]

/-- The actual parent wrapper preserves the complete source original-times-point rank interval. -/
theorem parent_points_complete [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (literalRead : ∀ value, read (literal value) = some value)
    (symbol : Symbol) (acceptsLabel : Symbol → Bool)
    (compatible : ∀ point, acceptsLabel (exactLabel point symbol) = true)
    {source : Source Value} {rank : Nat} {term : Term (Label Symbol)} (selected : Selected source rank term)
    (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (width source)) (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (pointRank : Fin (LatticeSelect.pointCount points.levels)) :
    Probability.pairRank (LatticeSelect.pointCount points.levels) rank pointRank.val ∈
      parentPointCandidates literal exactLabel read symbol acceptsLabel source points view
        (decodeView literal exactLabel points view (SupportTerms.labelTerm symbol term) pointRank) := by
  apply List.mem_flatMap.mpr
  refine ⟨rank, parent_candidates_complete literal exactLabel symbol acceptsLabel compatible selected _ view, ?_⟩
  rw [selected_select selected]
  simp only []
  rw [rank_decode literal exactLabel read literalRead (names (width source)) formula points built view
    (SupportTerms.labelTerm symbol term) (label_valid symbol term (selected_valid selected))
    (by rw [label_count literal symbol term (selected_valid selected), selected_width selected]; simp [names]) pointRank]
  simp

/-- A parent candidate survives full point validation only at an actual source original and integer point. -/
theorem parent_points_sound [DecidableEq Symbol] (literal : Int → Symbol) (exactLabel : List Int → Symbol → Symbol)
    (read : Symbol → Option Int) (symbol : Symbol) (acceptsLabel : Symbol → Bool)
    (source : Source Value) (declared : List FullSyntax.Name) (formula : FullSyntax.Formula) (points : LatticeAPI.Points)
    (built : LatticeAPI.points declared (FullSyntax.lowerFormula formula) = .ok points)
    (view : View) (wanted : List (Term (Label Symbol))) (rank : Nat)
    (accepted : rank ∈ parentPointCandidates literal exactLabel read symbol acceptsLabel source points view wanted) :
    ∃ originalRank term, Selected source originalRank term ∧
      ∃ pointRank : Fin (LatticeSelect.pointCount points.levels),
        rank = Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank pointRank.val ∧
        decodeView literal exactLabel points view (SupportTerms.labelTerm symbol term) pointRank = wanted := by
  obtain ⟨originalRank, _, accepted⟩ := List.mem_flatMap.mp accepted
  cases chosen : select (Symbol := Symbol) source originalRank with
  | none => simp [chosen] at accepted
  | some term =>
      simp only [chosen] at accepted
      cases ranked : rankView literal exactLabel read points view (SupportTerms.labelTerm symbol term) wanted with
      | none => simp [ranked] at accepted
      | some pointRank =>
          have same : rank = Probability.pairRank (LatticeSelect.pointCount points.levels) originalRank pointRank := by
            simpa [ranked] using accepted
          obtain ⟨validRank, value, decoded⟩ := rankView_sound literal exactLabel read declared formula points built
            view (SupportTerms.labelTerm symbol term) wanted pointRank ranked
          exact ⟨originalRank, term, (select_exact source originalRank term).mp chosen, validRank,
            by simpa [value] using same, decoded⟩

/-- Successful source settlement and actual integer label specialization derive exact parent-view rank answers. -/
theorem settled_parent_ranks_exact
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol) (symbol : IntegerLabelCodec.Symbol)
    (specialized : ∀ point, IntegerLabelCodec.exactLabel point symbol = .ok (specialize point symbol))
    (parents : List FullSyntax.Formula) (bucket : Bucket Value) (closed : ClosedBucket Value)
    (success : settle parents bucket = .ok (some closed))
    (view : View) (wanted : List (Term (Label IntegerLabelCodec.Symbol))) (rank : Nat) :
    rank ∈ parentPointCandidates IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue symbol
      (IntegerLabelCodec.fills symbol) bucket.source closed.points view wanted ↔
      ∃ originalRank term, Selected bucket.source originalRank term ∧
        ∃ pointRank : Fin (LatticeSelect.pointCount closed.points.levels),
          rank = Probability.pairRank (LatticeSelect.pointCount closed.points.levels) originalRank pointRank.val ∧
          decodeView IntegerLabelCodec.integerSymbol specialize closed.points view
            (SupportTerms.labelTerm symbol term) pointRank = wanted := by
  have built := (settle_fields parents bucket closed success).2.2.1
  constructor
  · exact parent_points_sound IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue symbol
      (IntegerLabelCodec.fills symbol) bucket.source _ _ closed.points built view wanted rank
  · rintro ⟨originalRank, term, selected, pointRank, rfl, rfl⟩
    exact parent_points_complete IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
      IntegerLabelCodec.leafValue_integer symbol (IntegerLabelCodec.fills symbol)
      (fun point => IntegerLabelCodec.exactLabel_matches point symbol _ (specialized point)) selected
      (parentFormula bucket.source parents) closed.points built view pointRank

/-- The actual result map order follows key grouping after component indexes have been assigned. -/
def mergedBuckets (before : List Signature → List Signature → Bool)
    (left : List (Bucket (α → β))) (right : List (Bucket α)) : List (Bucket β) :=
  normalizeBuckets ((groupOutcomes before (fun bucket => keys bucket.source) (applyBuckets left right)).flatten)

/-- Result-key sorting and outer normalization retain the complete indexed static sources. -/
theorem merged_sources_perm (before : List Signature → List Signature → Bool)
    (left : List (Bucket (α → β))) (right : List (Bucket α)) :
    ((mergedBuckets before left right).map Bucket.source).Perm ((applyBuckets left right).map Bucket.source) := by
  rw [mergedBuckets, normalize_sources]
  exact (groupOutcomes_perm before (fun bucket => keys bucket.source) (applyBuckets left right)).map Bucket.source

/-- Source map construction retains every bucket-pair slot after its key sort. -/
theorem merged_count (before : List Signature → List Signature → Bool)
    (left : List (Bucket (α → β))) (right : List (Bucket α)) :
    (mergedBuckets before left right).length = left.length * right.length := by
  have same := (merged_sources_perm before left right).length_eq
  simpa [applyBuckets_count] using same

/-- The sum of stored original outcome cardinalities in a family. -/
def totalCount (buckets : List (Bucket Value)) : Nat := (buckets.map (fun bucket => cardinality bucket.source)).sum

/-- The actual pair constructor derives its original-count product independently of coordinate counts. -/
theorem applyBuckets_counts (left : List (Bucket (α → β))) (right : List (Bucket α)) :
    (applyBuckets left right).map (fun bucket => cardinality bucket.source) =
      (pairs left right).map (fun pair => cardinality pair.1.source * cardinality pair.2.source) := by
  simp only [applyBuckets, List.map_map, component, cardinality, Function.comp_def]
  exact map_zipIdx (pairs left right) (fun pair => cardinality pair.1.source * cardinality pair.2.source)

/-- Source bucket-pair cardinalities sum to exactly the full original-member product. -/
theorem applyBuckets_totalCount (left : List (Bucket (α → β))) (right : List (Bucket α)) :
    totalCount (applyBuckets left right) = totalCount left * totalCount right := by
  rw [totalCount, applyBuckets_counts]
  have rowCount (count : Nat) :
      (right.map (fun bucket => count * cardinality bucket.source)).sum = count * totalCount right := by
    induction right with
    | nil => simp [totalCount]
    | cons first rest ih => simp [totalCount] at ih ⊢; rw [ih, Nat.mul_add]
  induction left with
  | nil => simp [pairs, totalCount]
  | cons first rest ih =>
      simp only [pairs, List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
        Function.comp_def, rowCount]
      simp only [pairs] at ih
      rw [ih]
      simp [totalCount, Nat.add_mul]

/-- The actual key map's complete original count survives sorting and normalization. -/
theorem merged_totalCount (before : List Signature → List Signature → Bool)
    (left : List (Bucket (α → β))) (right : List (Bucket α)) :
    totalCount (mergedBuckets before left right) = totalCount left * totalCount right := by
  have same := ((merged_sources_perm before left right).map cardinality).sum_nat
  have preserved : totalCount (mergedBuckets before left right) = totalCount (applyBuckets left right) := by
    simpa [totalCount, List.map_map, Function.comp_def] using same
  exact preserved.trans (applyBuckets_totalCount left right)

/-- Every exact ordered input bucket pair survives in the final source map with its component identifier. -/
theorem merged_pair_source (before : List Signature → List Signature → Bool)
    (left : List (Bucket (α → β))) (right : List (Bucket α))
    (function : Fin left.length) (argument : Fin right.length) :
    Source.app (Probability.pairRank right.length function.val argument.val)
      left[function.val].source right[argument.val].source ∈
        (mergedBuckets before left right).map Bucket.source := by
  apply (merged_sources_perm before left right).mem_iff.mpr
  have selected := List.mem_of_getElem? (applyBuckets_get left right function argument)
  exact List.mem_map.mpr ⟨_, selected, rfl⟩

/-- The result family retains the same number of source positions in every bucket. -/
theorem merged_arity (before : List Signature → List Signature → Bool)
    (left : List (Bucket (α → β))) (right : List (Bucket α))
    (leftArity rightArity : Nat) (leftFixed : FixedArity leftArity left) (rightFixed : FixedArity rightArity right) :
    FixedArity (leftArity + rightArity) (mergedBuckets before left right) := by
  intro bucket present
  have sourceMember := (merged_sources_perm before left right).mem_iff.mp
    (List.mem_map.mpr ⟨bucket, present, rfl⟩)
  obtain ⟨original, member, same⟩ := List.mem_map.mp sourceMember
  rw [← same]
  exact applyBuckets_arity left right leftArity rightArity leftFixed rightFixed original member

/-- Result-key map uniqueness is closed under any further applicative product. -/
theorem merged_keys_unique (before : List Signature → List Signature → Bool)
    (left : List (Bucket (α → β))) (right : List (Bucket α))
    (leftArity : Nat) (fixed : FixedArity leftArity left)
    (leftUnique : (left.map (fun bucket => keys bucket.source)).Nodup)
    (rightUnique : (right.map (fun bucket => keys bucket.source)).Nodup) :
    ((mergedBuckets before left right).map (fun bucket => keys bucket.source)).Nodup := by
  have same := (merged_sources_perm before left right).map keys
  have unique := applyBuckets_keys_unique left right leftArity fixed leftUnique rightUnique
  exact (by simpa [List.map_map, Function.comp_def] using same.nodup_iff.mpr (by simpa [List.map_map, Function.comp_def] using unique))

end MicroCFTA.OpenGroupedApplication
