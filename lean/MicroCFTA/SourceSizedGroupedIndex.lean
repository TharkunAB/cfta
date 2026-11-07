import MicroCFTA.RecursiveJoinTyped
import MicroCFTA.SourceSizedGroupedClasses

/-!
# Count and selector fields of the source grouped row fold

The index below retains the source count and selector operations. Products
call `SizedRank.productSplit`. Choice subtracts earlier branch counts. The
row fold starts with a paid constant function. Each child maps `prepend`
over that function index before it forms the product.

Independent class lists specify count and selector order. They do not
construct the index. A selector law applies only below the class count.
This restriction is required by the source raw scale selector.

The field projection omits sparse storage, minimum metadata, the lazy
recursive table knot, and machine index conversions. Source sizes and
cardinalities use Integer. Natural sizes here have no machine word bound.
The empty-annotation shortcut has its own literal class expression. The
grouped branch agrees with the checked grouped row class.
-/
namespace MicroCFTA.SourceSizedGroupedIndex
open Language RecursiveSize SizedRank SourceSizedDecided
open RecursiveJoinFields (ValueIndex convolve)
open RecursiveJoinTyped (mapIndex productIndex)
open SourceSizedGroupedChainOrder (seed scaled groupClass assemble rowClass)

variable {State Symbol Key Value Result Left Right : Type}

/-- Independent ordered classes specify the source fields at counted positions. -/
structure Correct (index : ValueIndex Value) (classes : Nat → List Value) : Prop where
  counts : ∀ size, index.counts size = (classes size).length
  select : ∀ position, position.rank < index.counts position.size →
    index.select position = (classes position.size)[position.rank]?

/-- Equal independent class expressions preserve the field law. -/
theorem Correct.congr {index : ValueIndex Value} {first second : Nat → List Value}
    (correct : Correct index first) (same : ∀ size, first size = second size) :
    Correct index second := by
  have equal : first = second := funext same
  simpa only [equal] using correct

/-- The source constant contributes one member at size zero. -/
def constantIndex (value : Value) : ValueIndex Value :=
  ⟨fun size => if size = 0 then 1 else 0,
    fun position => if position.size = 0 ∧ position.rank = 0 then some value else none⟩

/-- Pay shifts counts and removes one size unit before the source selector read. -/
def payIndex (index : ValueIndex Value) : ValueIndex Value :=
  ⟨fun size => match size with | 0 => 0 | size + 1 => index.counts size,
    fun position => index.select ⟨position.size - 1, position.rank⟩⟩

/-- Scaling preserves rank and divides the size of the raw selector read. -/
def scaleIndex (factor : Nat) (index : ValueIndex Value) : ValueIndex Value :=
  if factor = 1 then index else
    ⟨fun size => if size % factor = 0 then index.counts (size / factor) else 0,
      fun position => index.select ⟨position.size / factor, position.rank⟩⟩

/-- The empty source choice has no counted positions. -/
def emptyIndex : ValueIndex Value := ⟨fun _ => 0, fun _ => none⟩

/-- The source branch selector subtracts the preceding class count. -/
def selectChoice : List (ValueIndex Value) → Position → Option Value
  | [], _ => none
  | first :: rest, position =>
      if position.rank < first.counts position.size then first.select position
      else selectChoice rest ⟨position.size, position.rank - first.counts position.size⟩

/-- Ordered choice adds class counts without constructing class members. -/
def choiceIndex (indexes : List (ValueIndex Value)) : ValueIndex Value :=
  ⟨fun size => (indexes.map fun index => index.counts size).sum, selectChoice indexes⟩

/-- The constant selector agrees with its one-member independent class. -/
theorem constant_correct (value : Value) :
    Correct (constantIndex value) (fun size => if size = 0 then [value] else []) := by
  constructor
  · intro size
    by_cases zero : size = 0 <;> simp [constantIndex, zero]
  · intro position bounded
    have zero : position.size = 0 := by
      by_cases zero : position.size = 0
      · exact zero
      · simp [constantIndex, zero] at bounded
    have rankZero : position.rank = 0 := by
      have small : position.rank < 1 := by
        simpa only [constantIndex, zero, ite_true] using bounded
      omega
    simp [constantIndex, zero, rankZero]

/-- Mapping the source values preserves every class position. -/
theorem map_correct (transform : Value → Result) (index : ValueIndex Value)
    (classes : Nat → List Value) (correct : Correct index classes) :
    Correct (mapIndex transform index) (fun size => (classes size).map transform) := by
  constructor
  · intro size
    simpa only [mapIndex, List.length_map] using correct.counts size
  · intro position bounded
    have read := correct.select position bounded
    simpa only [mapIndex, List.getElem?_map] using congrArg (Option.map transform) read

/-- Pay retains class order and adds the source root-size unit. -/
theorem pay_correct (index : ValueIndex Value) (classes : Nat → List Value)
    (correct : Correct index classes) :
    Correct (payIndex index) (fun size => match size with | 0 => [] | size + 1 => classes size) := by
  constructor
  · intro size
    cases size with
    | zero => rfl
    | succ size => exact correct.counts size
  · intro position bounded
    cases sizeEq : position.size with
    | zero => simp [payIndex, sizeEq] at bounded
    | succ size =>
        have inner : position.rank < index.counts size := by
          simpa only [payIndex, sizeEq] using bounded
        simpa only [payIndex, sizeEq, Nat.add_sub_cancel] using
          correct.select ⟨size, position.rank⟩ inner

/-- A counted scale read has a divisible size and a valid child rank. -/
theorem scale_read_bound (factor : Nat) (index : ValueIndex Value) (position : Position)
    (bounded : position.rank < (scaleIndex factor index).counts position.size) :
    position.size % factor = 0 ∧ position.rank < index.counts (position.size / factor) := by
  by_cases one : factor = 1
  · subst factor
    exact ⟨Nat.mod_one _, by simpa only [scaleIndex, ite_true, Nat.div_one] using bounded⟩
  · by_cases divisible : position.size % factor = 0
    · exact ⟨divisible, by simpa only [scaleIndex, one, ↓reduceIte, divisible] using bounded⟩
    · simp [scaleIndex, one, divisible] at bounded

/-- Positive source scaling has the same class order at every counted position. -/
theorem scale_correct (factor : Nat) (_positive : 0 < factor)
    (index : ValueIndex Value) (classes : Nat → List Value) (correct : Correct index classes) :
    Correct (scaleIndex factor index) (scaled factor classes) := by
  constructor
  · intro size
    by_cases one : factor = 1
    · simpa only [scaleIndex, scaled, one, ite_true] using correct.counts size
    · by_cases divisible : size % factor = 0
      · simpa only [scaleIndex, scaled, one, ↓reduceIte, divisible] using
          correct.counts (size / factor)
      · simp [scaleIndex, scaled, one, divisible]
  · intro position bounded
    obtain ⟨divisible, childBound⟩ := scale_read_bound factor index position bounded
    by_cases one : factor = 1
    · subst factor
      simpa only [scaleIndex, scaled, ite_true] using correct.select position bounded
    · simpa only [scaleIndex, scaled, one, ↓reduceIte, divisible] using
        correct.select ⟨position.size / factor, position.rank⟩ childBound

/-- The empty index has the independent empty class at every size. -/
theorem empty_correct : Correct (emptyIndex : ValueIndex Value) (fun _ => []) := by
  constructor
  · intro size; rfl
  · intro position bounded; cases bounded

/-- The independent product order uses ascending prefix size and left-major pairs. -/
def productClass (combine : Left → Right → Result)
    (left : Nat → List Left) (right : Nat → List Right) (size : Nat) : List Result :=
  (List.range (size + 1)).flatMap fun split =>
    (left split).flatMap fun first => (right (size - split)).map (combine first)

private theorem product_replay (combine : Left → Right → Result)
    (left : Nat → List Left) (right : Nat → List Right)
    (first second : Position) (before : Left) (after : Right)
    (leftFound : (left first.size)[first.rank]? = some before)
    (rightFound : (right second.size)[second.rank]? = some after) :
    (productClass combine left right (first.size + second.size))[
      (productPosition (fun size => (left size).length)
        (fun size => (right size).length) first second).rank]? = some (combine before after) := by
  have replay := SizedRank.productPosition_replay
    (fun size => (left size).map fun first second => combine first second) right first second
    (by simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp leftFound).1)
    (List.getElem?_eq_some_iff.mp rightFound).1
  simpa only [List.length_map, productClass, Decoder.applyValues, List.flatMap_map,
    List.getElem?_map, leftFound, rightFound, Option.map_some, Option.bind_some] using replay

/-- The direct source product count and split selector agree with independent classes. -/
theorem product_correct (combine : Left → Right → Result)
    (left : ValueIndex Left) (right : ValueIndex Right)
    (leftClasses : Nat → List Left) (rightClasses : Nat → List Right)
    (leftCorrect : Correct left leftClasses) (rightCorrect : Correct right rightClasses) :
    Correct (productIndex combine left right) (productClass combine leftClasses rightClasses) := by
  constructor
  · intro size
    simp [productIndex, convolve, productClass, List.length_flatMap, List.map_const',
      List.sum_replicate_nat, leftCorrect.counts, rightCorrect.counts]
  · intro position bounded
    obtain ⟨first, second, combined, firstBound, secondBound⟩ :=
      RecursiveCallbackTables.product_split left.counts right.counts position bounded
    have leftWithin : first.rank < (leftClasses first.size).length := by
      rw [← leftCorrect.counts]; exact firstBound
    have rightWithin : second.rank < (rightClasses second.size).length := by
      rw [← rightCorrect.counts]; exact secondBound
    let before := (leftClasses first.size)[first.rank]
    let after := (rightClasses second.size)[second.rank]
    have leftFound : (leftClasses first.size)[first.rank]? = some before :=
      List.getElem?_eq_getElem leftWithin
    have rightFound : (rightClasses second.size)[second.rank]? = some after :=
      List.getElem?_eq_getElem rightWithin
    have replay := product_replay combine leftClasses rightClasses first second before after leftFound rightFound
    have leftCounts : (fun size => (leftClasses size).length) = left.counts :=
      funext (fun size => (leftCorrect.counts size).symm)
    have rightCounts : (fun size => (rightClasses size).length) = right.counts :=
      funext (fun size => (rightCorrect.counts size).symm)
    have sizeEq : first.size + second.size = position.size := congrArg Position.size combined
    simp only [leftCounts, rightCounts, combined, sizeEq] at replay
    rw [replay, ← combined]
    have firstRead := (leftCorrect.select first firstBound).trans leftFound
    have secondRead := (rightCorrect.select second secondBound).trans rightFound
    simp [productIndex, productSplit_productPosition _ _ _ _ firstBound secondBound,
      firstRead, secondRead]

/-- A valid product position reads only counted positions of its operands. -/
theorem product_read_bounds (left : ValueIndex Left) (right : ValueIndex Right) (position : Position)
    (bounded : position.rank < convolve left.counts right.counts position.size) :
    ∃ first second, productSplit left.counts right.counts position = some (first, second) ∧
      first.rank < left.counts first.size ∧ second.rank < right.counts second.size := by
  obtain ⟨first, second, combined, firstBound, secondBound⟩ :=
    RecursiveCallbackTables.product_split left.counts right.counts position bounded
  refine ⟨first, second, ?_, firstBound, secondBound⟩
  rw [← combined]
  exact productSplit_productPosition _ _ _ _ firstBound secondBound

/-- Choice preserves row occurrence order and all duplicate occurrences. -/
theorem choice_correct (items : List Key) (indexes : Key → ValueIndex Value)
    (classes : Key → Nat → List Value)
    (correct : ∀ item ∈ items, Correct (indexes item) (classes item)) :
    Correct (choiceIndex (items.map indexes))
      (fun size => items.flatMap fun item => classes item size) := by
  induction items with
  | nil => exact empty_correct
  | cons first rest ih =>
      have head := correct first (by simp)
      have tail := ih (fun item member => correct item (by simp [member]))
      constructor
      · intro size
        change (indexes first).counts size + (choiceIndex (rest.map indexes)).counts size =
          (classes first size ++ rest.flatMap (fun item => classes item size)).length
        rw [List.length_append, head.counts, tail.counts]
      · intro position bounded
        by_cases here : position.rank < (indexes first).counts position.size
        · have before : position.rank < (classes first position.size).length := by
            rw [← head.counts]; exact here
          simpa only [choiceIndex, List.map_cons, selectChoice, here, ite_true,
            List.flatMap_cons, List.getElem?_append_left before] using head.select position here
        · have after : (classes first position.size).length ≤ position.rank := by
            rw [← head.counts]; omega
          have tailBound : position.rank - (indexes first).counts position.size <
              (choiceIndex (rest.map indexes)).counts position.size := by
            change position.rank < (indexes first).counts position.size +
              (choiceIndex (rest.map indexes)).counts position.size at bounded
            omega
          simpa only [choiceIndex, List.map_cons, selectChoice, here, ite_false,
            List.flatMap_cons, List.getElem?_append_right after, ← head.counts] using
              tail.select ⟨position.size, position.rank - (indexes first).counts position.size⟩ tailBound

/-- Source prepend maps a partial constructor before the child product. -/
def prepend (build : List (Term Symbol) → Result) (term : Term Symbol)
    (arguments : List (Term Symbol)) : Result := build (term :: arguments)

/-- This is the literal map-prepend and application product in consumeChild. -/
def consumeChild (built : ValueIndex (List (Term Symbol) → Result))
    (child : ValueIndex (Term Symbol)) : ValueIndex (List (Term Symbol) → Result) :=
  productIndex (fun function value => function value) (mapIndex prepend built) child

/-- A selected prefix retains the remaining constructor arguments as a function. -/
def partialBuild (build : List (Term Symbol) → Result) (before : List (Term Symbol)) :
    List (Term Symbol) → Result := fun after => build (before ++ after)

private theorem consume_classes (build : List (Term Symbol) → Result)
    (prefixes : Nat → List (List (Term Symbol))) (children : Nat → List (Term Symbol))
    (size : Nat) :
    productClass (fun function value => function value)
      (fun size => ((prefixes size).map (partialBuild build)).map prepend) children size =
      (extendForests prefixes children size).map (partialBuild build) := by
  simp only [productClass, extendForests, List.map_flatMap, List.flatMap_map, List.map_map]
  congr 1
  funext split
  congr 1
  funext before
  congr 1
  funext child
  funext after
  simp only [Function.comp_def, prepend, partialBuild, List.append_assoc, List.singleton_append]

/-- The literal function-valued child step realizes the prefix class extension. -/
theorem consume_correct (build : List (Term Symbol) → Result)
    (built : ValueIndex (List (Term Symbol) → Result)) (child : ValueIndex (Term Symbol))
    (prefixes : Nat → List (List (Term Symbol))) (children : Nat → List (Term Symbol))
    (builtCorrect : Correct built (fun size => (prefixes size).map (partialBuild build)))
    (childCorrect : Correct child children) :
    Correct (consumeChild built child)
      (fun size => (extendForests prefixes children size).map (partialBuild build)) := by
  exact (product_correct (fun function value => function value) _ _ _ _
    (map_correct prepend built _ builtCorrect) childCorrect).congr (consume_classes build prefixes children)

private theorem seed_correct (build : List (Term Symbol) → Result) :
    Correct (payIndex (constantIndex build)) (fun size => (seed size).map (partialBuild build)) := by
  apply (pay_correct _ _ (constant_correct build)).congr
  intro size
  cases size with
  | zero => rfl
  | succ size =>
      cases size with
      | zero =>
          change [build] = [partialBuild build []]
          apply congrArg (fun function => [function])
          funext arguments
          rfl
      | succ size => simp [seed]

/-- Build a source row by its actual paid function seed and left child fold. -/
def foldedIndex (build : List (Term Symbol) → Result) (indexes : Key → ValueIndex (Term Symbol))
    (children : List Key) : ValueIndex (List (Term Symbol) → Result) :=
  children.foldl (fun built child => consumeChild built (indexes child)) (payIndex (constantIndex build))

/-- Every source prefix retains exactly the independently computed function class. -/
theorem folded_correct (build : List (Term Symbol) → Result) (indexes : Key → ValueIndex (Term Symbol))
    (classes : Key → Nat → List (Term Symbol)) (correct : ∀ key, Correct (indexes key) (classes key))
    (children : List Key) :
    Correct (foldedIndex build indexes children)
      (fun size => ((children.foldl (fun built child => extendForests built (classes child)) seed) size).map
        (partialBuild build)) := by
  induction children using RecursiveSize.snoc_induction with
  | empty => exact seed_correct build
  | step children last ih =>
      simpa only [foldedIndex, List.foldl_append, List.foldl_cons, List.foldl_nil] using
        consume_correct build _ _ _ _ ih (correct last)

/-- The source transition index applies its final constructor function to []. -/
def builtIndex (build : List (Term Symbol) → Result) (indexes : Key → ValueIndex (Term Symbol))
    (children : List Key) : ValueIndex Result :=
  mapIndex (fun function => function []) (foldedIndex build indexes children)

/-- The final source map preserves all prefix-product counts and selected positions. -/
theorem built_correct (build : List (Term Symbol) → Result) (indexes : Key → ValueIndex (Term Symbol))
    (classes : Key → Nat → List (Term Symbol)) (correct : ∀ key, Correct (indexes key) (classes key))
    (children : List Key) :
    Correct (builtIndex build indexes children)
      (fun size => ((children.foldl (fun built child => extendForests built (classes child)) seed) size).map build) := by
  apply (map_correct (fun function => function []) _ _
    (folded_correct build indexes classes correct children)).congr
  intro size
  simp only [List.map_map, Function.comp_def, partialBuild, List.append_nil]

/-- The source group reads its first child and scales by the group length. -/
def groupIndex (indexes : State → ValueIndex (Term Symbol)) (children : List State)
    (positions : List Nat) : ValueIndex (Term Symbol) :=
  match positions with
  | [] => emptyIndex
  | first :: _ =>
      match children[first]? with
      | none => emptyIndex
      | some state => scaleIndex positions.length (indexes state)

/-- Each concrete group field agrees with its checked ordered group class. -/
theorem group_correct (indexes : State → ValueIndex (Term Symbol))
    (classes : State → Nat → List (Term Symbol)) (correct : ∀ state, Correct (indexes state) (classes state))
    (children : List State) (positions : List Nat) :
    Correct (groupIndex indexes children positions) (groupClass classes children positions) := by
  change Correct (groupIndex indexes children positions) (fun size => groupClass classes children positions size)
  cases positions with
  | nil => exact empty_correct
  | cons first rest =>
      cases read : children[first]? with
      | none => simpa only [groupIndex, groupClass, read] using (empty_correct (Value := Term Symbol))
      | some state =>
          simpa only [groupIndex, groupClass, read] using
            scale_correct (first :: rest).length (by simp) (indexes state) (classes state) (correct state)

/-- Successful class parsing makes every source representative read valid. -/
theorem group_read_valid (children : List State) (classes : List (List Nat))
    (valid : CompactGroups.ValidClasses children.length classes) (group : List Nat)
    (member : group ∈ CompactGroups.childGroups children.length classes) :
    ∃ first rest state, group = first :: rest ∧ children[first]? = some state ∧ 0 < group.length := by
  have nonempty := CompactGroups.childGroups_nonempty children.length classes valid group member
  cases group with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      have within : first < children.length := List.mem_range.mp
        ((CompactGroups.childGroups_positions children.length classes).mem_iff.mp
          (List.mem_flatten.mpr ⟨first :: rest, member, by simp⟩))
      exact ⟨first, rest, children[first], rfl, List.getElem?_eq_getElem within, by simp⟩

/-- This is the literal transition fold of the nonempty-annotation source branch. -/
def groupedIndex (indexes : State → ValueIndex (Term Symbol))
    (row : Row State Symbol (List (List Nat))) : ValueIndex (Term Symbol) :=
  let groups := CompactGroups.childGroups row.children.length row.constraint
  builtIndex (assemble row.label row.children.length groups) (groupIndex indexes row.children) groups

/-- Source grouped count and direct selection have exactly the checked rowClass order. -/
theorem grouped_correct (indexes : State → ValueIndex (Term Symbol))
    (classes : State → Nat → List (Term Symbol)) (correct : ∀ state, Correct (indexes state) (classes state))
    (row : Row State Symbol (List (List Nat))) :
    Correct (groupedIndex indexes row) (rowClass classes row.label row.children row.constraint) := by
  exact built_correct _ _ _ (group_correct indexes classes correct row.children) _

/-- The source [] annotation branch folds the original child states directly. -/
def plainIndex (indexes : State → ValueIndex (Term Symbol))
    (row : Row State Symbol (List (List Nat))) : ValueIndex (Term Symbol) :=
  builtIndex (Term.node row.label) indexes row.children

/-- Preserve the literal source choice between ordinary and grouped row folds. -/
def rowIndex (indexes : State → ValueIndex (Term Symbol))
    (row : Row State Symbol (List (List Nat))) : ValueIndex (Term Symbol) :=
  if row.constraint = [] then plainIndex indexes row else groupedIndex indexes row

/-- Independent classes retain the source empty-annotation shortcut explicitly. -/
def sourceRowClass (classes : State → Nat → List (Term Symbol))
    (row : Row State Symbol (List (List Nat))) (size : Nat) : List (Term Symbol) :=
  if row.constraint = [] then
    ((row.children.foldl (fun built child => extendForests built (classes child)) seed) size).map
      (Term.node row.label)
  else rowClass classes row.label row.children row.constraint size

/-- Both literal source branches have exact compositional count and selector fields. -/
theorem row_correct (indexes : State → ValueIndex (Term Symbol))
    (classes : State → Nat → List (Term Symbol)) (correct : ∀ state, Correct (indexes state) (classes state))
    (row : Row State Symbol (List (List Nat))) :
    Correct (rowIndex indexes row) (sourceRowClass classes row) := by
  change Correct (rowIndex indexes row) (fun size => sourceRowClass classes row size)
  by_cases plain : row.constraint = []
  · simpa only [rowIndex, sourceRowClass, plain, ite_true, plainIndex] using
      built_correct (Term.node row.label) indexes classes correct row.children
  · simpa only [rowIndex, sourceRowClass, plain, ite_false] using grouped_correct indexes classes correct row

/-- The source state body chooses the actual rows in their stored order. -/
def stateIndex (indexes : State → ValueIndex (Term Symbol))
    (rows : List (Row State Symbol (List (List Nat)))) : ValueIndex (Term Symbol) :=
  choiceIndex (rows.map (rowIndex indexes))

/-- The complete source state body preserves row order and multiplicity. -/
theorem state_correct (indexes : State → ValueIndex (Term Symbol))
    (classes : State → Nat → List (Term Symbol)) (correct : ∀ state, Correct (indexes state) (classes state))
    (rows : List (Row State Symbol (List (List Nat)))) :
    Correct (stateIndex indexes rows) (fun size => rows.flatMap fun row => sourceRowClass classes row size) :=
  choice_correct rows (rowIndex indexes) (sourceRowClass classes) (fun row _ => row_correct indexes classes correct row)

/-- A nonempty annotation selects the checked grouped row class in the literal source body. -/
theorem constrained_row_correct (indexes : State → ValueIndex (Term Symbol))
    (classes : State → Nat → List (Term Symbol)) (correct : ∀ state, Correct (indexes state) (classes state))
    (row : Row State Symbol (List (List Nat))) (nonempty : row.constraint ≠ []) :
    Correct (rowIndex indexes row) (rowClass classes row.label row.children row.constraint) := by
  simpa only [rowIndex, nonempty, ite_false] using grouped_correct indexes classes correct row

end MicroCFTA.SourceSizedGroupedIndex
