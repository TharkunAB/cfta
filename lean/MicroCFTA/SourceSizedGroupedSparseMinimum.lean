import MicroCFTA.SourceSizedGroupedSparseFields
import MicroCFTA.SourceSizedGroupedMinimumIndex

/-!
# The shared global minimum on finite sparse unfoldings

`withKnotMetadata` follows the count/minimum projection of
`Ranked/Internal/Size.hs:666-677`. It leaves the count list unchanged. It does
not insert a `fromMinimum` seed. The actual pay and product operations insert
their seeds separately.

Every finite class unfolding is an ordered sublist of the complete class.
The actual prepared minimum therefore bounds every finite count field. The
finite storage evaluator can retain that same global minimum at each level.
No caller supplies a lower-bound certificate.

These results concern finite observations. They do not establish lazy knot
productivity, flag computation, sharing, machine conversions, or native cost.
-/
namespace MicroCFTA.SourceSizedGroupedSparseMinimum

open Language RecursiveSize SourceSizedDecided SourceSizedFiniteKeys
open SourceSizedGroupedChainOrder
open SourceSizedGroupedSparseFields (Stored Represents MinimumBound)

variable {State Symbol Key Value Formula : Type}

private theorem flatMap_mono {A B : Type} (first second : A → List B)
    {before after : List A} (included : before.Sublist after)
    (blocks : ∀ item, (first item).Sublist (second item)) :
    (before.flatMap first).Sublist (after.flatMap second) := by
  induction after generalizing before with
  | nil => cases included; exact .slnil
  | cons item rest ih =>
    cases included with
    | cons _ tail =>
      exact (ih tail).trans (List.sublist_append_right (second item) (rest.flatMap second))
    | cons_cons _ tail => exact (blocks item).append (ih tail)

private theorem extend_mono (first second : Nat → List (List (Term Symbol)))
    (left right : Nat → List (Term Symbol))
    (prefixes : ∀ size, (first size).Sublist (second size))
    (children : ∀ size, (left size).Sublist (right size)) (size : Nat) :
    (extendForests first left size).Sublist (extendForests second right size) := by
  unfold extendForests
  apply flatMap_mono _ _ (.refl _)
  intro prefixSize
  apply flatMap_mono _ _ (prefixes prefixSize)
  intro built
  exact List.Sublist.map (fun child => built ++ [child]) (children (size - prefixSize))

private theorem scaled_mono (first second : Nat → List (Term Symbol))
    (included : ∀ size, (first size).Sublist (second size)) (factor size : Nat) :
    (scaled factor first size).Sublist (scaled factor second size) := by
  unfold scaled
  split
  · exact included size
  · split
    · exact included _
    · exact .refl _

private theorem group_mono (first second : State → Nat → List (Term Symbol))
    (included : ∀ state size, (first state size).Sublist (second state size))
    (children : List State) (positions : List Nat) (size : Nat) :
    (groupClass first children positions size).Sublist
      (groupClass second children positions size) := by
  cases positions with
  | nil => exact .refl _
  | cons position rest =>
    cases selected : children[position]? with
    | none => simp only [groupClass, selected]; exact .refl _
    | some state =>
      simpa only [groupClass, selected] using
        scaled_mono (first state) (second state) (included state) (position :: rest).length size

private theorem fold_mono (groups : List Key)
    (first second : Key → Nat → List (Term Symbol))
    (included : ∀ key size, (first key size).Sublist (second key size))
    (before after : Nat → List (List (Term Symbol)))
    (initial : ∀ size, (before size).Sublist (after size)) :
    ∀ size,
      ((groups.foldl (fun built key => extendForests built (first key)) before) size).Sublist
        ((groups.foldl (fun built key => extendForests built (second key)) after) size) := by
  induction groups generalizing before after with
  | nil => exact initial
  | cons firstKey rest ih =>
    exact ih (extendForests before (first firstKey)) (extendForests after (second firstKey))
      (extend_mono before after (first firstKey) (second firstKey) initial (included firstKey))

/-- Source row products preserve pointwise sublists, including multiplicity and order. -/
theorem rowClass_mono (first second : State → Nat → List (Term Symbol))
    (included : ∀ state size, (first state size).Sublist (second state size))
    (symbol : Symbol) (children : List State) (classes : List (List Nat)) (size : Nat) :
    (rowClass first symbol children classes size).Sublist
      (rowClass second symbol children classes size) := by
  unfold rowClass
  dsimp only
  apply List.Sublist.map
  exact fold_mono (CompactGroups.childGroups children.length classes)
    (groupClass first children) (groupClass second children)
    (group_mono first second included children) seed seed (fun _ => .refl _) size

/-- The actual ordered row choice preserves each callback sublist. -/
theorem classOf_mono (first second : State → Nat → List (Term Symbol))
    (included : ∀ state size, (first state size).Sublist (second state size))
    (rows : List (Row State Symbol (List (List Nat)))) (size : Nat) :
    (SourceSizedGroupedClasses.classOf first rows size).Sublist
      (SourceSizedGroupedClasses.classOf second rows size) := by
  unfold SourceSizedGroupedClasses.classOf
  exact flatMap_mono _ _ (.refl rows)
    (fun row => rowClass_mono first second included row.label row.children row.constraint size)

private theorem classOf_zero (classes : State → Nat → List (Term Symbol))
    (rows : List (Row State Symbol (List (List Nat)))) :
    SourceSizedGroupedClasses.classOf classes rows 0 = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro row _
  exact SourceSizedGroupedRecurrence.rowClass_zero classes row.label row.children row.constraint

/-- Every finite gated unfolding is a sublist of the complete source class. -/
theorem unrolled_sublist (fuel : Nat) (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat)))) (size : Nat) (state : State) :
    (SourceSizedGroupedTableIndex.unrolled fuel known rows state size).Sublist
      (SourceSizedGroupedClasses.classes rows size state) := by
  induction fuel generalizing size state with
  | zero => exact List.nil_sublist _
  | succ fuel ih =>
    cases present : known state with
    | false =>
      simpa only [SourceSizedGroupedTableIndex.unrolled, present, Bool.false_eq_true, ite_false] using
        List.nil_sublist (SourceSizedGroupedClasses.classes rows size state)
    | true =>
      cases size with
      | zero =>
        simp only [SourceSizedGroupedTableIndex.unrolled, present, ite_true, classOf_zero,
          SourceSizedGroupedClasses.classes_zero]
        exact .refl _
      | succ remaining =>
        rw [SourceSizedGroupedRecurrence.classes_succ]
        simp only [SourceSizedGroupedTableIndex.unrolled, present, ite_true]
        exact classOf_mono _ _ (fun child childSize => ih childSize child) _ _

/-- Truncation cannot introduce extra terms or duplicate existing occurrences. -/
theorem evaluate_count_le (fuel : Nat) (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat)))) (size : Nat) (state : State) :
    (SourceSizedGroupedTableIndex.evaluate fuel known rows state).counts size ≤
      (SourceSizedGroupedClasses.classes rows size state).length := by
  rw [(SourceSizedGroupedTableIndex.evaluate_correct fuel known rows state).counts]
  exact (unrolled_sublist fuel known rows size state).length_le

/-- The source override keeps counts and changes only their minimum metadata. -/
def withKnotMetadata (minimum : Option Nat) (stored : Stored) : Stored :=
  ⟨stored.series, minimum⟩

/-- The count list is literally unchanged by the source metadata override. -/
theorem withKnotMetadata_series (minimum : Option Nat) (stored : Stored) :
    (withKnotMetadata minimum stored).series = stored.series := rfl

private theorem override_represents (minimum : Option Nat) (stored : Stored)
    (index : RecursiveJoinFields.ValueIndex Value) (represented : Represents stored index)
    (bounded : MinimumBound minimum index.counts) :
    Represents (withKnotMetadata minimum stored) index :=
  ⟨represented.ordered, represented.counts, bounded⟩

/-- All finite levels use the same supplied minimum map, with literal metadata overrides. -/
def evaluate : Nat → (State → Option Nat) →
    (State → List (Row State Symbol (List (List Nat)))) → State → Stored
  | 0, minimum, _, state => withKnotMetadata (minimum state) SourceSizedGroupedSparseFields.empty
  | fuel + 1, minimum, rows, state =>
      withKnotMetadata (minimum state)
        (if (minimum state).isSome then
          SourceSizedGroupedSparseFields.stateStorage (evaluate fuel minimum rows) (rows state)
        else SourceSizedGroupedSparseFields.empty)

section Prepared

variable [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol] [Ord Symbol]

/-- The actual prepared global minimum bounds every finite independent count field. -/
theorem minimum_bound (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (fuel : Nat) (key : List State) :
    MinimumBound (SourceSizedGroupedMinimumIndex.minimum original root output success key)
      (SourceSizedGroupedTableIndex.evaluate fuel
        (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output) key).counts := by
  cases found : SourceSizedGroupedMinimumIndex.minimum original root output success key with
  | none =>
    intro size
    have empty := (SourceSizedGroupedMinimumIndex.minimum_none_iff original root output success key).mp found size
    have bounded := evaluate_count_le fuel
      (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output) size key
    rw [empty, List.length_nil] at bounded
    omega
  | some least =>
    intro size below
    have empty : SourceSizedGroupedClasses.classes (lookup output) size key = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro term member
      have ordered := (SourceSizedGroupedMinimumIndex.minimum_is_least
        original root output success key least found).2 size term member
      omega
    have bounded := evaluate_count_le fuel
      (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output) size key
    rw [empty, List.length_nil] at bounded
    omega

/-- Existing finite storage can carry the actual global minimum without changing counts. -/
theorem finite_override_represents
    (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (fuel : Nat) (key : List State) :
    Represents
      (withKnotMetadata (SourceSizedGroupedMinimumIndex.minimum original root output success key)
        (SourceSizedGroupedSparseFields.evaluate fuel
          (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output) key))
      (SourceSizedGroupedTableIndex.evaluate fuel
        (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output) key) :=
  override_represents _ _ _ (SourceSizedGroupedSparseFields.evaluate_represents _ _ _ _)
    (minimum_bound original root output success fuel key)

/-- Globally fixed metadata remain valid through every actual finite sparse body. -/
theorem evaluate_represents
    (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (fuel : Nat) (key : List State) :
    Represents
      (evaluate fuel (SourceSizedGroupedMinimumIndex.minimum original root output success)
        (lookup output) key)
      (SourceSizedGroupedTableIndex.evaluate fuel
        (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output) key) := by
  induction fuel generalizing key with
  | zero =>
    exact override_represents _ _ _ SourceSizedGroupedSparseFields.empty_represents
      (minimum_bound original root output success 0 key)
  | succ fuel ih =>
    change Represents
      (withKnotMetadata (SourceSizedGroupedMinimumIndex.minimum original root output success key)
        (if SourceSizedGroupedMinimumIndex.known original root output success key then
          SourceSizedGroupedSparseFields.stateStorage
            (evaluate fuel (SourceSizedGroupedMinimumIndex.minimum original root output success)
              (lookup output)) (lookup output key)
        else SourceSizedGroupedSparseFields.empty))
      (SourceSizedGroupedTableIndex.evaluate (fuel + 1)
        (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output) key)
    refine override_represents _ _ _ ?_ (minimum_bound original root output success (fuel + 1) key)
    cases present : SourceSizedGroupedMinimumIndex.known original root output success key with
    | false =>
      simpa only [SourceSizedGroupedTableIndex.evaluate, present, Bool.false_eq_true, ite_false] using
        (SourceSizedGroupedSparseFields.empty_represents (Value := Term Symbol))
    | true =>
      simpa only [SourceSizedGroupedTableIndex.evaluate, present, ite_true] using
        SourceSizedGroupedSparseFields.state_represents
          (evaluate fuel (SourceSizedGroupedMinimumIndex.minimum original root output success) (lookup output))
          (SourceSizedGroupedTableIndex.evaluate fuel
            (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output))
          ih (lookup output key)

/-- Count lookup uses the actual prepared minimum map at every unfolding level. -/
theorem evaluate_lookup
    (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (fuel size : Nat) (key : List State) :
    Sparse.valueAtSize
      (evaluate fuel (SourceSizedGroupedMinimumIndex.minimum original root output success)
        (lookup output) key).series size =
      (SourceSizedGroupedTableIndex.evaluate fuel
        (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output) key).counts size :=
  (evaluate_represents original root output success fuel key).lookup size

/-- A request-derived finite observation has the exact grouped class count. -/
theorem requested_classes
    (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
    (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (size : Nat) (key : List State) :
    Sparse.valueAtSize
      (evaluate (size + 1) (SourceSizedGroupedMinimumIndex.minimum original root output success)
        (lookup output) key).series size =
      (SourceSizedGroupedClasses.classes (lookup output) size key).length := by
  rw [evaluate_lookup]
  exact SourceSizedGroupedTableIndex.evaluate_count (size + 1)
    (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output)
    (SourceSizedGroupedMinimumIndex.known_false_empty original root output success) size key (Nat.le_refl _)

end Prepared
end MicroCFTA.SourceSizedGroupedSparseMinimum
