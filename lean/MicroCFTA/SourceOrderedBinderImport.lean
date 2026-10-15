import MicroCFTA.SourceOrderedBinderRank

/-!
# The ordered binder schedule of source graph import

`Data.CFTA.Interned.fromRows` first computes finite positional rows and SCC
labels. This module starts with those completed values. It records ordered
child dispatch and the completed memo schedule. It does not prove SCC
extraction, constructor semantics, or GHC evaluation correspondence.
-/
namespace MicroCFTA.SourceOrderedBinderImport

/-- Enclosing binders in increasing source position order. -/
abbrev Bound := List Nat

/-- The source memo key contains the full binder context and current position. -/
abbrev Key := Bound × Nat

/-- Enclosing binders are distinct and occur before the current position. -/
def Ordered (bound : Bound) (here : Nat) : Prop :=
  bound.Pairwise (· < ·) ∧ ∀ index ∈ bound, index < here

/-- The body also binds the current state. -/
def bodyBound (bound : Bound) (here : Nat) : Bound := bound ++ [here]

/-- A child is a bound reference or a recursive build request. -/
inductive Choice where
  | reference (index : Nat)
  | build (bound : Bound) (here : Nat)
deriving DecidableEq

/-- Match the source component check, bound check, and strict-prefix split. -/
def select (component : Nat → Nat) (bound : Bound) (here next : Nat) : Choice :=
  if component next ≠ component here then .build [] next
  else if next ∈ bodyBound bound here then .reference next
  else .build ((bodyBound bound here).filter (fun index => decide (index < next))) next

/-- A different component resets the context before the bound test. -/
theorem select_external (different : component next ≠ component here) :
    select component bound here next = .build [] next := by
  simp [select, different]

/-- A bound child of the current component is a reference. -/
theorem select_reference (same : component next = component here)
    (present : next ∈ bodyBound bound here) :
    select component bound here next = .reference next := by
  simp [select, same, present]

/-- An unbound child keeps exactly the binders with smaller positions. -/
theorem select_recursive (same : component next = component here)
    (absent : next ∉ bodyBound bound here) :
    select component bound here next =
      .build ((bodyBound bound here).filter (fun index => decide (index < next))) next := by
  simp [select, same, absent]

/-- A direct self edge is a reference without a recursive build. -/
theorem select_self (component : Nat → Nat) (bound : Bound) (here : Nat) :
    select component bound here here = .reference here := by
  simp [select, bodyBound]

/-- Adding the current position preserves strict increasing order. -/
theorem bodyBound_pairwise (ordered : Ordered bound here) :
    (bodyBound bound here).Pairwise (· < ·) := by
  simpa only [bodyBound, List.pairwise_append, List.pairwise_singleton,
    List.mem_singleton, forall_eq, true_and, Ordered] using ordered

/-- Every selected build context remains ordered below its child. -/
theorem select_build_ordered (ordered : Ordered bound here)
    (chosen : select component bound here next = .build childBound childHere) :
    childHere = next ∧ Ordered childBound childHere := by
  unfold select at chosen
  split at chosen
  · cases chosen
    exact ⟨rfl, by simp [Ordered]⟩
  · split at chosen
    · cases chosen
    · cases chosen
      exact ⟨rfl, (bodyBound_pairwise ordered).filter _,
        fun index present => by simpa using (List.mem_filter.mp present).2⟩

/-- Context membership agrees with the bit-vector rank representation. -/
theorem bodyBound_mem (bound : Bound) (here index : Nat) :
    index ∈ bodyBound bound here ↔ index ∈ here :: bound := by
  simp [bodyBound, or_comm]

/-- Actual same-component recursive dispatch strictly decreases the finite rank. -/
theorem select_rank_decreases (width : Nat) (bounded : next < width)
    (absent : next ∉ bodyBound bound here) :
    SourceOrderedBinderRank.rank width
        ((bodyBound bound here).filter (fun index => decide (index < next))) next <
      SourceOrderedBinderRank.rank width bound here := by
  exact SourceOrderedBinderRank.child_decreases_append width bound here next bounded absent

/-- Enumerate the order-preserving subsets of a finite position list. -/
def subsets : List Nat → List Bound
  | [] => [[]]
  | head :: tail => subsets tail ++ (subsets tail).map (head :: ·)

/-- The explicit subset inventory has one slot per binary choice. -/
theorem subsets_length (items : List Nat) : (subsets items).length = 2 ^ items.length := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp [subsets, ih, Nat.pow_succ, Nat.mul_two]

/-- A filtered position list occurs in the explicit subset inventory. -/
theorem filter_mem_subsets (items : List Nat) (keep : Nat → Bool) :
    items.filter keep ∈ subsets items := by
  induction items with
  | nil => simp [subsets]
  | cons head tail ih => cases selected : keep head <;> simp [subsets, selected, ih]

/-- All memo keys for states below the finite positional width. -/
def keys : Nat → List Key
  | 0 => []
  | width + 1 => keys width ++ (subsets (List.range width)).map (fun bound => (bound, width))

/-- The finite key inventory has exactly one slot for each ordered context. -/
theorem keys_length (width : Nat) : (keys width).length + 1 = 2 ^ width := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [keys, List.length_append, List.length_map,
      subsets_length, List.length_range, Nat.pow_succ]; omega

/-- Ordered contexts are the literal filtered position list. -/
theorem ordered_filter (ordered : Ordered bound here) :
    (List.range here).filter (fun index => decide (index ∈ bound)) = bound := by
  have distinct : bound.Nodup := ordered.1.imp Nat.ne_of_lt
  have selected := (List.pairwise_lt_range (n := here)).filter (fun index => decide (index ∈ bound))
  apply List.Perm.eq_of_pairwise (le := (· < ·))
    (fun _ _ _ _ forward backward => by omega) selected ordered.1
  apply (List.perm_ext_iff_of_nodup (selected.imp Nat.ne_of_lt) distinct).mpr
  intro index
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨And.right, fun present => ⟨ordered.2 index present, present⟩⟩

/-- Every valid finite build key occurs in the explicit inventory. -/
theorem key_mem (ordered : Ordered bound here) (bounded : here < width) :
    (bound, here) ∈ keys width := by
  induction width with
  | zero => omega
  | succ width ih =>
      by_cases last : here = width
      · subst here
        apply List.mem_append.mpr
        right
        apply List.mem_map.mpr
        refine ⟨bound, ?_, rfl⟩
        rw [← ordered_filter ordered]
        exact filter_mem_subsets _ _
      · exact List.mem_append.mpr (.inl (ih (by omega)))

/-- An imported transition keeps its symbol, constraint, and child order. -/
structure Row (Symbol Constraint Child : Type) where
  symbol : Symbol
  constraint : Constraint
  children : List Child

/-- The actual constructor operations are parameters of this schedule model. -/
structure Operations (Symbol Constraint Node : Type) where
  reference : Nat → Node
  assemble : List (Row Symbol Constraint Node) → Node
  refers : Node → Nat → Bool
  bind : Nat → Node → Node

/-- Add a binder exactly when the completed body refers to its state. -/
def finish (operations : Operations Symbol Constraint Node) (here : Nat) (body : Node) : Node :=
  if operations.refers body here then operations.bind here body else body

mutual
  /-- A completed build performs lookup before the body and insertion after it. -/
  inductive Build (source : Nat → List (Row Symbol Constraint Nat))
      (component : Nat → Nat) (operations : Operations Symbol Constraint Node) :
      Key → Cache.Table Key Node → Node → Cache.Table Key Node → Prop where
    | hit (present : before key = some value) :
        Build source component operations key before value before
    | miss (absent : before (bound, here) = none)
        (body : Rows source component operations bound here (source here) before copied middle) :
        Build source component operations (bound, here) before
          (finish operations here (operations.assemble copied))
          (Cache.put middle (bound, here) (finish operations here (operations.assemble copied)))

  /-- Children execute from left to right, with the source dispatch at each child. -/
  inductive Children (source : Nat → List (Row Symbol Constraint Nat))
      (component : Nat → Nat) (operations : Operations Symbol Constraint Node) :
      Bound → Nat → List Nat → Cache.Table Key Node → List Node → Cache.Table Key Node → Prop where
    | nil : Children source component operations bound here [] before [] before
    | reference (chosen : select component bound here next = .reference next)
        (tail : Children source component operations bound here rest before values after) :
        Children source component operations bound here (next :: rest) before
          (operations.reference next :: values) after
    | build (chosen : select component bound here next = .build childBound next)
        (head : Build source component operations (childBound, next) before value middle)
        (tail : Children source component operations bound here rest middle values after) :
        Children source component operations bound here (next :: rest) before (value :: values) after

  /-- Transitions execute from left to right, retaining their literal fields. -/
  inductive Rows (source : Nat → List (Row Symbol Constraint Nat))
      (component : Nat → Nat) (operations : Operations Symbol Constraint Node) :
      Bound → Nat → List (Row Symbol Constraint Nat) → Cache.Table Key Node →
        List (Row Symbol Constraint Node) → Cache.Table Key Node → Prop where
    | nil : Rows source component operations bound here [] before [] before
    | cons (head : Children source component operations bound here first.children before children middle)
        (tail : Rows source component operations bound here rest middle copied after) :
        Rows source component operations bound here (first :: rest) before
          (⟨first.symbol, first.constraint, children⟩ :: copied) after
end

variable {Symbol Constraint Node : Type}
variable {source : Nat → List (Row Symbol Constraint Nat)} {component : Nat → Nat}
variable {operations : Operations Symbol Constraint Node}

private theorem publish_growth {before middle : Cache.Table Key Node} {key : Key} {value : Node}
    (absent : before key = none) (growth : Cache.Extends before middle) :
    Cache.Extends before (Cache.put middle key value) := by
  intro old original present
  have different : old ≠ key := by
    intro same
    subst old
    rw [absent] at present
    contradiction
  simpa only [Cache.put, different, ↓reduceIte] using growth old original present

/-- A completed build retains every memo entry present at its start. -/
theorem Build.grows (receipt : Build source component operations key before value after) :
    Cache.Extends before after := by
  induction receipt using Build.rec
    (motive_2 := fun _ _ _ before _ after _ => Cache.Extends before after)
    (motive_3 := fun _ _ _ before _ after _ => Cache.Extends before after)
  case hit present => exact Cache.extends_refl _
  case miss absent body ih => exact publish_growth absent ih
  case reference chosen tail ih => exact ih
  case build chosen head tail first second => exact Cache.extends_trans first second
  case cons head tail first second => exact Cache.extends_trans first second
  all_goals exact Cache.extends_refl _

/-- Ordered child execution retains all old entries. -/
theorem Children.grows
    (receipt : Children source component operations bound here inputs before values after) :
    Cache.Extends before after := by
  induction receipt using Children.rec
    (motive_1 := fun _ before _ after _ => Cache.Extends before after)
    (motive_3 := fun _ _ _ before _ after _ => Cache.Extends before after)
  case hit present => exact Cache.extends_refl _
  case miss absent body ih => exact publish_growth absent ih
  case reference chosen tail ih => exact ih
  case build chosen head tail first second => exact Cache.extends_trans first second
  case cons head tail first second => exact Cache.extends_trans first second
  all_goals exact Cache.extends_refl _

/-- Ordered transition execution retains all old entries. -/
theorem Rows.grows
    (receipt : Rows source component operations bound here inputs before copied after) :
    Cache.Extends before after := by
  induction receipt using Rows.rec
    (motive_1 := fun _ before _ after _ => Cache.Extends before after)
    (motive_2 := fun _ _ _ before _ after _ => Cache.Extends before after)
  case hit present => exact Cache.extends_refl _
  case miss absent body ih => exact publish_growth absent ih
  case reference chosen tail ih => exact ih
  case build chosen head tail first second => exact Cache.extends_trans first second
  case cons head tail first second => exact Cache.extends_trans first second
  all_goals exact Cache.extends_refl _

/-- A completed build publishes the exact result at its requested key. -/
theorem Build.present (receipt : Build source component operations key before value after) :
    after key = some value := by
  cases receipt with
  | hit present => exact present
  | miss _ _ => simp [Cache.put]

/-- Transition order and literal symbol/constraint fields survive the schedule. -/
theorem Rows.fields (receipt : Rows source component operations bound here inputs before copied after) :
    copied.map (fun row => (row.symbol, row.constraint)) =
      inputs.map (fun row => (row.symbol, row.constraint)) := by
  induction receipt using Rows.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ => True)
  case hit => trivial
  case miss => trivial
  case reference => trivial
  case build => trivial
  case cons head tail first second => simp only [List.map_cons, second]
  all_goals first | rfl | trivial

/-- Child execution produces one result for each source occurrence. -/
theorem Children.length (receipt : Children source component operations bound here inputs before values after) :
    values.length = inputs.length := by
  induction receipt using Children.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
  case hit => trivial
  case miss => trivial
  case reference chosen tail ih => exact congrArg Nat.succ ih
  case build chosen head tail first second => exact congrArg Nat.succ second
  case cons => trivial
  all_goals first | rfl | trivial

end MicroCFTA.SourceOrderedBinderImport
