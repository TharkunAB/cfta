import MicroCFTA.SourceSizedReference

/-!
# A bound on increasing subsequences of a reference class

A root row visits prefix sizes in increasing order. Its last child therefore
has nonincreasing size. Guards and first-occurrence removal preserve this
order. A strictly increasing subsequence takes at most one term from each
root row. The state type need not be finite.

This bound does not establish the order of the grouped implementation.
-/

namespace MicroCFTA.SourceSizedReferenceOrderBound

open Language RecursiveSize SourceSizedCandidates SourceSizedReference

/-- The last child has size zero when the term has no children. -/
def lastChildSize : Term Symbol → Nat
  | .node _ children => (children.getLast?.map nodeSize).getD 0

/-- Appending a child determines the last-child size. -/
theorem lastChildSize_snoc (label : Symbol) (before : List (Term Symbol))
    (last : Term Symbol) :
    lastChildSize (.node label (before ++ [last])) = nodeSize last := by
  simp [lastChildSize]

private theorem pairwise_of_constant {A : Type} (measure : A → Nat)
    (values : List A) (size : Nat)
    (constant : ∀ value ∈ values, measure value = size) :
    values.Pairwise (fun first second => measure second ≤ measure first) := by
  induction values with
  | nil => exact .nil
  | cons first rest ih =>
      apply List.pairwise_cons.mpr
      constructor
      · intro second present
        simpa only [constant first (by simp), constant second (by simp [present])]
          using Nat.le_refl size
      · exact ih (fun value present => constant value (by simp [present]))

private theorem length_le_one_of_opposite_orders {A : Type}
    (measure : A → Nat) (values : List A)
    (increasing : values.Pairwise (fun first second => measure first < measure second))
    (decreasing : values.Pairwise (fun first second => measure second ≤ measure first)) :
    values.length ≤ 1 := by
  cases values with
  | nil => simp
  | cons first rest =>
      cases rest with
      | nil => simp
      | cons second tail =>
          have up := (List.pairwise_cons.mp increasing).1 second (by simp)
          have down := (List.pairwise_cons.mp decreasing).1 second (by simp)
          omega

/-- A strictly increasing subsequence takes at most one value from each
nonincreasing block. -/
theorem increasing_sublist_flatMap_bound {Owner Value : Type}
    (measure : Value → Nat) (owners : List Owner) (block : Owner → List Value)
    (descending : ∀ owner ∈ owners,
      (block owner).Pairwise (fun first second => measure second ≤ measure first))
    (selected : List Value) (included : selected.Sublist (owners.flatMap block))
    (increasing : selected.Pairwise (fun first second => measure first < measure second)) :
    selected.length ≤ owners.length := by
  induction owners generalizing selected with
  | nil =>
      simp only [List.flatMap_nil, List.sublist_nil] at included
      simp [included]
  | cons owner rest ih =>
      simp only [List.flatMap_cons] at included
      obtain ⟨first, later, rfl, firstIncluded, laterIncluded⟩ :=
        List.sublist_append_iff.mp included
      have splitOrder := List.pairwise_append.mp increasing
      have firstDescending :=
        (descending owner (by simp)).sublist firstIncluded
      have firstBound :=
        length_le_one_of_opposite_orders measure first splitOrder.1 firstDescending
      have laterBound := ih
        (fun value present => descending value (by simp [present]))
        later laterIncluded splitOrder.2.1
      simp only [List.length_append, List.length_cons]
      omega

/-- A source candidate row visits last-child sizes in nonincreasing order. -/
theorem candidates_lastChildSize_nonincreasing {State Symbol : Type}
    (classAt : State → Nat → List (Term Symbol))
    (sized : ∀ state size term, term ∈ classAt state size → nodeSize term = size)
    (label : Symbol) (children : List State) (size : Nat) :
    (candidates classAt label children size).Pairwise
      (fun first second => lastChildSize second ≤ lastChildSize first) := by
  cases size with
  | zero => simp [candidates]
  | succ remaining =>
      cases reversed : children.reverse with
      | nil =>
          simp only [candidates, reversed, go]
          split <;> simp
      | cons current before =>
          let block := fun left =>
            (go classAt before left).flatMap fun arguments =>
              (classAt current (remaining - left)).map fun term =>
                Term.node label (term :: arguments).reverse
          have blockSize (left : Nat) (term : Term Symbol)
              (present : term ∈ block left) : lastChildSize term = remaining - left := by
            obtain ⟨arguments, _, mapped⟩ := List.mem_flatMap.mp present
            obtain ⟨term, member, rfl⟩ := List.mem_map.mp mapped
            simpa [lastChildSize, List.reverse_cons] using
              sized current (remaining - left) term member
          simp only [candidates, reversed, go, List.map_flatMap, List.map_map,
            Function.comp_def]
          change ((List.range (remaining + 1)).flatMap block).Pairwise _
          apply List.pairwise_flatMap.mpr
          constructor
          · intro left _
            exact pairwise_of_constant lastChildSize (block left) (remaining - left)
              (blockSize left)
          · apply List.Pairwise.imp_of_mem (p := List.pairwise_lt_range)
            intro left right _ _ earlier first firstIn second secondIn
            rw [blockSize left first firstIn, blockSize right second secondIn]
            omega

private theorem dedup_sublist {A : Type} [DecidableEq A] (seen values : List A) :
    (RefinementValidation.dedup seen values).Sublist values := by
  induction values generalizing seen with
  | nil => exact .slnil
  | cons first rest ih =>
      simp only [RefinementValidation.dedup]
      split
      · exact (ih seen).cons first
      · exact (ih (first :: seen)).cons_cons first

/-- Guard filtering and first-occurrence removal preserve the root-row bound. -/
theorem classOf_increasing_sublist_bound {State Symbol : Type} [DecidableEq Symbol]
    (classAt : State → Nat → List (Term Symbol))
    (sized : ∀ state size term, term ∈ classAt state size → nodeSize term = size)
    (rows : List (Edge State Symbol)) (size : Nat) (selected : List (Term Symbol))
    (included : selected.Sublist (classOf classAt rows size))
    (increasing : selected.Pairwise
      (fun first second => lastChildSize first < lastChildSize second)) :
    selected.length ≤ rows.length := by
  apply increasing_sublist_flatMap_bound lastChildSize rows
    (fun edge => (candidates classAt edge.label edge.children size).filter edge.guard)
    ?_ selected ?_ increasing
  · intro edge _
    exact (candidates_lastChildSize_nonincreasing classAt sized
      edge.label edge.children size).sublist List.filter_sublist
  · exact included.trans (dedup_sublist [] _)

/-- A fixed reference root admits at most one strictly increasing last-child
size per outgoing root row. This theorem permits infinitely many states. -/
theorem classes_increasing_sublist_bound {State Symbol : Type} [DecidableEq Symbol]
    (A : Automaton State Symbol) (root : State) (size : Nat)
    (selected : List (Term Symbol))
    (included : selected.Sublist (classes A size root))
    (increasing : selected.Pairwise
      (fun first second => lastChildSize first < lastChildSize second)) :
    selected.length ≤ (A root).length := by
  cases size with
  | zero =>
      rw [classes_zero] at included
      have empty := List.eq_nil_of_sublist_nil included
      simp [empty]
  | succ remaining =>
      rw [classes_succ] at included
      exact classOf_increasing_sublist_bound
        (fun state size => classes A size state)
        (fun state size term member => ((mem_classes_iff A size state term).mp member).2)
        (A root) (remaining + 1) selected included increasing

end MicroCFTA.SourceSizedReferenceOrderBound
