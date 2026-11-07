import MicroCFTA.SourceSizedGroupedClasses

/-!
# Exact source equations for finite grouped classes

The paid seed makes the zero-size prefix empty. Every nonempty product
therefore reads child sizes below its parent size. The finite evaluator
satisfies the unbounded source table equation in the same list order.
That equation has one solution with empty zero-size classes.

The chain-family order obstruction applies to this generic finite table
worker. Native minimum tables, lazy indexes, and public routing remain
separate attachments. No query contract changes here.
-/
namespace MicroCFTA.SourceSizedGroupedRecurrence
open Language RecursiveSize SourceSizedDecided SourceSizedGroupedChainOrder

variable {State Symbol : Type}

private theorem fold_zero (generate : List Nat → Nat → List (Term Symbol))
    (groups : List (List Nat)) :
    (groups.foldl (fun built group => extendForests built (generate group)) seed) 0 = [] := by
  induction groups using snoc_induction with
  | empty => simp [seed]
  | step before last ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      simp [extendForests, ih]

private theorem scaled_congr (first second : Nat → List (Term Symbol))
    (factor size : Nat) (agree : ∀ childSize, childSize ≤ size → first childSize = second childSize) :
    scaled factor first size = scaled factor second size := by
  unfold scaled
  split
  · exact agree size (Nat.le_refl _)
  · split
    · exact agree (size / factor) (Nat.div_le_self _ _)
    · rfl

private theorem group_congr (first second : State → Nat → List (Term Symbol))
    (children : List State) (group : List Nat) (size : Nat)
    (agree : ∀ state childSize, childSize ≤ size → first state childSize = second state childSize) :
    groupClass first children group size = groupClass second children group size := by
  cases group with
  | nil => rfl
  | cons position rest =>
      cases read : children[position]? with
      | none => simp only [groupClass, read]
      | some state =>
          simp only [groupClass, read]
          exact scaled_congr _ _ _ size (agree state)

private theorem fold_congr (first second : State → Nat → List (Term Symbol))
    (children : List State) (bound : Nat)
    (agree : ∀ state childSize, childSize < bound → first state childSize = second state childSize)
    (groups : List (List Nat)) (size : Nat) (within : size ≤ bound) :
    (groups.foldl (fun built group => extendForests built (groupClass first children group)) seed) size =
      (groups.foldl (fun built group => extendForests built (groupClass second children group)) seed) size := by
  induction groups using snoc_induction generalizing size with
  | empty => rfl
  | step before last ih =>
      rw [List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, extendForests]
      apply TablePosition.flatMap_congr
      intro prefixSize prefixIn
      have prefixBound : prefixSize ≤ size := by have := List.mem_range.mp prefixIn; omega
      rw [ih prefixSize (by omega)]
      by_cases zero : prefixSize = 0
      · subst prefixSize
        rw [fold_zero]
        rfl
      · have later : size - prefixSize < bound := by omega
        have same := group_congr first second children last (size - prefixSize)
          (fun state childSize small => agree state childSize (by omega))
        rw [same]

/-- A grouped row reads only child classes strictly below its own requested size. -/
theorem rowClass_congr (first second : State → Nat → List (Term Symbol))
    (symbol : Symbol) (children : List State) (classes : List (List Nat)) (size : Nat)
    (agree : ∀ state childSize, childSize < size → first state childSize = second state childSize) :
    rowClass first symbol children classes size = rowClass second symbol children classes size := by
  unfold rowClass
  dsimp only
  exact congrArg (List.map (assemble symbol children.length
    (CompactGroups.childGroups children.length classes)))
      (fold_congr first second children size agree
        (CompactGroups.childGroups children.length classes) size (Nat.le_refl _))

/-- Row choice preserves the same strict child-size dependency and exact order. -/
theorem classOf_congr (first second : State → Nat → List (Term Symbol))
    (rows : List (Row State Symbol (List (List Nat)))) (size : Nat)
    (agree : ∀ state childSize, childSize < size → first state childSize = second state childSize) :
    SourceSizedGroupedClasses.classOf first rows size = SourceSizedGroupedClasses.classOf second rows size := by
  apply TablePosition.flatMap_congr
  intro row _
  exact rowClass_congr first second row.label row.children row.constraint size agree

/-- The grouped source class at zero is empty for every row and child callback. -/
theorem rowClass_zero (classAt : State → Nat → List (Term Symbol))
    (symbol : Symbol) (children : List State) (classes : List (List Nat)) :
    rowClass classAt symbol children classes 0 = [] := by
  unfold rowClass
  dsimp only
  rw [fold_zero]
  rfl

/-- The finite worker satisfies the literal source equation with its full child-class function. -/
theorem classes_succ (rows : State → List (Row State Symbol (List (List Nat))))
    (remaining : Nat) (state : State) :
    SourceSizedGroupedClasses.classes rows (remaining + 1) state =
      SourceSizedGroupedClasses.classOf
        (fun child size => SourceSizedGroupedClasses.classes rows size child) (rows state) (remaining + 1) := by
  rw [SourceSizedGroupedClasses.classes_succ]
  apply classOf_congr
  intro child childSize smaller
  simp only [ite_eq_left (show childSize ≤ remaining by omega)]

/-- Empty zero classes and the actual ordered row equation determine every class uniquely. -/
theorem unique (rows : State → List (Row State Symbol (List (List Nat))))
    (other : State → Nat → List (Term Symbol)) (zero : ∀ state, other state 0 = [])
    (step : ∀ state remaining, other state (remaining + 1) =
      SourceSizedGroupedClasses.classOf other (rows state) (remaining + 1))
    (size : Nat) (state : State) : SourceSizedGroupedClasses.classes rows size state = other state size := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
      cases size with
      | zero => rw [SourceSizedGroupedClasses.classes_zero, zero]
      | succ remaining =>
          rw [classes_succ, step]
          exact classOf_congr _ _ _ _ (fun child childSize smaller => ih childSize smaller child)

/-- The explicit fixed chain table is an instance of the generic finite grouped worker. -/
theorem chain_table_classes (size : Nat) (state : Option Bool) :
    SourceSizedGroupedClasses.classes SourceSizedGroupedChainOrder.table size state =
      SourceSizedGroupedChainOrder.tableClasses state size := by
  apply unique
  · intro state
    cases state with
    | none => exact rowClass_zero _ _ _ _
    | some kind => simp [tableClasses, chainClasses]
  · intro state remaining
    exact table_equation state (remaining + 1)

/-- The generic finite grouped worker can have no fixed reference-graph list representation.
This still does not attach the worker to the native public API. -/
theorem chain_not_reference {Reference : Type} (rows : Automaton Reference Nat) (root : Reference) :
    ∃ size, SourceSizedGroupedClasses.classes SourceSizedGroupedChainOrder.table size none ≠
      SourceSizedReference.classes rows size root := by
  obtain ⟨size, different⟩ := familyClass_not_reference rows root
  refine ⟨size, ?_⟩
  rw [chain_table_classes]
  exact different

end MicroCFTA.SourceSizedGroupedRecurrence
