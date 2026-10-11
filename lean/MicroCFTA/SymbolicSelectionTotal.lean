import MicroCFTA.SymbolicBlocks

/-!
# Total source selection at every valid finite rank

Constructor blocks partition the accepted language. Each selected child has
smaller subtree height. Earlier child restrictions preserve all remaining
path and height bounds because they retain a subset of the current language.
-/
namespace MicroCFTA.SymbolicDriver
open Language

/-- Total selection for every current position with a fixed finite subtree-height bound. -/
def SelectHeightTotal [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (height : Nat) : Prop :=
  ∀ root path rank initial, invariant initial → 0 ≤ rank → rank < ((meaning.terms root).length : Int) →
    PathExists meaning root path → SubtreeHeight meaning root path height →
      Eventually (fun fuel => selectAt graph order fuel root path rank) initial

/-- Left-to-right child selection has a stable result when selection terminates at every child height. -/
theorem selectChildren_eventual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (height : Nat) (smaller : SelectHeightTotal graph order meaning invariant height)
    (indices : List Nat) (root : Nat) (path : List Nat) (rank : Int) (initial : Counts Symbol)
    (valid : invariant initial) (nonnegative : 0 ≤ rank) (inRange : rank < ((meaning.terms root).length : Int))
    (paths : ∀ index ∈ indices, PathExists meaning root (path ++ [index]))
    (heights : ∀ index ∈ indices, SubtreeHeight meaning root (path ++ [index]) height) :
    Eventually (fun fuel => selectChildren graph order fuel root path rank indices) initial := by
  induction indices generalizing root rank initial with
  | nil => exact ⟨0, ([], root, rank), initial, fun fuel _ => by simp only [selectChildren]; rfl⟩
  | cons index rest ih =>
      obtain ⟨firstBound, ⟨term, selected, suffix⟩, middle, firstStable⟩ :=
        smaller root (path ++ [index]) rank initial valid nonnegative inRange (paths index (by simp)) (heights index (by simp))
      dsimp only at firstStable
      have firstRun := firstStable firstBound (Nat.le_refl _)
      have semantic := (decoder_meaning_mutual graph order meaning invariant sound firstBound).1
        root (path ++ [index]) rank initial term selected suffix middle valid nonnegative (paths index (by simp)) firstRun
      have bounded := (decoder_bounds_mutual graph order (fun node => (meaning.terms node).length) invariant sound firstBound).1
        root (path ++ [index]) rank initial term selected suffix middle valid nonnegative inRange firstRun
      have lower := ((decoder_inverse_mutual graph order firstBound).1 root (path ++ [index]) rank initial term selected suffix middle nonnegative firstRun).1
      obtain ⟨restBound, ⟨children, final, finalRank⟩, finalState, restStable⟩ :=
        ih selected suffix middle semantic.1 lower bounded.2
          (fun child member => pathExists_subset meaning selected root semantic.2.1 _ (paths child (by simp [member])))
          (fun child member => subtreeHeight_subset meaning selected root semantic.2.1 _ height (heights child (by simp [member])))
      dsimp only at restStable
      refine ⟨max firstBound restBound + 1, (term :: children, final, finalRank), finalState, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [selectChildren, Bind.bind, StateT.bind, firstStable fuel (by omega), Except.bind, restStable fuel (by omega)]
          rfl

/-- A finite constructor scan selects a nonempty exact block and terminates in smaller child subtrees. -/
theorem chooseConstructor_eventual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (height : Nat) (smaller : SelectHeightTotal graph order meaning invariant (height - 1))
    (constructors : List (Symbol × Nat)) (root : Nat) (path : List Nat) (rank : Int) (initial : Counts Symbol)
    (valid : invariant initial) (nonnegative : 0 ≤ rank)
    (inRange : rank < (blockCount graph meaning root path constructors : Int))
    (bounded : SubtreeHeight meaning root path height) :
    Eventually (fun fuel => chooseConstructor graph order fuel root path rank constructors) initial := by
  induction constructors generalizing rank initial with
  | nil => simp only [blockCount, List.map_nil, List.sum_nil, Int.natCast_zero] at inRange; omega
  | cons constructor rest ih =>
      obtain ⟨countBound, middle, middleValid, counted⟩ :=
        count_eventual_exact graph meaning invariant sound countTotal (graph.condition path constructor root) initial valid
      by_cases skipped : rank ≥ ((meaning.terms (graph.condition path constructor root)).length : Int)
      · have lower : 0 ≤ rank - ((meaning.terms (graph.condition path constructor root)).length : Int) := by omega
        have upper : rank - ((meaning.terms (graph.condition path constructor root)).length : Int) <
            (blockCount graph meaning root path rest : Int) := by
          simp only [blockCount, List.map_cons, List.sum_cons, Int.natCast_add] at inRange ⊢
          omega
        obtain ⟨restBound, output, finalState, restStable⟩ := ih _ middle middleValid lower upper
        dsimp only at restStable
        refine ⟨max countBound restBound + 1, output, finalState, ?_⟩
        intro fuel enough
        cases fuel with
        | zero => omega
        | succ fuel =>
            simp only [chooseConstructor, Bind.bind, StateT.bind, counted fuel (by omega), Except.bind, ite_eq_left skipped]
            exact restStable fuel (by omega)
      · have inside : rank < ((meaning.terms (graph.condition path constructor root)).length : Int) := by omega
        have childShape := fun index member => conditioned_child_height graph meaning root path constructor height bounded index (List.mem_range.mp member)
        obtain ⟨childBound, ⟨children, final, suffix⟩, finalState, childrenStable⟩ :=
          selectChildren_eventual graph order meaning invariant sound (height - 1) smaller (List.range constructor.2)
            (graph.condition path constructor root) path rank middle middleValid nonnegative inside
            (fun index member => (childShape index member).1) (fun index member => (childShape index member).2)
        dsimp only at childrenStable
        refine ⟨max countBound childBound + 1, (.node constructor.1 children, final, suffix), finalState, ?_⟩
        intro fuel enough
        cases fuel with
        | zero => omega
        | succ fuel =>
            simp only [chooseConstructor, Bind.bind, StateT.bind, counted fuel (by omega), Except.bind, ite_eq_right skipped,
              childrenStable fuel (by omega)]
            rfl

/-- The full actual source selector terminates at every in-range rank and existing bounded-height position. -/
theorem selectAt_eventual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (coverage : ConstructorCoverage graph order meaning) (height : Nat) :
    SelectHeightTotal graph order meaning invariant height := by
  induction height using Nat.strongRecOn with
  | ind height ih =>
      intro root path rank initial valid nonnegative inRange existsPath bounded
      have positive : 0 < height := subtreeHeight_positive meaning root path height (by omega) existsPath bounded
      obtain ⟨countBound, middle, middleValid, counted⟩ :=
        count_eventual_exact graph meaning invariant sound countTotal (graph.project path root) initial valid
      by_cases singletonCount : (meaning.terms (graph.project path root)).length = 1
      · obtain ⟨unique, singleton⟩ := List.length_eq_one_iff.mp singletonCount
        obtain ⟨uniqueBound, selected, discarded, uniqueStable⟩ :=
          selectUnique_eventual graph order meaning invariant sound countTotal coverage unique.height
            (graph.project path root) [] unique unique singleton rfl rfl middle middleValid
        dsimp only at uniqueStable
        refine ⟨max countBound uniqueBound + 1, (selected, root, rank), middle, ?_⟩
        intro fuel enough
        cases fuel with
        | zero => omega
        | succ fuel =>
            have isolatedSuccess : isolated (selectUnique graph order fuel (graph.project path root) []) middle = .ok (selected, middle) := by
              rw [isolated_run, uniqueStable fuel (by omega)]
            simp only [selectAt, Bind.bind, StateT.bind, counted fuel (by omega), Except.bind, singletonCount,
              Int.natCast_one, ite_true, isolatedSuccess]
            rfl
      · have smaller := ih (height - 1) (by omega)
        have blockBound : rank < (blockCount graph meaning root path (constructorsAt graph order path root) : Int) := by
          rw [constructorsAt_count graph order meaning coverage root path existsPath]
          exact inRange
        obtain ⟨scanBound, output, finalState, scanStable⟩ := chooseConstructor_eventual graph order meaning invariant sound countTotal
          height smaller (constructorsAt graph order path root) root path rank middle middleValid nonnegative blockBound bounded
        dsimp only at scanStable
        have different : ¬((meaning.terms (graph.project path root)).length : Int) = 1 := by omega
        refine ⟨max countBound scanBound + 1, output, finalState, ?_⟩
        intro fuel enough
        cases fuel with
        | zero => omega
        | succ fuel =>
            simp only [selectAt, Bind.bind, StateT.bind, counted fuel (by omega), Except.bind, ite_eq_right different]
            exact scanStable fuel (by omega)

end MicroCFTA.SymbolicDriver
