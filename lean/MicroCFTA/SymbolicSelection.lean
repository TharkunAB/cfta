import MicroCFTA.SymbolicCounting

/-!
# Operational inverse of the symbolic decoder

These proofs compare the actual decoder and inverse on the same cache state.
They track the residual rank separately. A semantic count theorem is needed
to prove that the final residual at a complete root is zero.
-/
namespace MicroCFTA.SymbolicDriver
open Language

/-- Singleton decoding restores the cache snapshot even when its inner calls add entries. -/
theorem isolated_run (action : CountM Symbol Value) (counts : Counts Symbol) :
    isolated action counts = match action counts with
      | .error error => .error error
      | .ok (value, _) => .ok (value, counts) := by
  simp [isolated, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    Except.bind, Pure.pure, StateT.pure, Except.pure, liftM, monadLift, MonadLift.monadLift, StateT.lift]
  cases action counts <;> rfl

/-- Removing later copies leaves a duplicate-free list. -/
theorem eraseDups_nodup [BEq Value] [LawfulBEq Value] (values : List Value) : values.eraseDups.Nodup := by
  cases values with
  | nil => simp
  | cons first rest =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · simp [List.mem_eraseDups]
      · exact eraseDups_nodup _
termination_by values.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le ..)

/-- Constructor candidates retain distinct symbol/arity pairs even when order keys collide. -/
theorem constructorsAt_nodup [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (path : List Nat) (root : Nat) :
    (constructorsAt graph order path root).Nodup := by
  unfold constructorsAt
  exact (List.mergeSort_perm _ _).nodup_iff.mpr
    (eraseDups_nodup ((graph.edges (graph.project path root)).map fun edge => (edge.symbol, edge.children.length)))

/-- Inverting one selected subtree restores its consumed prefix rank and the same final cache. -/
def SelectionInverse [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel : Nat) : Prop :=
  ∀ root path rank initial term final suffix after,
    0 ≤ rank → selectAt graph order fuel root path rank initial = .ok ((term, final, suffix), after) →
      0 ≤ suffix ∧ ∀ before,
        rankAt graph order fuel root path term before initial = .ok (some (final, before + rank - suffix), after)

/-- Constructor block inversion uses each constructor once and returns the same cache state. -/
def ConstructorInverse [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel : Nat) : Prop :=
  ∀ root path rank constructors initial symbol children final suffix after,
    constructors.Nodup → 0 ≤ rank →
    chooseConstructor graph order fuel root path rank constructors initial =
      .ok ((.node symbol children, final, suffix), after) →
    (symbol, children.length) ∈ constructors ∧ 0 ≤ suffix ∧ ∀ before,
      rankConstructor graph order fuel root path (symbol, children.length) children before constructors initial =
        .ok (some (final, before + rank - suffix), after)

/-- Child inversion follows exactly the indices selected by the decoder. -/
def ChildrenInverse [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel : Nat) : Prop :=
  ∀ root path rank indices initial children final suffix after,
    0 ≤ rank → selectChildren graph order fuel root path rank indices initial =
      .ok ((children, final, suffix), after) →
    children.length = indices.length ∧ 0 ≤ suffix ∧ ∀ before,
      rankChildren graph order fuel root path before (children.zip indices) initial =
        .ok (some (final, before + rank - suffix), after)

/-- The source singleton shortcut and ordinary constructor branch both preserve the inverse relation. -/
theorem selection_inverse_step [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel : Nat)
    (constructors : ConstructorInverse graph order fuel) : SelectionInverse graph order (fuel + 1) := by
  intro root path rank initial term final suffix after nonnegative success
  cases term with
  | node symbol children =>
      cases counted : countNode graph fuel (graph.project path root) initial with
      | error error =>
          simp only [selectAt, Bind.bind, StateT.bind, counted, Except.bind] at success
          cases success
      | ok pair =>
          rcases pair with ⟨count, middle⟩
          simp only [selectAt, Bind.bind, StateT.bind, counted, Except.bind] at success
          by_cases singleton : count = 1
          · simp only [singleton, ↓reduceIte] at success
            change Except.bind (isolated (selectUnique graph order fuel (graph.project path root) []) middle)
              (fun (selected, cache) => .ok ((selected, root, rank), cache)) =
                .ok ((.node symbol children, final, suffix), after) at success
            cases unique : isolated (selectUnique graph order fuel (graph.project path root) []) middle with
            | error error => simp only [unique, Except.bind] at success; cases success
            | ok pair =>
                rcases pair with ⟨uniqueTerm, cache⟩
                simp only [unique, Except.bind, Except.ok.injEq, Prod.mk.injEq] at success
                rcases success with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
                refine ⟨nonnegative, ?_⟩
                intro before
                simp only [rankAt, Bind.bind, StateT.bind, counted, Except.bind, singleton, ↓reduceIte,
                  unique, Pure.pure, StateT.pure, Except.pure]
                rw [(termEq_correct _ _).mpr rfl]
                simp
          · simp only [singleton, ↓reduceIte] at success
            have checked := constructors root path rank (constructorsAt graph order path root) middle
              symbol children final suffix after (constructorsAt_nodup graph order path root) nonnegative success
            refine ⟨checked.2.1, ?_⟩
            intro before
            simp only [rankAt, Bind.bind, StateT.bind, counted, Except.bind, singleton, ↓reduceIte, checked.1]
            exact checked.2.2 before

/-- Sequential child inversion uses the same conditioned graph and cache after each child. -/
theorem children_inverse_step [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel : Nat)
    (selection : SelectionInverse graph order fuel) (remaining : ChildrenInverse graph order fuel) :
    ChildrenInverse graph order (fuel + 1) := by
  intro root path rank indices initial children final suffix after nonnegative success
  cases indices with
  | nil =>
      cases success
      refine ⟨rfl, nonnegative, ?_⟩
      intro before
      simp [rankChildren]
      rfl
  | cons index rest =>
      cases selected : selectAt graph order fuel root (path ++ [index]) rank initial with
      | error error =>
          simp only [selectChildren, Bind.bind, StateT.bind, selected, Except.bind] at success
          cases success
      | ok pair =>
          rcases pair with ⟨⟨term, restricted, residual⟩, middle⟩
          have first := selection root (path ++ [index]) rank initial term restricted residual middle nonnegative selected
          cases tailSelected : selectChildren graph order fuel restricted path residual rest middle with
          | error error =>
              simp only [selectChildren, Bind.bind, StateT.bind, selected, Except.bind, tailSelected] at success
              cases success
          | ok pair =>
              rcases pair with ⟨⟨terms, last, lastRank⟩, cache⟩
              have tail := remaining restricted path residual rest middle terms last lastRank cache first.1 tailSelected
              simp only [selectChildren, Bind.bind, StateT.bind, selected, Except.bind, tailSelected,
                Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
              rcases success with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
              refine ⟨by simp [tail.1], tail.2.1, ?_⟩
              intro before
              simp only [List.zip_cons_cons, rankChildren, Bind.bind, StateT.bind, first.2 before, Except.bind]
              have inverted := tail.2.2 (before + rank - residual)
              have arithmetic : before + rank - residual + residual - lastRank = before + rank - lastRank := by omega
              simpa only [arithmetic] using inverted

/-- Constructor block skipping and child decoding invert through the same source counts. -/
theorem constructor_inverse_step [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel : Nat)
    (remaining : ConstructorInverse graph order fuel) (childrenInverse : ChildrenInverse graph order fuel) :
    ConstructorInverse graph order (fuel + 1) := by
  intro root path rank constructors initial symbol children final suffix after distinct nonnegative success
  cases constructors with
  | nil => cases success
  | cons constructor rest =>
      rcases constructor with ⟨headSymbol, arity⟩
      have distinct := List.nodup_cons.mp distinct
      cases counted : countNode graph fuel (graph.condition path (headSymbol, arity) root) initial with
      | error error =>
          simp only [chooseConstructor, Bind.bind, StateT.bind, counted, Except.bind] at success
          cases success
      | ok pair =>
          rcases pair with ⟨count, middle⟩
          simp only [chooseConstructor, Bind.bind, StateT.bind, counted, Except.bind] at success
          by_cases skip : rank ≥ count
          · simp only [skip, ↓reduceIte] at success
            have tail := remaining root path (rank - count) rest middle symbol children final suffix after
              distinct.2 (by omega) success
            refine ⟨List.mem_cons_of_mem _ tail.1, tail.2.1, ?_⟩
            intro before
            have different : (headSymbol, arity) ≠ (symbol, children.length) := by
              intro same
              exact distinct.1 (same ▸ tail.1)
            simp only [rankConstructor, Bind.bind, StateT.bind, counted, Except.bind, different, ↓reduceIte]
            have inverted := tail.2.2 (before + count)
            have arithmetic : before + count + (rank - count) - suffix = before + rank - suffix := by omega
            simpa only [arithmetic] using inverted
          · simp only [skip, ↓reduceIte] at success
            change Except.bind
              (selectChildren graph order fuel (graph.condition path (headSymbol, arity) root) path rank (List.range arity) middle)
              (fun ((terms, last, residual), cache) => .ok ((Term.node headSymbol terms, last, residual), cache)) =
                .ok ((Term.node symbol children, final, suffix), after) at success
            cases selected : selectChildren graph order fuel (graph.condition path (headSymbol, arity) root)
                path rank (List.range arity) middle with
            | error error => simp only [selected, Except.bind] at success; cases success
            | ok pair =>
                rcases pair with ⟨⟨terms, last, residual⟩, cache⟩
                have decoded := childrenInverse (graph.condition path (headSymbol, arity) root) path rank
                  (List.range arity) middle terms last residual cache nonnegative selected
                simp only [selected, Except.bind, Except.ok.injEq, Prod.mk.injEq, Term.node.injEq] at success
                rcases success with ⟨⟨⟨rfl, rfl⟩, rfl, rfl⟩, rfl⟩
                have length : terms.length = arity := by simpa using decoded.1
                refine ⟨by simp [length], decoded.2.1, ?_⟩
                intro before
                have positive : count ≠ 0 := by omega
                simp only [rankConstructor, length, Bind.bind, StateT.bind, counted, Except.bind,
                  ↓reduceIte, positive]
                have positions : terms.zipIdx = terms.zip (List.range arity) := by
                  simp [List.zipIdx_eq_zip_range', length, List.range_eq_range']
                rw [positions]
                exact decoded.2.2 before

/-- The three mutually recursive decoder paths invert their successful execution at every fuel bound. -/
theorem decoder_inverse_mutual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel : Nat) :
    SelectionInverse graph order fuel ∧ ConstructorInverse graph order fuel ∧ ChildrenInverse graph order fuel := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro root path rank initial term final suffix after nonnegative success
        cases success
      · intro root path rank constructors initial symbol children final suffix after distinct nonnegative success
        cases success
      · intro root path rank indices initial children final suffix after nonnegative success
        cases indices with
        | cons first rest => cases success
        | nil =>
            cases success
            refine ⟨rfl, nonnegative, ?_⟩
            intro before
            simp [rankChildren]
            rfl
  | succ fuel ih =>
      exact ⟨selection_inverse_step graph order fuel ih.2.1,
        constructor_inverse_step graph order fuel ih.2.1 ih.2.2,
        children_inverse_step graph order fuel ih.1 ih.2.2⟩

/-- Every successful public decode has a successful source inverse, up to its unconsumed suffix. -/
theorem unrank_rankOf_residual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel root : Nat) (rank : Int) (term : Term Symbol)
    (success : unrank graph order fuel root rank = .ok term) :
    ∃ suffix, 0 ≤ suffix ∧ rankOf graph order fuel root term = .ok (some (rank - suffix)) := by
  cases counted : countNode graph fuel root {} with
  | error error => simp only [unrank, counted] at success; cases success
  | ok pair =>
      rcases pair with ⟨total, counts⟩
      simp only [unrank, counted, Bind.bind, Except.bind] at success
      split at success
      · cases success
      · rename_i inRange
        have nonnegative : 0 ≤ rank := by omega
        cases selected : selectAt graph order fuel root [] rank counts with
        | error error => simp only [selected] at success; cases success
        | ok pair =>
            rcases pair with ⟨⟨chosen, final, suffix⟩, after⟩
            simp only [selected, Pure.pure, Except.pure, Except.ok.injEq] at success
            subst term
            have inverse := (decoder_inverse_mutual graph order fuel).1 root [] rank counts chosen final suffix after
              nonnegative selected
            refine ⟨suffix, inverse.1, ?_⟩
            simp only [rankOf, counted, Bind.bind, Except.bind, inverse.2 0, Pure.pure, Except.pure, Option.map_some]
            simp

/-- A completed root selection with zero residual has its exact original source rank. -/
theorem unrank_rankOf_exact [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel root : Nat) (rank : Int)
    (total : Int) (counts after : Counts Symbol) (term : Term Symbol) (final : Nat)
    (counted : countNode graph fuel root {} = .ok (total, counts)) (nonnegative : 0 ≤ rank)
    (bounded : rank < total)
    (selected : selectAt graph order fuel root [] rank counts = .ok ((term, final, 0), after)) :
    unrank graph order fuel root rank = .ok term ∧ rankOf graph order fuel root term = .ok (some rank) := by
  have inverse := (decoder_inverse_mutual graph order fuel).1 root [] rank counts term final 0 after nonnegative selected
  constructor
  · simp only [unrank, counted, Bind.bind, Except.bind]
    have valid : ¬(rank < 0 ∨ total ≤ rank) := by omega
    simp only [valid, ↓reduceIte, selected, Pure.pure, Except.pure]
  · simp only [rankOf, counted, Bind.bind, Except.bind, inverse.2 0, Pure.pure, Except.pure, Option.map_some]
    simp

end MicroCFTA.SymbolicDriver
