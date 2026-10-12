import MicroCFTA.SymbolicTotalAPI

/-!
# Shared cache contents cannot change symbolic results

Two valid snapshots can contain different sets of previously computed
counts. Every successful query returns the same value from either snapshot.
The resulting caches may differ. Atomic replacement can discard another
query's new counts, but it cannot change the meaning of a later query.
-/
namespace MicroCFTA.SymbolicDriver

/-- A cache action preserves validity and has the same result from any two valid snapshots. -/
structure CacheLaw (invariant : State → Prop) (action : StateT State (Except Failure) Value) : Prop where
  preserves : Preserves invariant action
  observes : ∀ first second left right afterFirst afterSecond,
    invariant first → invariant second → action first = .ok (left, afterFirst) →
      action second = .ok (right, afterSecond) → left = right

/-- Pure output is independent of cache contents. -/
theorem cacheLaw_pure (invariant : State → Prop) (value : Value) :
    CacheLaw invariant (pure value : StateT State (Except Failure) Value) := by
  refine ⟨preserves_pure invariant value, ?_⟩
  intro first second left right afterFirst afterSecond firstValid secondValid firstRun secondRun
  cases firstRun
  cases secondRun
  rfl

/-- Failure has no successful observations to compare. -/
theorem cacheLaw_error (invariant : State → Prop) (error : Failure) :
    CacheLaw invariant (throw error : StateT State (Except Failure) Value) := by
  refine ⟨preserves_error invariant error, ?_⟩
  intro first second left right afterFirst afterSecond firstValid secondValid firstRun secondRun
  cases firstRun

/-- Result independence composes through the exact source state bind. -/
theorem cacheLaw_bind (invariant : State → Prop) (first : StateT State (Except Failure) Input)
    (rest : Input → StateT State (Except Failure) Value)
    (firstLaw : CacheLaw invariant first) (restLaw : ∀ value, CacheLaw invariant (rest value)) :
    CacheLaw invariant (first >>= rest) := by
  refine ⟨preserves_bind invariant first rest firstLaw.preserves (fun value => (restLaw value).preserves), ?_⟩
  intro leftState rightState left right afterLeft afterRight leftValid rightValid leftRun rightRun
  change Except.bind (first leftState) (fun (value, middle) => rest value middle) = .ok (left, afterLeft) at leftRun
  change Except.bind (first rightState) (fun (value, middle) => rest value middle) = .ok (right, afterRight) at rightRun
  cases firstLeft : first leftState with
  | error error => simp only [firstLeft, Except.bind] at leftRun; cases leftRun
  | ok pair =>
    rcases pair with ⟨leftValue, middleLeft⟩
    cases firstRight : first rightState with
    | error error => simp only [firstRight, Except.bind] at rightRun; cases rightRun
    | ok pair =>
      rcases pair with ⟨rightValue, middleRight⟩
      have same := firstLaw.observes leftState rightState leftValue rightValue middleLeft middleRight
        leftValid rightValid firstLeft firstRight
      subst rightValue
      exact (restLaw leftValue).observes middleLeft middleRight left right afterLeft afterRight
        (firstLaw.preserves leftState leftValue middleLeft leftValid firstLeft)
        (firstLaw.preserves rightState leftValue middleRight rightValid firstRight)
        (by simpa only [firstLeft, Except.bind] using leftRun)
        (by simpa only [firstRight, Except.bind] using rightRun)

/-- Finite traversals retain result independence and valid intermediate snapshots. -/
theorem cacheLaw_mapM (invariant : State → Prop) (action : Input → StateT State (Except Failure) Value)
    (inputs : List Input) (law : ∀ input ∈ inputs, CacheLaw invariant (action input)) :
    CacheLaw invariant (inputs.mapM action : StateT State (Except Failure) (List Value)) := by
  induction inputs with
  | nil => exact cacheLaw_pure invariant []
  | cons first rest ih =>
    rw [List.mapM_cons]
    apply cacheLaw_bind invariant (action first) _ (law first (by simp))
    intro value
    apply cacheLaw_bind invariant (rest.mapM action) _ (ih (fun input member => law input (by simp [member])))
    intro values
    exact cacheLaw_pure invariant (value :: values)

/-- Restoring snapshots does not alter the inner query's result independence. -/
theorem cacheLaw_isolated (invariant : Counts Symbol → Prop) (action : CountM Symbol Value)
    (law : CacheLaw invariant action) : CacheLaw invariant (isolated action) := by
  refine ⟨isolated_preserves invariant action, ?_⟩
  intro first second left right afterFirst afterSecond firstValid secondValid firstRun secondRun
  obtain ⟨innerFirst, firstRun, _⟩ := isolated_inner action first afterFirst left firstRun
  obtain ⟨innerSecond, secondRun, _⟩ := isolated_inner action second afterSecond right secondRun
  exact law.observes first second left right innerFirst innerSecond firstValid secondValid firstRun secondRun

/-- Exact counts make cache hits and recomputed counts observationally equal. -/
theorem count_cacheLaw [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (size : Nat → Nat)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph size invariant) (fuel root : Nat) :
    CacheLaw invariant (countNode graph fuel root) := by
  refine ⟨count_preserves graph size invariant sound fuel root, ?_⟩
  intro first second left right afterFirst afterSecond firstValid secondValid firstRun secondRun
  exact (sound fuel root first left afterFirst firstValid firstRun).1.trans
    (sound fuel root second right afterSecond secondValid secondRun).1.symm

/-- All five actual selection workers return the same values from all valid shared count caches. -/
theorem selection_cacheLaw [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (size : Nat → Nat)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph size invariant) (fuel : Nat) :
    (∀ root path rank, CacheLaw invariant (selectAt graph order fuel root path rank)) ∧
    (∀ root path rank available, CacheLaw invariant (chooseConstructor graph order fuel root path rank available)) ∧
    (∀ root path rank indices, CacheLaw invariant (selectChildren graph order fuel root path rank indices)) ∧
    (∀ root path, CacheLaw invariant (selectUnique graph order fuel root path)) ∧
    (∀ root path available, CacheLaw invariant (uniqueConstructor graph order fuel root path available)) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro root path rank; exact cacheLaw_error invariant _
    · intro root path rank available; exact cacheLaw_error invariant _
    · intro root path rank indices
      cases indices with
      | nil => exact cacheLaw_pure invariant _
      | cons index rest => exact cacheLaw_error invariant _
    · intro root path; exact cacheLaw_error invariant _
    · intro root path available; exact cacheLaw_error invariant _
  | succ fuel ih =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro root path rank
      apply cacheLaw_bind invariant (countNode graph fuel (graph.project path root)) _
        (count_cacheLaw graph size invariant sound fuel (graph.project path root))
      intro count
      split
      · apply cacheLaw_bind invariant (isolated (selectUnique graph order fuel (graph.project path root) [])) _
          (cacheLaw_isolated invariant _ (ih.2.2.2.1 (graph.project path root) []))
        intro term
        exact cacheLaw_pure invariant _
      · exact ih.2.1 root path rank (constructorsAt graph order path root)
    · intro root path rank available
      cases available with
      | nil => exact cacheLaw_error invariant _
      | cons constructor rest =>
        apply cacheLaw_bind invariant (countNode graph fuel (graph.condition path constructor root)) _
          (count_cacheLaw graph size invariant sound fuel (graph.condition path constructor root))
        intro count
        split
        · exact ih.2.1 root path (rank - count) rest
        · apply cacheLaw_bind invariant (selectChildren graph order fuel (graph.condition path constructor root)
            path rank (List.range constructor.2)) _ (ih.2.2.1 _ path rank _)
          intro result
          exact cacheLaw_pure invariant _
    · intro root path rank indices
      cases indices with
      | nil => exact cacheLaw_pure invariant _
      | cons index rest =>
        apply cacheLaw_bind invariant (selectAt graph order fuel root (path ++ [index]) rank) _
          (ih.1 root (path ++ [index]) rank)
        intro result
        apply cacheLaw_bind invariant (selectChildren graph order fuel result.2.1 path result.2.2 rest) _
          (ih.2.2.1 result.2.1 path result.2.2 rest)
        intro remaining
        exact cacheLaw_pure invariant _
    · intro root path
      exact ih.2.2.2.2 root path (constructorsAt graph order path root)
    · intro root path available
      cases available with
      | nil => exact cacheLaw_error invariant _
      | cons constructor rest =>
        apply cacheLaw_bind invariant (countNode graph fuel (graph.condition path constructor root)) _
          (count_cacheLaw graph size invariant sound fuel (graph.condition path constructor root))
        intro count
        split
        · exact ih.2.2.2.2 root path rest
        · apply cacheLaw_bind invariant
            ((List.range constructor.2).mapM fun index => isolated (selectUnique graph order fuel root (path ++ [index])) :
              CountM Symbol (List (Language.Term Symbol))) _
            (cacheLaw_mapM invariant _ _ (fun index _ => cacheLaw_isolated invariant _ (ih.2.2.2.1 root (path ++ [index]))))
          intro children
          exact cacheLaw_pure invariant _

/-- The actual inverse result also ignores which valid count snapshot was read. -/
theorem ranking_cacheLaw [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (size : Nat → Nat)
    (invariant : Counts Symbol → Prop) (sound : CountSound graph size invariant) (fuel : Nat) :
    (∀ root path term before, CacheLaw invariant (rankAt graph order fuel root path term before)) ∧
    (∀ root path wanted children before available,
      CacheLaw invariant (rankConstructor graph order fuel root path wanted children before available)) ∧
    (∀ root path before children, CacheLaw invariant (rankChildren graph order fuel root path before children)) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro root path term before; exact cacheLaw_error invariant _
    · intro root path wanted children before available; exact cacheLaw_error invariant _
    · intro root path before children
      cases children with
      | nil => exact cacheLaw_pure invariant _
      | cons child rest => exact cacheLaw_error invariant _
  | succ fuel ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro root path term before
      cases term with
      | node symbol children =>
        apply cacheLaw_bind invariant (countNode graph fuel (graph.project path root)) _
          (count_cacheLaw graph size invariant sound fuel (graph.project path root))
        intro count
        split
        · apply cacheLaw_bind invariant (isolated (selectUnique graph order fuel (graph.project path root) [])) _
            (cacheLaw_isolated invariant _ ((selection_cacheLaw graph order size invariant sound fuel).2.2.2.1 _ _))
          intro unique
          exact cacheLaw_pure invariant _
        · dsimp only
          split
          · exact ih.2.1 root path (symbol, children.length) children before (constructorsAt graph order path root)
          · exact cacheLaw_pure invariant _
    · intro root path wanted children before available
      cases available with
      | nil => exact cacheLaw_pure invariant _
      | cons constructor rest =>
        apply cacheLaw_bind invariant (countNode graph fuel (graph.condition path constructor root)) _
          (count_cacheLaw graph size invariant sound fuel (graph.condition path constructor root))
        intro count
        split
        · split
          · exact cacheLaw_pure invariant _
          · exact ih.2.2 (graph.condition path constructor root) path before children.zipIdx
        · exact ih.2.1 root path wanted children (before + count) rest
    · intro root path before children
      cases children with
      | nil => exact cacheLaw_pure invariant _
      | cons child rest =>
        rcases child with ⟨term, index⟩
        apply cacheLaw_bind invariant (rankAt graph order fuel root (path ++ [index]) term before) _
          (ih.1 root (path ++ [index]) term before)
        intro result
        cases result with
        | none => exact cacheLaw_pure invariant _
        | some pair => exact ih.2.2 pair.1 path pair.2 rest

/-- Stable eventual results from two valid snapshots have the same observed value. -/
theorem eventual_cache_independent (invariant : State → Prop)
    (action : Nat → StateT State (Except Failure) Value)
    (law : ∀ fuel, CacheLaw invariant (action fuel))
    (first second : State) (firstValid : invariant first) (secondValid : invariant second)
    (firstBound secondBound : Nat) (left right : Value) (afterFirst afterSecond : State)
    (firstStable : ∀ fuel, firstBound ≤ fuel → action fuel first = .ok (left, afterFirst))
    (secondStable : ∀ fuel, secondBound ≤ fuel → action fuel second = .ok (right, afterSecond)) : left = right :=
  (law (max firstBound secondBound)).observes first second left right afterFirst afterSecond
    firstValid secondValid (firstStable _ (Nat.le_max_left _ _)) (secondStable _ (Nat.le_max_right _ _))

/-- Shared state remembers each immutable snapshot that a query has read. -/
structure SharedCache (State : Type) where
  current : State
  snapshots : List State := []

/-- The published cache and every captured snapshot satisfy the semantic count invariant. -/
def SharedValid (invariant : State → Prop) (shared : SharedCache State) : Prop :=
  invariant shared.current ∧ ∀ snapshot ∈ shared.snapshots, invariant snapshot

/-- Source reads capture the current cache; completed calls replace it with their own result cache. -/
inductive SharedStep (invariant : State → Prop) (Failure : Type) : SharedCache State → SharedCache State → Prop where
  | read (shared : SharedCache State) : SharedStep invariant Failure shared
      {shared with snapshots := shared.current :: shared.snapshots}
  | publish (shared : SharedCache State) (snapshot : State) (readEarlier : snapshot ∈ shared.snapshots)
      (action : StateT State (Except Failure) Value) (law : CacheLaw invariant action)
      (result : Value) (grown : State) (completed : action snapshot = .ok (result, grown)) :
      SharedStep invariant Failure shared {shared with current := grown}

/-- A stale publication can discard computed entries but cannot publish an incorrect count. -/
theorem sharedStep_valid (invariant : State → Prop) (first second : SharedCache State)
    (valid : SharedValid invariant first) (step : SharedStep invariant Failure first second) : SharedValid invariant second := by
  cases step with
  | read =>
    refine ⟨valid.1, ?_⟩
    intro snapshot member
    rcases List.mem_cons.mp member with rfl | member
    · exact valid.1
    · exact valid.2 snapshot member
  | publish shared snapshot present action law result grown completed =>
    exact ⟨law.preserves snapshot result grown (valid.2 snapshot present) completed, valid.2⟩

/-- A finite interleaving of source reads and atomic whole-cache replacements. -/
inductive SharedHistory (invariant : State → Prop) (Failure : Type) : SharedCache State → SharedCache State → Prop where
  | refl (shared : SharedCache State) : SharedHistory invariant Failure shared shared
  | step (history : SharedHistory invariant Failure initial before) (next : SharedStep invariant Failure before after) :
      SharedHistory invariant Failure initial after

/-- All finite source cache interleavings retain valid published and captured snapshots. -/
theorem sharedHistory_valid (invariant : State → Prop) (initial finalState : SharedCache State)
    (valid : SharedValid invariant initial) (history : SharedHistory invariant Failure initial finalState) :
    SharedValid invariant finalState := by
  induction history with
  | refl => exact valid
  | step _ next ih => exact sharedStep_valid invariant _ _ ih next

/-- Identical queries read at different points in an interleaving return identical results. -/
theorem shared_reads_agree (invariant : State → Prop) (shared : SharedCache State)
    (valid : SharedValid invariant shared) (first second : State)
    (firstRead : first ∈ shared.snapshots) (secondRead : second ∈ shared.snapshots)
    (action : StateT State (Except Failure) Value) (law : CacheLaw invariant action)
    (left right : Value) (afterFirst afterSecond : State)
    (firstCompleted : action first = .ok (left, afterFirst))
    (secondCompleted : action second = .ok (right, afterSecond)) : left = right :=
  law.observes first second left right afterFirst afterSecond (valid.2 first firstRead) (valid.2 second secondRead)
    firstCompleted secondCompleted

end MicroCFTA.SymbolicDriver
