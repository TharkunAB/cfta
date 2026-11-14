import MicroCFTA.SourcePruningEnumerationSharedChildRawTargets
import MicroCFTA.SourceCurrentAllocatedPartialInvariant

/-!
# The shared prefix and fold at a fresh singleton goal terminal

The actual singleton prefix publishes the fresh root.
It performs no union with another variable and preserves the unbound slot.
The actual shared fold then dispatches the same source and target.
The complete caller and query memo remain unchanged.
The source fresh-slot producer supplies the two entry slot facts.
-/
namespace MicroCFTA.SourceSynthesisCurrentSharedGoalSingletonPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
attribute [local instance] SourcePruningEnumerationTerminalPrefix.terminalPrefixMonadList
  SourcePruningEnumerationTerminalPrefix.terminalPrefixLawfulMonadList

set_option autoImplicit false

private theorem singleton_prefix_endpoints
    (fuel uv : Nat) (before joined : Core) (waiting moved : EnumerationWaitingIndex.Waiting)
    (recorded : List Nat) (winner : Nat)
    (missing : before.representatives uv = none)
    (actual : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
      fuel ⟨.terminal, uv⟩ [] waiting before) = [.ok ((recorded, winner, moved), joined)]) :
    0 < fuel ∧ recorded = [uv] ∧ winner = uv ∧ moved = waiting ∧
      joined = {before with representatives := UnionFind.put before.representatives uv (.root 1)} := by
  have success : Success (SourcePruningEnumerationTerminalPrefix.run
      fuel ⟨.terminal, uv⟩ [] waiting) before (recorded, winner, moved) joined := by
    rw [Success, actual]
    exact List.mem_singleton_self _
  unfold SourcePruningEnumerationTerminalPrefix.run at success
  obtain ⟨actualRecorded, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
  rw [List.mapM_cons] at scanning
  obtain ⟨head, headAfter, headStep, scanningTail⟩ := (success_bind _ _ _ _ _).mp scanning
  obtain ⟨tail, tailAfter, tailStep, scanPure⟩ := (success_bind _ _ _ _ _).mp scanningTail
  have tailPure : Success (pure ([] : List Nat)) headAfter tail tailAfter := by
    simpa only [List.mapM_nil] using tailStep
  obtain ⟨tailSame, tailAfterSame⟩ := (success_pure [] tail headAfter tailAfter).mp tailPure
  subst tail
  subst tailAfter
  obtain ⟨recordedSame, scannedSame⟩ :=
    (success_pure [head] actualRecorded headAfter scanned).mp scanPure
  subst actualRecorded
  subst scanned
  obtain ⟨found, lookup, headSame, headAfterSame⟩ :=
    (representative_success fuel uv before headAfter head).mp headStep
  cases fuel with
  | zero =>
      simp only [UnionFind.findRoot] at lookup
      cases lookup
  | succ smaller =>
      have expected : UnionFind.findRoot (smaller + 1) before.representatives uv =
          some ⟨uv, 1, UnionFind.put before.representatives uv (.root 1)⟩ := by
        simp only [UnionFind.findRoot, missing]
      have foundSame : found = ⟨uv, 1, UnionFind.put before.representatives uv (.root 1)⟩ :=
        Option.some.inj (lookup.symm.trans expected)
      subst found
      subst head
      subst headAfter
      let published : Core := {before with representatives := UnionFind.put before.representatives uv (.root 1)}
      obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
      have unitedSame : published = united := ((success_pure _ _ _ _).mp unions).2
      subst united
      obtain ⟨actualWinner, resolved, resolution, final⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨lastFound, lastLookup, winnerSame, resolvedSame⟩ :=
        (representative_success (smaller + 1) uv published resolved actualWinner).mp resolution
      have publishedRead : published.representatives uv = some (.root 1) := by
        simp only [published, UnionFind.put, ↓reduceIte]
      have lastExpected : UnionFind.findRoot (smaller + 1) published.representatives uv =
          some ⟨uv, 1, published.representatives⟩ := by
        simp only [UnionFind.findRoot, publishedRead]
      have lastSame : lastFound = ⟨uv, 1, published.representatives⟩ :=
        Option.some.inj (lastLookup.symm.trans lastExpected)
      subst lastFound
      subst actualWinner
      have resolvedPublished : resolved = published := resolvedSame
      subst resolved
      have finalSame := (success_pure
        ([uv], uv, EnumerationCanonicalWaiting.moveMany uv
          (EnumerationBuilderCaches.canonicalIds ([uv].filter (fun key => key != uv))) waiting)
        (recorded, winner, moved) published joined).mp final
      have sameWaiting : EnumerationCanonicalWaiting.moveMany uv
          (EnumerationBuilderCaches.canonicalIds ([uv].filter (fun key => key != uv))) waiting = waiting := by
        simp [EnumerationBuilderCaches.canonicalIds, EnumerationCanonicalWaiting.moveMany]
      have tupleSame : ([uv], uv, waiting) = (recorded, winner, moved) := by
        simpa only [sameWaiting] using finalSame.1
      exact ⟨Nat.zero_lt_succ smaller,
        (congrArg (fun result => result.1) tupleSame).symm,
        (congrArg (fun result => result.2.1) tupleSame).symm,
        (congrArg (fun result => result.2.2) tupleSame).symm, finalSame.2.symm⟩

/-- An observed singleton prefix derives the shared no-op fold and the next unbound incoming read. -/
theorem singleton_goal_prefix_shared_fold
    {width : Nat}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (checkEmpty : Bool) (fuel nativeFuel p h uv : Nat)
    (before joined : Core) (waiting moved : EnumerationWaitingIndex.Waiting)
    (recorded : List Nat) (winner : Nat) (queries : Queries)
    (missing : before.representatives uv = none)
    (slot : before.values[uv]? = some (.unenumerated none []))
    (actual : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
      fuel ⟨.terminal, uv⟩ [] waiting before) = [.ok ((recorded, winner, moved), joined)]) :
    ∃ found : UnionFind.Result,
      recorded = [uv] ∧ winner = uv ∧ moved = waiting ∧
      joined = {before with representatives := UnionFind.put before.representatives uv (.root 1)} ∧
      SourcePruningEnumerationSharedCachedTerminal.rawFold
        checkEmpty nativeFuel p h recorded caller joined winner queries =
          (.ok (some [.ok ((), joined)]), caller, queries, joined) ∧
      UnionFind.findRoot fuel joined.representatives winner = some found ∧
      found.representative = uv ∧ found.forest = joined.representatives ∧
      joined.values[found.representative]? = some (.unenumerated none []) ∧
      Context formulas solver inventory caller memos := by
  obtain ⟨positive, recordedSame, winnerSame, movedSame, joinedSame⟩ :=
    singleton_prefix_endpoints fuel uv before joined waiting moved recorded winner missing actual
  have foldExact : SourcePruningEnumerationSharedCachedTerminal.rawFold
      checkEmpty nativeFuel p h recorded caller joined winner queries =
      (.ok (some [.ok ((), joined)]), caller, queries, joined) := by
    rw [recordedSame, winnerSame]
    simp [SourcePruningEnumerationSharedCachedTerminal.rawFold,
      SourcePruningEnumerationSharedDispatch.dispatch]
  let found : UnionFind.Result := ⟨uv, 1, joined.representatives⟩
  have rootRead : joined.representatives uv = some (.root 1) := by
    rw [joinedSame]
    simp only [UnionFind.put, ↓reduceIte]
  have reading : UnionFind.findRoot fuel joined.representatives winner = some found := by
    rw [winnerSame]
    cases fuel with
    | zero => omega
    | succ smaller => simp only [UnionFind.findRoot, rootRead]; rfl
  have unbound : joined.values[found.representative]? = some (.unenumerated none []) := by
    change joined.values[uv]? = some (.unenumerated none [])
    rw [joinedSame]
    exact slot
  exact ⟨found, recordedSame, winnerSame, movedSame, joinedSame, foldExact,
    reading, rfl, rfl, unbound, initial⟩

end MicroCFTA.SourceSynthesisCurrentSharedGoalSingletonPrefix
