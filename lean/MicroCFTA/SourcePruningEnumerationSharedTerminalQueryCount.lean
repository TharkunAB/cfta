import MicroCFTA.SourcePruningEnumerationSharedTerminalQueryEvents

/-!
# Query count from the literal terminal input

A successful prefix records one representative for each suspension.
The bound counts explicit intersection calls in the checked observer.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedTerminalQueryCount
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Waiting" => EnumerationWaitingIndex.Waiting
variable {width : Nat}

local instance queryCountMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance queryCountLawfulMonadList : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
    simp only [List.map_const']
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, pure]
  bind_pure_comp := by intros; simp [bind, pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; exact List.flatMap_assoc

private theorem representatives_length (fuel : Nat) (items : List Suspended)
    (before after : Core) (recorded : List Nat)
    (observed : Success (items.mapM fun sc => representative fuel sc.var) before recorded after) :
    recorded.length = items.length := by
  induction items generalizing before after recorded with
  | nil =>
      obtain ⟨same, _⟩ := (success_pure [] recorded before after).mp observed
      exact congrArg List.length same
  | cons sc items ih =>
      rw [List.mapM_cons] at observed
      obtain ⟨root, middle, _head, continued⟩ := (success_bind _ _ _ _ _).mp observed
      obtain ⟨tail, last, tailRun, finalPure⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨same, _⟩ := (success_pure (root :: tail) recorded last after).mp finalPure
      rw [same]
      simpa only [List.length_cons] using congrArg Nat.succ (ih middle last tail tailRun)

private theorem prefix_length (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : Waiting) (before after : Core) (recorded : List Nat) (winner : Nat) (moved : Waiting)
    (observed : Success (SourcePruningEnumerationTerminalPrefix.run fuel first rest waiting)
      before (recorded, winner, moved) after) : recorded.length = (first :: rest).length := by
  unfold SourcePruningEnumerationTerminalPrefix.run at observed
  obtain ⟨roots, scanned, scan, afterScan⟩ := (success_bind _ _ _ _ _).mp observed
  obtain ⟨_discarded, united, _unions, afterUnions⟩ := (success_bind _ _ _ _ _).mp afterScan
  obtain ⟨_actualWinner, _last, _rootRead, finalPure⟩ := (success_bind _ _ _ _ _).mp afterUnions
  obtain ⟨same, _⟩ := (success_pure _ _ _ _).mp finalPure
  have recordedSame := congrArg (fun result : List Nat × Nat × Waiting => result.1) same
  change recorded = roots at recordedSame
  rw [recordedSame]
  exact representatives_length fuel (first :: rest) before scanned roots scan

/-- Count the same checked observation without a prefix or count premise. -/
theorem run_query_count
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : Suspended) (rest : List Suspended) (caller : Caller width) (before : Cached)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    (SourcePruningEnumerationSharedTerminalQueryEvents.runObserved checkEmpty representativeFuel nativeFuel p h indexFuel
      first rest caller before incoming incomingScs queries).2.length ≤ rest.length + 2 := by
  have checked := SourcePruningEnumerationSharedTerminalQueryEvents.run_observe_exact checkEmpty representativeFuel nativeFuel p h indexFuel first rest caller before incoming incomingScs queries
  have small := checked.2.2.1
  generalize prefixEq : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run representativeFuel first rest before.waiting before.core) = prefixRows at small
  cases prefixRows with
  | nil =>
      simp only at small
      omega
  | cons firstRow tail =>
      cases firstRow with
      | error fault =>
          simp only at small
          omega
      | ok value =>
          rcases value with ⟨⟨recorded, winner, moved⟩, joined⟩
          cases tail with
          | cons next remaining =>
              simp only at small
              omega
          | nil =>
              simp only at small
              have actual : Success (SourcePruningEnumerationTerminalPrefix.run representativeFuel first rest before.waiting)
                  before.core (recorded, winner, moved) joined := by
                unfold Success
                rw [prefixEq]
                exact List.mem_singleton_self _
              have length := prefix_length representativeFuel first rest before.waiting before.core joined recorded winner moved actual
              have sizes : recorded.length = rest.length + 1 := by simpa only [List.length_cons] using length
              omega

end MicroCFTA.SourcePruningEnumerationSharedTerminalQueryCount
