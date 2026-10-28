import MicroCFTA.SourcePruningEnumerationPreparedIncomingIsolation
import MicroCFTA.SourcePruningEnumerationTerminalProper

/-!
# Isolation through an actual terminal singleton

The prefix excludes the original isolated class from every selected root.
The fold and incoming receipts retain that class at the actual returned row.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminal
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationSemantics EnumerationDischargeHistory
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] terminalMonadList

/-- The actual successful terminal row retains an original isolated class outside its inputs. -/
theorem successful_isolated
    (checkEmpty : Bool) (r n p h : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (caller : Caller width) (before : Core)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (fragment : Fragment) (afterCaller : Caller width) (savedQueries : Queries)
    (outer after : Core) (moved : EnumerationWaitingIndex.Waiting)
    (held heldHandle : Nat) (total : UnionFind.Total before.representatives)
    (isolated : IsolatedPending held heldHandle before)
    (active : Avoids before.representatives held (first :: rest))
    (inputs : Avoids before.representatives held incomingScs)
    (observed : run checkEmpty r n p h first rest waiting caller before incoming incomingScs queries =
      (.ok (some [.ok (fragment, after)]), afterCaller, savedQueries, outer, moved)) : IsolatedPending held heldHandle after := by
  unfold run at observed
  split at observed
  next empty => cases observed
  next nonempty =>
    split at observed
    next recorded winner transfer joined prefixObserved =>
      have prefixSuccess : Success (SourcePruningEnumerationTerminalPrefix.run r first rest waiting)
          before (recorded, winner, transfer) joined := by
        rw [Success, prefixObserved]
        exact List.mem_singleton_self _
      have joinedFacts := SourcePruningEnumerationTerminalPrefix.run_isolated r held heldHandle first rest waiting
        before joined recorded winner transfer total isolated active prefixSuccess
      rcases foldObserved : SourcePruningEnumerationFold.run checkEmpty n p h recorded caller joined winner queries with
        ⟨foldResult, foldCaller, foldQueries, foldOuter⟩
      rw [foldObserved] at observed
      have winnerOther : winner ≠ held := by
        intro same
        subst winner
        exact joinedFacts.2.2.2.1 (⟨held, joinedFacts.2.1.root.choose, joinedFacts.2.1.root.choose_spec, joinedFacts.2.1.root.choose_spec⟩)
      have foldFacts := SourcePruningEnumerationFold.run_isolated checkEmpty n p h recorded caller joined
        winner queries foldResult foldCaller foldQueries foldOuter held heldHandle joinedFacts.2.1
        joinedFacts.2.2.1 winnerOther foldObserved
      cases foldResult with
      | error fault => cases observed
      | ok possible =>
        cases possible with
        | none => cases observed
        | some raw =>
          dsimp only at observed
          split at observed
          next empty => cases observed
          next folded =>
            have foldedSame := SourcePruningEnumerationFold.singleton_core checkEmpty n p h recorded
              caller joined winner queries folded foldCaller foldQueries foldOuter foldObserved
            have foldedIsolated : IsolatedPending held heldHandle folded := by
              simpa only [foldedSame] using foldFacts.1
            have foldedForest : folded.representatives = joined.representatives := by
              simpa only [foldedSame] using foldFacts.2
            have foldedTotal : UnionFind.Total folded.representatives := by
              rw [foldedForest]
              exact joinedFacts.1
            have separate : ¬UnionFind.SameClass folded.representatives held winner := by
              rw [foldedForest]
              exact joinedFacts.2.2.2.1
            have incomingInputs : Avoids folded.representatives held incomingScs := by
              intro sc member related
              rw [foldedForest] at related
              exact inputs sc member ((joinedFacts.2.2.2.2 sc.var).mp related)
            have incomingFacts := SourcePruningEnumerationIncomingNode.run_isolated checkEmpty r n p h
              foldCaller folded winner incoming incomingScs foldQueries held heldHandle foldedTotal
              foldedIsolated separate incomingInputs
            rcases incomingObserved : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
                foldCaller folded winner incoming incomingScs foldQueries with
              ⟨incomingResult, reached, saved, read⟩
            rw [incomingObserved] at observed incomingFacts
            cases incomingResult with
            | error fault => cases observed
            | ok result =>
              cases result with
              | none => cases observed
              | some incomingRaw =>
                have rowsSame := congrArg Prod.fst observed
                dsimp only at rowsSame
                have mapped := Option.some.inj (Except.ok.inj rowsSame)
                have single : incomingRaw = [.ok ((), after)] := by
                  cases incomingRaw with
                  | nil => cases mapped
                  | cons row rest =>
                    cases row with
                    | error error => cases mapped
                    | ok value =>
                      rcases value with ⟨⟨⟩, returned⟩
                      have fields := List.cons.inj mapped
                      have coreSame : returned = after := (Prod.mk.inj (Except.ok.inj fields.1)).2
                      have restEmpty : rest = [] := List.map_eq_nil_iff.mp fields.2
                      simp only [coreSame, restEmpty]
                exact (incomingFacts.2 after (by rw [single])).2
          next other => cases observed
    next other => cases observed

end MicroCFTA.SourcePruningEnumerationTerminal
