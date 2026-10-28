import MicroCFTA.SourcePruningEnumerationPreparedTerminalIsolationOperations
import MicroCFTA.SourcePruningEnumerationIncomingCarriers

/-!
# Isolation at actual incoming rows

The raw native request does not change the enumeration cache.
The actual reached representative differs from the isolated class.
The successful write uses only old references and incoming references.
-/
namespace MicroCFTA.SourcePruningEnumerationIncomingNode
open EnumerationState EnumerationSchedule EnumerationCorrectness EnumerationCompressionFrame
open EnumerationReferences EnumerationDischargeHistory InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
attribute [local instance] SourcePruningEnumerationIncomingNode.incomingNodeMonadList

/-- The explicit different-slot write retains the original isolated root. -/
theorem written_isolated
    (before after : Core) (target handle held heldHandle : Nat) (oldNode : Option Nat)
    (incomingScs oldScs : List Suspended)
    (total : UnionFind.Total before.representatives)
    (isolated : IsolatedPending held heldHandle before)
    (different : target ≠ held) (inputs : Avoids before.representatives held incomingScs)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (shape : after = {before with
      values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
        else before.recursionAncestry other}) :
    UnionFind.Total after.representatives ∧ IsolatedPending held heldHandle after := by
  subst after
  refine ⟨total, ⟨isolated.root, ?_, ?_⟩⟩
  · simpa only [List.getElem?_set_ne different] using isolated.stored
  · exact SourcePruningEnumerationNativeReferences.incoming_written
      (fun uv => ¬UnionFind.SameClass before.representatives held uv)
      before _ target handle oldNode incomingScs oldScs isolated.incoming inputs stored rfl

private theorem finish_singleton_isolated
    {before returned : Core} {target handle held heldHandle : Nat} {oldNode : Option Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (total : UnionFind.Total before.representatives)
    (isolated : IsolatedPending held heldHandle before)
    (different : target ≠ held) (inputs : Avoids before.representatives held incomingScs)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (observed : ExceptT.run (finish target handle incomingScs oldScs replacement before) =
      [.ok ((), returned)]) :
    UnionFind.Total returned.representatives ∧ IsolatedPending held heldHandle returned := by
  let written : Core :=
    {before with
      values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
        else before.recursionAncestry other}
  have rawRun : ExceptT.run (finish target handle incomingScs oldScs replacement before) =
      match replacement with
      | .empty => []
      | _ => [.ok ((), written)] := by
    cases replacement <;> rfl
  rw [rawRun] at observed
  have coreSame : written = returned := by
    split at observed
    · cases observed
    · exact (Prod.mk.inj (Except.ok.inj (List.cons.inj observed).1)).2
  exact written_isolated before returned target handle held heldHandle oldNode incomingScs oldScs
    total isolated different inputs stored coreSame.symm

private theorem finish_reply_isolated
    {Fault : Type _} {before returned : Core} {target handle held heldHandle : Nat} {oldNode : Option Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (total : UnionFind.Total before.representatives)
    (isolated : IsolatedPending held heldHandle before)
    (different : target ≠ held) (inputs : Avoids before.representatives held incomingScs)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (observed : (Except.ok (some (ExceptT.run
        (finish target handle incomingScs oldScs replacement before))) : Except Fault (Option Raw)) =
      .ok (some [.ok ((), returned)])) :
    UnionFind.Total returned.representatives ∧ IsolatedPending held heldHandle returned :=
  finish_singleton_isolated total isolated different inputs stored (Option.some.inj (Except.ok.inj observed))

variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual incoming singleton retains the original isolated slot in a separate class. -/
theorem run_isolated
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (held heldHandle : Nat) (total : UnionFind.Total before.representatives)
    (isolated : IsolatedPending held heldHandle before)
    (separate : ¬UnionFind.SameClass before.representatives held target)
    (inputs : Avoids before.representatives held incomingScs) :
    (UnionFind.Total (run checkEmpty r n p h caller before target incoming incomingScs queries).2.2.2.representatives ∧
      IsolatedPending held heldHandle
        (run checkEmpty r n p h caller before target incoming incomingScs queries).2.2.2) ∧
      ∀ returned, (run checkEmpty r n p h caller before target incoming incomingScs queries).1 =
        .ok (some [.ok ((), returned)]) →
        UnionFind.Total returned.representatives ∧ IsolatedPending held heldHandle returned := by
  generalize observedEq : run checkEmpty r n p h caller before target incoming incomingScs queries = observed
  obtain ⟨result, reachedCaller, savedQueries, read⟩ := observed
  dsimp only
  unfold run at observedEq
  cases lookup : UnionFind.findRoot r before.representatives target with
  | none =>
      simp only [lookup, Prod.mk.injEq] at observedEq
      rcases observedEq with ⟨rfl, rfl, rfl, rfl⟩
      refine ⟨⟨total, isolated⟩, ?_⟩
      intro returned singleton
      simp at singleton
  | some found =>
      simp only [lookup] at observedEq
      have frame : Frame before {before with representatives := found.forest} := by
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
        intro other root size
        exact UnionFind.findRoot_reaches_iff total lookup other root size
      have different : found.representative ≠ held :=
        representative_away before.representatives r target held separate found lookup
      have readIsolated := isolated.through_frame frame
      have readInputs : Avoids found.forest held incomingScs := by
        intro sc member related
        exact inputs sc member ((SourcePruningEnumerationNativeLanguage.frame_sameClass
          before _ frame held sc.var).mp related)
      repeat' first
        | (have readSame := congrArg (fun observed : _ × Caller width × Queries × Core => observed.2.2.2) observedEq
           have resultSame := congrArg Prod.fst observedEq
           dsimp only at readSame resultSame
           constructor
           · rw [← readSame]
             exact ⟨frame.total total, readIsolated⟩
           · intro returned singleton
             rw [← resultSame] at singleton
             solve
             | simp at singleton
             | exact finish_reply_isolated (frame.total total) readIsolated different readInputs
                 (by assumption) singleton)
        | split at observedEq

end MicroCFTA.SourcePruningEnumerationIncomingNode
