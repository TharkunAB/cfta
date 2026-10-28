import MicroCFTA.SourcePruningEnumerationKeyAncestry
import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter

/-!
# Historical key shapes through actual incoming writes

The incoming read keeps both ancestry fields.
The completed write combines only old expansion and target keys.
The actual cache adapter retains this property in singleton and Empty rows.
-/
namespace MicroCFTA
open SourcePruningEnumerationKeyAncestry

private theorem incoming_written_key_ancestry
    {Symbol Guard : Type} {carrier : List (List (List (List Nat)))}
    (before : EnumerationState.State Symbol Guard) (target handle : Nat)
    (incomingScs oldScs : List EnumerationState.Suspended)
    (bounded : KeyAncestry carrier before) :
    KeyAncestry carrier {before with
      values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
        else before.recursionAncestry other} := by
  refine ⟨?_, bounded.2⟩
  intro slot key member
  change key ∈ (if slot = target then
    (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
    else before.recursionAncestry slot) at member
  by_cases current : slot = target
  · simp only [ite_eq_left current, List.mem_eraseDups, List.mem_append] at member
    exact member.elim (bounded.2 key) (bounded.1 target key)
  · exact bounded.1 slot key (by simpa only [ite_eq_right current] using member)

namespace SourcePruningEnumerationIncomingNode
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
attribute [local instance] incomingNodeMonadList

private theorem finish_singleton_key_ancestry
    {carrier : List (List (List (List Nat)))}
    {before returned : Core} {target handle : Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (bounded : KeyAncestry carrier before)
    (observed : ExceptT.run (finish target handle incomingScs oldScs replacement before) =
      [.ok ((), returned)]) : KeyAncestry carrier returned := by
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
  rw [← coreSame]
  exact incoming_written_key_ancestry before target handle incomingScs oldScs bounded

private theorem finish_reply_key_ancestry
    {Fault : Type _} {carrier : List (List (List (List Nat)))}
    {before returned : Core} {target handle : Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (bounded : KeyAncestry carrier before)
    (observed : (Except.ok (some (ExceptT.run
        (finish target handle incomingScs oldScs replacement before))) : Except Fault (Option Raw)) =
      .ok (some [.ok ((), returned)])) : KeyAncestry carrier returned :=
  finish_singleton_key_ancestry bounded (Option.some.inj (Except.ok.inj observed))

variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual read and successful singleton retains the original historical key carrier. -/
theorem run_key_ancestry
    {carrier : List (List (List (List Nat)))}
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (bounded : KeyAncestry carrier before) :
    KeyAncestry carrier (run checkEmpty r n p h caller before target incoming incomingScs queries).2.2.2 ∧
      ∀ returned, (run checkEmpty r n p h caller before target incoming incomingScs queries).1 =
        .ok (some [.ok ((), returned)]) → KeyAncestry carrier returned := by
  generalize observedEq : run checkEmpty r n p h caller before target incoming incomingScs queries = observed
  obtain ⟨result, reachedCaller, savedQueries, read⟩ := observed
  dsimp only
  unfold run at observedEq
  split at observedEq
  next =>
    simp only [Prod.mk.injEq] at observedEq
    rcases observedEq with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨bounded, ?_⟩
    intro returned singleton
    simp at singleton
  next =>
    repeat' first
      | (have readSame := congrArg (fun observed : _ × Caller width × Queries × Core => observed.2.2.2) observedEq
         have resultSame := congrArg Prod.fst observedEq
         dsimp only at readSame resultSame
         constructor
         · rw [← readSame]
           change KeyAncestry carrier before
           exact bounded
         · intro returned singleton
           rw [← resultSame] at singleton
           solve
           | simp at singleton
           | apply finish_reply_key_ancestry (observed := singleton)
             change KeyAncestry carrier before
             exact bounded)
      | split at observedEq
      | (dsimp only at observedEq; split at observedEq)

end SourcePruningEnumerationIncomingNode

namespace SourcePruningEnumerationIncomingCacheAdapter
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))

private theorem adapt_key_ancestry
    {carrier : List (List (List (List Nat)))}
    {heap : InternedConstructorTemplates.State Symbol Constraint} {indexFuel target : Nat}
    {incomingScs : List Suspended} {before after : Cached} {read : Core} {raw : Raw}
    (readBounded : KeyAncestry carrier read)
    (rows : ∀ returned, raw = [.ok ((), returned)] → KeyAncestry carrier returned)
    (adapted : adapt heap indexFuel target incomingScs before read raw = some after) :
    KeyAncestry carrier after.core := by
  cases raw with
  | nil =>
      simp only [adapt] at adapted
      split at adapted
      · rename_i oldNode oldScs stored
        simp only [Option.map_eq_some_iff] at adapted
        obtain ⟨written, _written, same⟩ := adapted
        subst after
        exact incoming_written_key_ancestry read target 0 incomingScs oldScs readBounded
      · cases adapted
  | cons row rest =>
      cases row with
      | error fault => simp only [adapt] at adapted; cases adapted
      | ok payload =>
          obtain ⟨⟨⟩, returned⟩ := payload
          cases rest with
          | nil =>
              have coreSame := adapt_singleton_core heap indexFuel target incomingScs
                before after read returned adapted
              simpa only [coreSame] using rows returned rfl
          | cons next later => simp only [adapt] at adapted; cases adapted

variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual attached cache retains its original ancestry carrier, including Empty rows. -/
theorem observed_cache_key_ancestry
    {carrier : List (List (List (List Nat)))}
    (checkEmpty : Bool) (r n p h k : Nat) (caller : Caller width) (before : Cached)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (bounded : KeyAncestry carrier before.core) (after : Cached)
    (candidate : (run checkEmpty r n p h k caller before target incoming incomingScs queries).2 = some after) :
    KeyAncestry carrier after.core := by
  have fields := SourcePruningEnumerationIncomingNode.run_key_ancestry
    checkEmpty r n p h caller before.core target incoming incomingScs queries bounded
  unfold run at candidate
  generalize original : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
    caller before.core target incoming incomingScs queries = observed at fields candidate
  obtain ⟨result, reached, saved, read⟩ := observed
  dsimp only at fields candidate
  cases result with
  | error fault => cases candidate
  | ok payload =>
      cases payload with
      | none => cases candidate
      | some raw =>
          apply adapt_key_ancestry fields.1 ?_ candidate
          intro returned rawSame
          exact fields.2 returned (by rw [rawSame])

end SourcePruningEnumerationIncomingCacheAdapter
end MicroCFTA
