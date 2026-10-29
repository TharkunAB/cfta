import MicroCFTA.SourcePruningEnumerationAncestryExtensionStorage
import MicroCFTA.SourcePruningEnumerationCachedAssimilationAncestry
import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter

/-!
# Recursion ancestry through actual incoming and assimilation writes

Incoming writes retain each target's old keys.
Every observed core and recovered cache retains exact expansion ancestry.
-/
namespace MicroCFTA
open SourcePruningEnumerationAncestryExtension

private theorem incoming_written_ancestry_extension
    {Symbol Guard : Type}
    (before : EnumerationState.State Symbol Guard) (target handle : Nat)
    (incomingScs oldScs : List EnumerationState.Suspended) :
    Extends before {before with
      values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
        else before.recursionAncestry other} ∧
      ({before with
        values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
        recursionAncestry := fun other => if other = target then
          (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
          else before.recursionAncestry other} : EnumerationState.State Symbol Guard).expansionAncestry =
        before.expansionAncestry := by
  constructor
  · intro slot key member
    change key ∈ (if slot = target then
      (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
      else before.recursionAncestry slot)
    by_cases current : slot = target
    · subst slot
      simp only [↓reduceIte, List.mem_eraseDups, List.mem_append]
      exact Or.inr member
    · simpa only [ite_eq_right current] using member
  · rfl

namespace SourcePruningEnumerationCachedAssimilation
open EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

/-- Actual assimilation extends all slots and retains exact expansion ancestry. -/
theorem finish_ancestry_extension
    {heap : InternedConstructorTemplates.State Symbol Constraint}
    {fuel source target : Nat} {merged : Option Nat}
    {sourceScs targetScs : List Suspended} {before after : Cached}
    {rows : List (Unit × Cached)}
    (observed : finish heap fuel source target merged sourceScs targetScs before =
      some (rows, after)) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry := by
  refine ⟨(finish_ancestry observed).1, ?_⟩
  by_cases rejected : merged = some 0
  · rw [finish, ite_eq_left rejected] at observed
    have afterSame : before = after := congrArg Prod.snd (Option.some.inj observed)
    rw [← afterSame]
  · unfold finish at observed
    rw [ite_eq_right rejected] at observed
    obtain ⟨targetAfter, targetWritten, observed⟩ := Option.bind_eq_some_iff.mp observed
    obtain ⟨sourceAfter, sourceWritten, rowsSame⟩ := Option.map_eq_some_iff.mp observed
    have first := SourcePruningEnumerationNativeIndex.write_ancestry_extension targetWritten
    have second := SourcePruningEnumerationNativeIndex.write_ancestry_extension sourceWritten
    have expansionSame : sourceAfter.core.expansionAncestry = after.core.expansionAncestry :=
      congrArg (fun result : List (Unit × Cached) × Cached => result.2.core.expansionAncestry) rowsSame
    exact expansionSame.symm.trans (second.2.trans first.2)

end SourcePruningEnumerationCachedAssimilation

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

private theorem finish_singleton_ancestry_extension
    {before returned : Core} {target handle : Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (observed : ExceptT.run (finish target handle incomingScs oldScs replacement before) =
      [.ok ((), returned)]) :
    Extends before returned ∧ returned.expansionAncestry = before.expansionAncestry := by
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
  exact incoming_written_ancestry_extension before target handle incomingScs oldScs

private theorem finish_reply_ancestry_extension
    {Fault : Type _}
    {before returned : Core} {target handle : Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (observed : (Except.ok (some (ExceptT.run
        (finish target handle incomingScs oldScs replacement before))) : Except Fault (Option Raw)) =
      .ok (some [.ok ((), returned)])) :
    Extends before returned ∧ returned.expansionAncestry = before.expansionAncestry :=
  finish_singleton_ancestry_extension (Option.some.inj (Except.ok.inj observed))

variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual read core and successful singleton extends all slots and retains expansion ancestry. -/
theorem run_ancestry_extension
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    (Extends before (run checkEmpty r n p h caller before target incoming incomingScs queries).2.2.2 ∧
      (run checkEmpty r n p h caller before target incoming incomingScs queries).2.2.2.expansionAncestry =
        before.expansionAncestry) ∧
      ∀ returned, (run checkEmpty r n p h caller before target incoming incomingScs queries).1 =
        .ok (some [.ok ((), returned)]) →
          Extends before returned ∧ returned.expansionAncestry = before.expansionAncestry := by
  generalize observedEq : run checkEmpty r n p h caller before target incoming incomingScs queries = observed
  obtain ⟨result, reachedCaller, savedQueries, read⟩ := observed
  dsimp only
  unfold run at observedEq
  split at observedEq
  next =>
    simp only [Prod.mk.injEq] at observedEq
    rcases observedEq with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨⟨Extends.refl before, rfl⟩, ?_⟩
    intro returned singleton
    simp at singleton
  next =>
    repeat' first
      | (have readSame := congrArg (fun observed : _ × Caller width × Queries × Core => observed.2.2.2) observedEq
         have resultSame := congrArg Prod.fst observedEq
         dsimp only at readSame resultSame
         constructor
         · rw [← readSame]
           exact ⟨Extends.refl before, rfl⟩
         · intro returned singleton
           rw [← resultSame] at singleton
           solve
           | simp at singleton
           | (have finished := finish_reply_ancestry_extension singleton
              exact finished))
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

private theorem adapt_ancestry_extension
    {heap : InternedConstructorTemplates.State Symbol Constraint} {indexFuel target : Nat}
    {incomingScs : List Suspended} {before after : Cached} {origin read : Core} {raw : Raw}
    (readFields : Extends origin read ∧ read.expansionAncestry = origin.expansionAncestry)
    (rows : ∀ returned, raw = [.ok ((), returned)] →
      Extends origin returned ∧ returned.expansionAncestry = origin.expansionAncestry)
    (adapted : adapt heap indexFuel target incomingScs before read raw = some after) :
    Extends origin after.core ∧ after.core.expansionAncestry = origin.expansionAncestry := by
  cases raw with
  | nil =>
      simp only [adapt] at adapted
      split at adapted
      · rename_i oldNode oldScs stored
        simp only [Option.map_eq_some_iff] at adapted
        obtain ⟨written, _written, same⟩ := adapted
        subst after
        have inherited := incoming_written_ancestry_extension read target 0 incomingScs oldScs
        exact ⟨readFields.1.trans inherited.1, inherited.2.trans readFields.2⟩
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

/-- Every actual incoming cache candidate extends all slots, including Empty rows. -/
theorem observed_cache_ancestry_extension
    (checkEmpty : Bool) (r n p h k : Nat) (caller : Caller width) (before : Cached)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (after : Cached)
    (candidate : (run checkEmpty r n p h k caller before target incoming incomingScs queries).2 = some after) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry := by
  have fields := SourcePruningEnumerationIncomingNode.run_ancestry_extension
    checkEmpty r n p h caller before.core target incoming incomingScs queries
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
          apply adapt_ancestry_extension fields.1 ?_ candidate
          intro returned rawSame
          exact fields.2 returned (by rw [rawSame])

end SourcePruningEnumerationIncomingCacheAdapter
end MicroCFTA
