import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
import MicroCFTA.SourcePruningEnumerationSuspendedMass

/-!
# Suspended mass at actual incoming observations

The original action returns its read core separately from its raw rows.
A successful row or recovered Empty cache retains the completed write.
These numerical bounds assert no safety or native postcondition.
-/
namespace MicroCFTA.SourcePruningEnumerationIncomingNode
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationPrefixAdmission (suspendedBound suspendedBound_values)
open SourcePruningEnumerationSuspendedMass (incoming_mass)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
attribute [local instance] SourcePruningEnumerationIncomingNode.incomingNodeMonadList

private theorem finish_singleton_mass
    {before returned : Core} {target handle : Nat} {oldNode : Option Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (observed : ExceptT.run (finish target handle incomingScs oldScs replacement before) =
      [.ok ((), returned)]) :
    returned.counter = before.counter ∧
      suspendedBound returned = suspendedBound before + incomingScs.length := by
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
  exact ⟨rfl, incoming_mass before target oldNode (some handle) incomingScs oldScs stored⟩

private theorem finish_reply_mass
    {Fault : Type} {before returned : Core} {target handle : Nat} {oldNode : Option Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (observed : (Except.ok (some (ExceptT.run
        (finish target handle incomingScs oldScs replacement before))) : Except Fault (Option Raw)) =
      .ok (some [.ok ((), returned)])) :
    returned.counter = before.counter ∧
      suspendedBound returned = suspendedBound before + incomingScs.length :=
  finish_singleton_mass stored (Option.some.inj (Except.ok.inj observed))

variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every observed read retains the original values and counter, including errors and unsupported results. -/
theorem run_mass
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    let observed := run checkEmpty r n p h caller before target incoming incomingScs queries
    observed.2.2.2.counter = before.counter ∧ observed.2.2.2.values = before.values ∧
      ∀ returned, observed.1 = .ok (some [.ok ((), returned)]) →
        returned.counter = before.counter ∧
          suspendedBound returned = suspendedBound before + incomingScs.length := by
  generalize observedEq : run checkEmpty r n p h caller before target incoming incomingScs queries = observed
  obtain ⟨result, reachedCaller, savedQueries, read⟩ := observed
  dsimp only
  unfold run at observedEq
  split at observedEq
  next =>
    simp only [Prod.mk.injEq] at observedEq
    rcases observedEq with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨rfl, rfl, ?_⟩
    intro returned singleton
    simp at singleton
  next =>
    repeat' first
      | (simp only [Prod.mk.injEq] at observedEq
         rcases observedEq with ⟨rfl, rfl, rfl, rfl⟩
         refine ⟨rfl, rfl, ?_⟩
         intro returned singleton
         solve
         | simp at singleton
         | have mass := finish_reply_mass (by assumption) singleton
           exact mass)
      | split at observedEq

end MicroCFTA.SourcePruningEnumerationIncomingNode

namespace MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationPrefixAdmission (suspendedBound suspendedBound_values)
open SourcePruningEnumerationSuspendedMass (incoming_mass)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))

private theorem adapt_mass
    {heap : InternedConstructorTemplates.State Symbol Constraint} {indexFuel target : Nat}
    {incomingScs : List Suspended} {before after : Cached} {read : Core} {raw : Raw}
    (readCounter : read.counter = before.core.counter)
    (readValues : read.values = before.core.values)
    (rows : ∀ returned, raw = [.ok ((), returned)] →
      returned.counter = before.core.counter ∧
        suspendedBound returned = suspendedBound before.core + incomingScs.length)
    (adapted : adapt heap indexFuel target incomingScs before read raw = some after) :
    after.core.counter = before.core.counter ∧
      suspendedBound after.core = suspendedBound before.core + incomingScs.length := by
  cases raw with
  | nil =>
      simp only [adapt] at adapted
      split at adapted
      · rename_i oldNode oldScs stored
        simp only [Option.map_eq_some_iff] at adapted
        obtain ⟨written, _written, same⟩ := adapted
        subst after
        have mass := incoming_mass read target oldNode (some 0) incomingScs oldScs stored
        have original := suspendedBound_values before.core read readValues
        exact ⟨readCounter, mass.trans
          (congrArg (fun bound => bound + incomingScs.length) original)⟩
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

/-- Every attached cache has exact incoming mass, including a recovered Empty rejection. -/
theorem observed_cache_bounds
    (checkEmpty : Bool) (r n p h k : Nat) (caller : Caller width) (before : Cached)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (after : Cached)
    (candidate : (run checkEmpty r n p h k caller before target incoming incomingScs queries).2 = some after) :
    after.core.counter = before.core.counter ∧
      suspendedBound after.core = suspendedBound before.core + incomingScs.length := by
  have fields := SourcePruningEnumerationIncomingNode.run_mass
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
          apply adapt_mass fields.1 fields.2.1 ?_ candidate
          intro returned rawSame
          exact fields.2.2 returned (by rw [rawSame])

end MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter

namespace MicroCFTA.SourcePruningEnumerationCachedIncoming
open EnumerationState
open SourcePruningEnumerationPrefixAdmission (suspendedBound suspendedBound_values)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint

/-- The actual completed write has exact incoming mass even when its raw continuation rejects. -/
theorem written_mass
    (before read after : Core) (target handle : Nat) (oldNode : Option Nat)
    (incomingScs oldScs : List Suspended)
    (frame : EnumerationCompressionFrame.Frame before read)
    (stored : read.values[target]? = some (.unenumerated oldNode oldScs))
    (shape : after = {read with
      values := read.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (read.expansionAncestry ++ read.recursionAncestry target).eraseDups
        else read.recursionAncestry other}) :
    after.counter = before.counter ∧
      suspendedBound after = suspendedBound before + incomingScs.length := by
  rw [shape]
  exact ⟨frame.counter,
    (SourcePruningEnumerationSuspendedMass.incoming_mass read target oldNode (some handle)
      incomingScs oldScs stored).trans (congrArg (fun bound => bound + incomingScs.length)
        (suspendedBound_values before read frame.values))⟩

end MicroCFTA.SourcePruningEnumerationCachedIncoming
