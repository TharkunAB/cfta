import MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
import MicroCFTA.SourcePruningEnumerationIncomingProper

/-!
# Proper pending paths at actual shared incoming outcomes

The raw read changes no stored bucket. Successful writes retain strict paths.
The actual cache adapter also retains strict paths on its synthetic Empty write.
The full input partition supplies strict descendant inputs from ProperInputs.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedIncomingNode
open EnumerationState EnumerationSchedule EnumerationCorrectness
open EnumerationSemantics EnumerationProgress InternedConstructorTemplates
open SourcePruningEnumerationIncomingNode (finish)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
attribute [local instance] SourcePruningEnumerationIncomingNode.incomingNodeMonadList

private theorem pending_paths_proper (node : Option Nat) (scs : List Suspended)
    (payload : ProperValue (.unenumerated node scs : UVarValue Symbol)) :
    ∀ sc ∈ scs, ProperTrie sc.trie := by
  cases node with
  | none =>
      have empty : scs = [] := payload
      intro sc member
      rw [empty] at member
      cases member
  | some _handle => exact payload

private theorem proper_set (target : Nat) (value : UVarValue Symbol) (before : Core)
    (proper : ProperState before) (payload : ProperValue value) :
    ProperState {before with values := before.values.set target value} := by
  intro stored member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact proper stored old
  · simpa [same] using payload

private theorem finish_singleton_proper
    {before returned : Core} {target handle : Nat} {oldNode : Option Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (valid : ProperState before) (inputs : ∀ sc ∈ incomingScs, ProperTrie sc.trie)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (observed : ExceptT.run (finish target handle incomingScs oldScs replacement before) =
      [.ok ((), returned)]) : ProperState returned := by
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
  have oldValid : ∀ sc ∈ oldScs, ProperTrie sc.trie :=
    pending_paths_proper oldNode oldScs (valid _ (List.mem_of_getElem? stored))
  apply proper_set target (.unenumerated (some handle) (incomingScs ++ oldScs)) before valid
  intro sc member
  rcases List.mem_append.mp member with incoming | old
  · exact inputs sc incoming
  · exact oldValid sc old

private theorem finish_reply_proper
    {Fault : Type _} {before returned : Core} {target handle : Nat} {oldNode : Option Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (valid : ProperState before) (inputs : ∀ sc ∈ incomingScs, ProperTrie sc.trie)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (observed : (Except.ok (some (ExceptT.run
        (finish target handle incomingScs oldScs replacement before))) : Except Fault (Option Raw)) =
      .ok (some [.ok ((), returned)])) : ProperState returned :=
  finish_singleton_proper valid inputs stored (Option.some.inj (Except.ok.inj observed))

variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every literal shared read and successful raw singleton retain proper pending paths. -/
theorem run_proper
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (valid : ProperState before) (inputs : ∀ sc ∈ incomingScs, ProperTrie sc.trie) :
    ProperState (run checkEmpty r n p h caller before target incoming incomingScs queries).2.2.2 ∧
      ∀ returned, (run checkEmpty r n p h caller before target incoming incomingScs queries).1 =
        .ok (some [.ok ((), returned)]) → ProperState returned := by
  generalize observedEq : run checkEmpty r n p h caller before target incoming incomingScs queries = observed
  obtain ⟨result, reachedCaller, savedQueries, read⟩ := observed
  dsimp only
  unfold run at observedEq
  split at observedEq
  next =>
    simp only [Prod.mk.injEq] at observedEq
    rcases observedEq with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨valid, ?_⟩
    intro returned singleton
    simp at singleton
  next =>
    repeat' first
      | (have readSame := congrArg (fun observed : _ × Caller width × Queries × Core => observed.2.2.2) observedEq
         have resultSame := congrArg Prod.fst observedEq
         dsimp only at readSame resultSame
         constructor
         · rw [← readSame]
           change ProperState before
           exact valid
         · intro returned singleton
           rw [← resultSame] at singleton
           solve
           | simp at singleton
           | apply finish_reply_proper (observed := singleton)
             · change ProperState before
               exact valid
             · exact inputs
             · assumption)
      | split at observedEq
      | (dsimp only at observedEq; split at observedEq)

end MicroCFTA.SourcePruningEnumerationSharedIncomingNode

namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
open EnumerationState EnumerationProgress InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual shared cache candidate retains strict paths, including its raw-empty write. -/
theorem incoming_cache_proper
    (checkEmpty : Bool) (r n p h k : Nat) (caller : Caller width) (before : Cached)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (valid : ProperState before.core) (inputs : ∀ sc ∈ incomingScs, ProperTrie sc.trie)
    (after : Cached)
    (candidate : (incomingCacheAdapter checkEmpty r n p h k caller before
      target incoming incomingScs queries).2 = some after) : ProperState after.core := by
  have fields := SourcePruningEnumerationSharedIncomingNode.run_proper
    checkEmpty r n p h caller before.core target incoming incomingScs queries valid inputs
  unfold incomingCacheAdapter at candidate
  generalize original : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
    caller before.core target incoming incomingScs queries = observed at fields candidate
  obtain ⟨result, reached, saved, read⟩ := observed
  dsimp only at fields candidate
  cases result with
  | error fault => cases candidate
  | ok payload =>
      cases payload with
      | none => cases candidate
      | some raw =>
          apply SourcePruningEnumerationIncomingCacheAdapter.adapt_proper fields.1 inputs ?_ candidate
          intro returned rawSame
          exact fields.2 returned (by rw [rawSame])

/-- The literal terminal partition supplies the incoming adapter's strict descendant paths. -/
theorem incoming_cache_partition_proper
    (checkEmpty : Bool) (r n p h k : Nat) (caller : Caller width) (before : Cached)
    (target : Nat) (incoming : Node) (bucket : List Suspended)
    (first : Suspended) (rest descendants : List Suspended) (queries : Queries)
    (valid : ProperState before.core) (inputs : ProperInputs bucket)
    (partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) =
      (first :: rest, descendants))
    (after : Cached)
    (candidate : (incomingCacheAdapter checkEmpty r n p h k caller before
      target incoming descendants queries).2 = some after) : ProperState after.core := by
  have below : bucket.filter (fun sc => !(EqualityTrie.isTerminal sc.trie)) = descendants := by
    simpa only [List.partition_eq_filter_filter, Function.comp_def] using congrArg Prod.snd partitioned
  have strict : ∀ sc ∈ descendants, ProperTrie sc.trie := by
    rw [← below]
    exact proper_below bucket inputs
  exact incoming_cache_proper checkEmpty r n p h k caller before target incoming descendants queries
    valid strict after candidate

end MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
