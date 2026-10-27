import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
import MicroCFTA.EnumerationProgress

/-!
# Proper pending paths at actual incoming observations

The incoming read changes no value slot. A completed write concatenates the
incoming bucket with the actual stored bucket. The cache adapter retains
proper pending paths in singleton rows and synthetic Empty writes.
-/
namespace MicroCFTA

private theorem pending_paths_proper {Symbol : Type} (node : Option Nat) (scs : List EnumerationState.Suspended)
    (payload : EnumerationProgress.ProperValue
      (.unenumerated node scs : EnumerationState.UVarValue Symbol)) :
    ∀ sc ∈ scs, EnumerationProgress.ProperTrie sc.trie := by
  cases node with
  | none =>
      have empty : scs = [] := payload
      intro sc member
      rw [empty] at member
      cases member
  | some _handle => exact payload

private theorem proper_set {Symbol Guard : Type} (target : Nat) (value : EnumerationState.UVarValue Symbol)
    (before : EnumerationState.State Symbol Guard)
    (proper : EnumerationProgress.ProperState before) (payload : EnumerationProgress.ProperValue value) :
    EnumerationProgress.ProperState {before with values := before.values.set target value} := by
  intro stored member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact proper stored old
  · simpa [same] using payload

namespace SourcePruningEnumerationIncomingNode
open EnumerationState EnumerationSchedule EnumerationCorrectness
open EnumerationSemantics EnumerationProgress InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
attribute [local instance] SourcePruningEnumerationIncomingNode.incomingNodeMonadList

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
    pending_paths_proper oldNode oldScs (valid (.unenumerated oldNode oldScs) (List.mem_of_getElem? stored))
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
section runtime
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual read and successful singleton retain proper pending paths at every fixed bound. -/
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

end runtime

/-- The actual read and explicit write shape also retain proper pending paths when raw continuation rejects. -/
theorem written_proper
    (before read after : Core) (fuel uv target handle : Nat) (oldNode : Option Nat)
    (incomingScs oldScs : List Suspended)
    (valid : ProperState before) (inputs : ∀ sc ∈ incomingScs, ProperTrie sc.trie)
    (reading : Success (getValue fuel uv) before (.unenumerated oldNode oldScs) read)
    (shape : after = {read with
      values := read.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (read.expansionAncestry ++ read.recursionAncestry target).eraseDups
        else read.recursionAncestry other}) : ProperState after := by
  obtain ⟨readValid, oldPayload⟩ := getValue_proper fuel uv before read
    (.unenumerated oldNode oldScs) valid reading
  have oldValid := pending_paths_proper oldNode oldScs oldPayload
  rw [shape]
  apply proper_set target (.unenumerated (some handle) (incomingScs ++ oldScs)) read readValid
  intro sc member
  rcases List.mem_append.mp member with incoming | old
  · exact inputs sc incoming
  · exact oldValid sc old

end SourcePruningEnumerationIncomingNode

namespace SourcePruningEnumerationIncomingCacheAdapter
open EnumerationState EnumerationSchedule EnumerationCorrectness
open EnumerationSemantics EnumerationProgress InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))

/-- The literal adapter preserves proper pending paths, including its synthetic raw-empty write. -/
theorem adapt_proper
    {heap : InternedConstructorTemplates.State Symbol Constraint} {indexFuel target : Nat}
    {incomingScs : List Suspended} {before after : Cached} {read : Core} {raw : Raw}
    (readValid : ProperState read) (inputs : ∀ sc ∈ incomingScs, ProperTrie sc.trie)
    (rows : ∀ returned, raw = [.ok ((), returned)] → ProperState returned)
    (adapted : adapt heap indexFuel target incomingScs before read raw = some after) :
    ProperState after.core := by
  cases raw with
  | nil =>
      simp only [adapt] at adapted
      split at adapted
      · rename_i oldNode oldScs stored
        simp only [Option.map_eq_some_iff] at adapted
        obtain ⟨written, _written, same⟩ := adapted
        subst after
        have oldValid : ∀ sc ∈ oldScs, ProperTrie sc.trie :=
          pending_paths_proper oldNode oldScs (readValid (.unenumerated oldNode oldScs) (List.mem_of_getElem? stored))
        apply proper_set target (.unenumerated (some 0) (incomingScs ++ oldScs)) read readValid
        intro sc member
        rcases List.mem_append.mp member with incoming | old
        · exact inputs sc incoming
        · exact oldValid sc old
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

/-- Every actual attached cache retains proper pending paths, without a safety claim on rejection. -/
theorem observed_cache_proper
    (checkEmpty : Bool) (r n p h k : Nat) (caller : Caller width) (before : Cached)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (valid : ProperState before.core) (inputs : ∀ sc ∈ incomingScs, ProperTrie sc.trie)
    (after : Cached)
    (candidate : (run checkEmpty r n p h k caller before target incoming incomingScs queries).2 = some after) :
    ProperState after.core := by
  have fields := SourcePruningEnumerationIncomingNode.run_proper
    checkEmpty r n p h caller before.core target incoming incomingScs queries valid inputs
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
          apply adapt_proper fields.1 inputs ?_ candidate
          intro returned rawSame
          exact fields.2 returned (by rw [rawSame])

end SourcePruningEnumerationIncomingCacheAdapter
end MicroCFTA
