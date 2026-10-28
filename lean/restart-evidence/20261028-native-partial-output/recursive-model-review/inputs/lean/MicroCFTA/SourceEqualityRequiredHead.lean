import MicroCFTA.SourceEqualityRequiredCache

/-!
# Actual constructor-row normalization before required-path traversal

The graph retains the completed cold read and the subsequent actual node
constructor. The read bound is proof instrumentation. Complete head reads
have a unique returned node and cache at every sufficient read bound.
-/
namespace MicroCFTA.SourceEqualityRequiredHead
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache
open MergedFreshOrdinaryExposure

/-- The source first exposes rows, then constructs the ordinary row node. -/
inductive Head [DecidableEq (EdgeKey Symbol Guard)] :
    Value Symbol Guard → State Symbol Guard → Value Symbol Guard → State Symbol Guard → Prop where
  | read (fuel : Nat) (edges : List (EdgeValue Symbol Guard)) (middle : State Symbol Guard)
      (exposed : nodeEdges fuel value before = .done edges middle)
      (rebuilt : run (makeNode edges) middle = (result, after)) : Head value before result after

/-- Each closed available source value has a finite complete physical head normalization. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (ready : Ready state) (available : Available state value) (closed : value.free = []) :
    ∃ result after, Head value state result after ∧ Keeps state after ∧ Available after result ∧
      result.free = [] ∧ Ordinary result := by
  obtain ⟨fuel, edges, middle, read, semantic, covered, depth, growth, history, resident, closedEdges, _⟩ :=
    MergedFreshOrdinaryColdTermination.read_closed value state ready.semantic ready.covered ready.depth available closed
  have first : Keeps state middle := ⟨⟨semantic, covered, depth⟩, growth, history⟩
  have rebuilt := SourceEqualityRequiredCache.node edges middle first.ready resident closedEdges
  exact ⟨_, _, .read fuel edges middle read rfl, first.trans rebuilt.1,
    rebuilt.2.1, rebuilt.2.2.1, rebuilt.2.2.2⟩

/-- Successful read bounds return exactly the same rebuilt source node and cache. -/
theorem Head.unique [DecidableEq (EdgeKey Symbol Guard)]
    {value first second : Value Symbol Guard} {before afterFirst afterSecond : State Symbol Guard}
    (left : Head value before first afterFirst) (right : Head value before second afterSecond) :
    first = second ∧ afterFirst = afterSecond := by
  cases left with
  | read firstFuel firstEdges firstMiddle firstRead firstBuilt =>
      cases right with
      | read secondFuel secondEdges secondMiddle secondRead secondBuilt =>
          have leftStable := MergedFreshOrdinaryColdReplay.nodeEdges_stable firstFuel secondFuel value before
            (by simp only [firstRead, MergedSourceExposure.Finished])
          have rightStable := MergedFreshOrdinaryColdReplay.nodeEdges_stable secondFuel firstFuel value before
            (by simp only [secondRead, MergedSourceExposure.Finished])
          rw [Nat.add_comm secondFuel firstFuel] at rightStable
          have equal := (leftStable.trans firstRead).symm.trans (rightStable.trans secondRead)
          have same := MergedSourceExposure.Result.done.inj equal
          cases same.1
          cases same.2
          have pair := firstBuilt.symm.trans secondBuilt
          exact ⟨congrArg Prod.fst pair, congrArg Prod.snd pair⟩

/-- Every successful source head graph derives the same complete cache and value invariants. -/
theorem Head.verified [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (head : Head value before result after) (ready : Ready before)
    (available : Available before value) (closed : value.free = []) :
    Keeps before after ∧ Available after result ∧ result.free = [] ∧ Ordinary result := by
  obtain ⟨actual, final, completed, kept, resident, resultClosed, ordinary⟩ := complete value before ready available closed
  obtain ⟨sameValue, sameState⟩ := completed.unique head
  cases sameValue
  cases sameState
  exact ⟨kept, resident, resultClosed, ordinary⟩

/-- An ordinary first unfolding takes the existing zero-worklist fast path. -/
theorem ordinary_fast [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (before middle : State Symbol Guard) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (recursive : ∃ own body probe ordinary, value = .mu own body probe ordinary)
    (unfolded : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done (.node entry edges depth free) middle) :
    Head value before (run (makeNode edges) middle).1 (run (makeNode edges) middle).2 := by
  obtain ⟨own, body, probe, ordinary, rfl⟩ := recursive
  exact .read 0 edges middle (by simp only [nodeEdges, unfolded]) rfl

end MicroCFTA.SourceEqualityRequiredHead
