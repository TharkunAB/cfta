  generalize observedEq : run checkEmpty r n p h caller before target incoming incomingScs queries = observed
  obtain ⟨result, reachedCaller, savedQueries, read⟩ := observed
  dsimp only
  unfold run at observedEq
  cases lookup : UnionFind.findRoot r before.representatives target with
  | none =>
      simp only [lookup, Prod.mk.injEq] at observedEq
      rcases observedEq with ⟨rfl, rfl, rfl, rfl⟩
      refine ⟨⟨total, .refl before, references⟩, ?_⟩
      intro returned singleton
      simp at singleton
  | some found =>
      simp only [lookup] at observedEq
      have frame : Frame before {before with representatives := found.forest} := by
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
        intro other root size
        exact UnionFind.findRoot_reaches_iff total lookup other root size
      have reached := (UnionFind.findRoot_correct r before.representatives target found lookup).2
        (UnionFind.findRoot_correct r before.representatives target found lookup).1
      have related : UnionFind.SameClass found.forest target found.representative :=
        UnionFind.sameClass_root reached
      repeat' first
        | (have readSame := congrArg (fun observed : _ × Caller width × Queries × Core => observed.2.2.2) observedEq
           have resultSame := congrArg Prod.fst observedEq
           dsimp only at readSame resultSame
           constructor
           · rw [← readSame]
             exact ⟨frame.total total, frame.carriers, frame.references references⟩
           · intro returned singleton
             rw [← resultSame] at singleton
             solve
             | simp at singleton
             | (obtain ⟨returnedTotal, preserved, returnedReferences, own⟩ :=
                  finish_reply_carriers (frame.total total) (frame.references references)
                    related (by assumption) singleton
                exact ⟨returnedTotal, frame.carriers.trans preserved, returnedReferences, own⟩))
        | split at observedEq

end MicroCFTA.SourcePruningEnumerationIncomingNode

namespace MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
open EnumerationState EnumerationSchedule EnumerationCorrectness EnumerationCarriers EnumerationGraphReferences
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
