import MicroCFTA.SourceCurrentHereditaryMerge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.HereditaryRequiredMergeKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityAnnotationLanguage SourceCurrentMemoMergeGraph
open SourceEqualityRequiredSemanticCache
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- A current ordinary merge performs its recursive Mu child request before publication. -/
theorem ordinary_mu_child [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (top : Guard) (topValid : valid top)
    (entry muEntry : Interned InternedBinderProtocol.NodeKey) (symbol : Symbol) (guard : Guard)
    (edgeEntry : Interned (EdgeKey Symbol Guard)) (key : edgeEntry.key.symbol = symbol)
    (sameGuard : edgeEntry.key.constraint = guard) (body depth ordinary : Value Symbol Guard) (nodeDepth : Nat)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before (.node entry [⟨edgeEntry, [.mu muEntry body depth ordinary]⟩] nodeDepth []))
    (guardValid : valid guard) (bodyAnnotated : Annotated valid body) :
    ∃ result after saved,
      Call clear top (.node entry [⟨edgeEntry, [.mu muEntry body depth ordinary]⟩] nodeDepth []) before empty result after saved ∧
      SourceCurrentMemoMergeEffects.Effect before after ∧ SourceCurrentMemoMergeEffects.Stored after saved ∧
      SourceCurrentHereditaryMerge.Stored valid saved ∧ Annotated valid result := by
  let mu : Value Symbol Guard := .mu muEntry body depth ordinary
  let edge : EdgeValue Symbol Guard := ⟨edgeEntry, [mu]⟩
  let input : Value Symbol Guard := .node entry [edge] nodeDepth []
  let current := remember (empty : Memo Symbol Guard) mu mu
  have first : Call clear top mu before empty mu before current := by
    simpa only [mu, winner, remember, empty, InternedRecordCoherence.keepFirst, Option.getD_some] using
      (Call.miss (memo := empty) (input := mu) rfl (by simpa only [mu, SourceCurrentMemoMergeGraph.body] using Run.pure mu before empty))
  have children : Run clear top (map Code.request [mu]) before empty [mu] before current :=
    Run.map_cons_iff.mpr ⟨mu, [], before, current, .request first, .pure [] before current, rfl⟩
  let rebuiltEdge := run (makeEdge edgeEntry.key.symbol edgeEntry.key.constraint [mu]) before
  have smallRun : Run clear top (small edge) before empty rebuiltEdge.1 rebuiltEdge.2 current :=
    .bind children (.work _ before current)
  have groupRun : Run clear top (group top [edge]) before empty [rebuiltEdge.1] rebuiltEdge.2 current := by
    rw [group_small top [edge] (by decide)]
    exact Run.map_cons_iff.mpr ⟨_, [], _, _, smallRun, .pure [] _ _, rfl⟩
  have groupsRun : Run clear top (map (group top) [[edge]]) before empty [[rebuiltEdge.1]] rebuiltEdge.2 current :=
    Run.map_cons_iff.mpr ⟨_, [], _, _, groupRun, .pure [] _ _, rfl⟩
  let rebuiltNode := run (makeNode [rebuiltEdge.1]) rebuiltEdge.2
  have bodyRun : Run clear top (SourceCurrentMemoMergeGraph.body top input) before empty rebuiltNode.1 rebuiltNode.2 current := by
    have rootRun : Run clear top (root top [[edge]]) before empty rebuiltNode.1 rebuiltNode.2 current :=
      .bind groupsRun (.work _ _ _)
    simpa [input, SourceCurrentMemoMergeGraph.body, MergedSourceGrouping.groups, Sized.groups] using rootRun
  have actual := Call.miss (memo := empty) (input := input) rfl bodyRun
  have annotated : Annotated valid input := by
    apply Annotated.node
    · intro selected member
      have eq := List.mem_singleton.mp member
      subst selected
      change valid edgeEntry.key.constraint
      rw [sameGuard]
      exact guardValid
    · intro value member
      have eq : value = mu := by simpa [edge] using member
      subst value
      exact .mu muEntry body depth ordinary bodyAnnotated
  obtain ⟨effects, physical, stored, result⟩ := SourceCurrentHereditaryMerge.cold valid topValid actual semantic costs available annotated
  exact ⟨_, _, _, actual, effects, physical, stored, result⟩

/-- An actual produced entry supplies the next warm result at the identical heap and table. -/
theorem produced_warm [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (top : Guard) (topValid : valid top)
    (input result : Value Symbol Guard) (before after : State Symbol Guard) (saved : Memo Symbol Guard)
    (actual : Call clear top input before empty result after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input)
    (annotated : Annotated valid input) :
    ∃ warm : Call clear top input after saved result after saved,
      Annotated valid result ∧ SourceCurrentHereditaryMerge.Stored valid saved ∧
      SourceCurrentMemoMergeEffects.Stored after saved ∧
      (∀ later other completed, Call clear top input after saved later other completed →
        other = after ∧ completed = saved ∧ later = result) := by
  obtain ⟨effects, physical, stored, output⟩ := SourceCurrentHereditaryMerge.cold valid topValid actual semantic costs available annotated
  obtain ⟨entry, found, rfl⟩ := actual.present
  have warm : Call clear top input after saved entry.result after saved := .hit found
  have inputAfter := effects.keeps.available input available
  have retained := SourceCurrentHereditaryMerge.call valid topValid warm effects.semantic effects.costs physical stored inputAfter
  exact ⟨warm, output, retained.2.2.1, retained.2.1,
    fun _ _ _ next => next.hit_unchanged entry found⟩

/-- A stored earlier winner keeps its own law when a different annotated candidate finishes. -/
theorem earlier_winner (valid : Guard → Prop) (memo : Memo Symbol Guard)
    (input candidate : Value Symbol Guard) (entry : Entry Symbol Guard)
    (stored : SourceCurrentHereditaryMerge.Stored valid memo)
    (found : memo input.referenceOf = some entry) (candidateAnnotated : Annotated valid candidate)
    (originalAnnotated : Annotated valid entry.original) :
    remember memo input candidate = memo ∧ winner memo input candidate = entry ∧ Annotated valid (winner memo input candidate).result := by
  have unchanged := winner_existing memo input candidate entry found
  exact ⟨unchanged.1, unchanged.2, unchanged.2 ▸ stored _ _ found originalAnnotated⟩

end MicroCFTA.HereditaryRequiredMergeKernels

#print axioms MicroCFTA.HereditaryRequiredMergeKernels.ordinary_mu_child
#check @MicroCFTA.HereditaryRequiredMergeKernels.ordinary_mu_child
#print axioms MicroCFTA.HereditaryRequiredMergeKernels.produced_warm
#check @MicroCFTA.HereditaryRequiredMergeKernels.produced_warm
#print axioms MicroCFTA.HereditaryRequiredMergeKernels.earlier_winner
#check @MicroCFTA.HereditaryRequiredMergeKernels.earlier_winner
