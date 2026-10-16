import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMerge
namespace FiniteOrdinaryMergeKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
namespace G
export SourceCurrentAllocatedMergeGraph (State Memo Call Run Code body root group small map)
end G
namespace M
export SourceCurrentMemoMergeGraph (empty remember winner remember_absent winner_found)
end M
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "Physical" => SourceCurrentMemoMergeEffects.Stored
local notation "Structural" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Empty cold completion records its exact winner, then a hit retains heap and equality state. -/
theorem cold_empty_then_warm (clear : Guard → Bool) (before : G.State) (ready : Ready before) :
    let saved : G.Memo := M.remember M.empty .empty .empty
    G.Call clear .empty before M.empty .empty before saved ∧
      G.Call clear .empty before saved .empty before saved ∧ Effects before before ∧
      Physical before.heap saved ∧ Structural saved ∧ Available before.heap (.empty : Value Symbol Guard) ∧
      DNode (.empty : Value Symbol Guard) ∧ saved .empty = some ⟨.empty, .empty⟩ := by
  let saved : G.Memo := M.remember M.empty .empty .empty
  have inserted := M.remember_absent (M.empty : G.Memo) .empty .empty rfl
  have cold : G.Call clear .empty before M.empty (M.winner M.empty .empty .empty).result before saved :=
    .miss rfl (.pure (.empty : Value Symbol Guard) before M.empty)
  rw [inserted.2] at cold
  have first := SourceCurrentAllocatedFiniteOrdinaryMerge.allocated cold ready
    (SourceCurrentMemoMergeEffects.stored_empty before.heap)
    SourceCurrentAllocatedFiniteOrdinaryMergeCache.empty_stored (empty_available before.heap) .empty
  have warm : G.Call clear .empty before saved .empty before saved := .hit inserted.1
  have second := SourceCurrentAllocatedFiniteOrdinaryMerge.allocated warm first.1.ready first.2.1 first.2.2.1
    (empty_available before.heap) .empty
  exact ⟨cold, warm, second.1, second.2.1, second.2.2.1, second.2.2.2.1, second.2.2.2.2, inserted.1⟩

/-- Two finite calls derive the warm result and retain the whole physical state and completed table. -/
theorem finite_then_finite_warm (clear : Guard → Bool) (input : Value Symbol Guard)
    (before : G.State) (memo : G.Memo) (ready : Ready before)
    (physical : Physical before.heap memo) (structural : Structural memo)
    (available : Available before.heap input) (domain : DNode input) :
    ∃ output after saved, G.Call clear input before memo output after saved ∧
      G.Call clear input after saved output after saved ∧ Effects before after ∧
      Physical after.heap saved ∧ Structural saved ∧ Available after.heap output ∧ DNode output ∧
      ∃ entry, saved input.referenceOf = some entry ∧ entry.original = input ∧ entry.result = output := by
  obtain ⟨output, after, saved, cold, effect, physicalAfter, structuralAfter, resultAvailable, resultDomain⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMerge.finite clear input before memo ready physical structural available domain
  have inputAvailable := effect.keeps.available input available
  obtain ⟨entry, found, sameResult⟩ := cold.graph.present
  have owner := (SourceCurrentMemoMergeEffects.hit_original effect.ready.semantic inputAvailable physicalAfter found).1
  obtain ⟨second, final, completed, warm, secondEffect, physicalFinal, structuralFinal, secondAvailable, secondDomain⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMerge.finite clear input after saved effect.ready physicalAfter structuralAfter inputAvailable domain
  have exactWarm : second = output ∧ final = after ∧ completed = saved := by
    cases warm with
    | hit observed =>
        have same := Option.some.inj (found.symm.trans observed)
        cases same
        exact ⟨sameResult.symm, rfl, rfl⟩
    | miss absent _ => rw [found] at absent; cases absent
  rcases exactWarm with ⟨rfl, rfl, rfl⟩
  exact ⟨second, final, completed, cold, warm, effect, physicalFinal, structuralFinal, secondAvailable, secondDomain,
    entry, found, owner, sameResult.symm⟩

/-- A constrained singleton group runs its literal small-row body and both raw constructors. -/
theorem constrained_small_group (clear : Guard → Bool) (before : G.State)
    (own : Interned InternedBinderProtocol.NodeKey) (entry : Interned (EdgeKey Symbol Guard)) (depth : Nat)
    (ready : Ready before) (available : Available before.heap (.node own [.mk entry []] depth [])) :
    let input : Value Symbol Guard := .node own [.mk entry []] depth []
    let rebuilt := run (makeEdge entry.key.symbol entry.key.constraint []) before.heap
    let nodeBuilt := run (makeNode [rebuilt.1]) rebuilt.2
    let after : G.State := ⟨nodeBuilt.2, before.equality⟩
    let saved : G.Memo := M.remember M.empty input nodeBuilt.1
    G.Call clear input before M.empty nodeBuilt.1 after saved ∧ Effects before after ∧
      Physical after.heap saved ∧ Structural saved ∧ Available after.heap nodeBuilt.1 ∧ DNode nodeBuilt.1 ∧
      after.equality = before.equality := by
  let edge : EdgeValue Symbol Guard := .mk entry []
  let input : Value Symbol Guard := .node own [edge] depth []
  let rebuilt := run (makeEdge entry.key.symbol entry.key.constraint []) before.heap
  let middle : G.State := ⟨rebuilt.2, before.equality⟩
  let nodeBuilt := run (makeNode [rebuilt.1]) rebuilt.2
  let after : G.State := ⟨nodeBuilt.2, before.equality⟩
  let saved : G.Memo := M.remember M.empty input nodeBuilt.1
  have small : G.Run clear (G.small edge) before M.empty rebuilt.1 middle M.empty :=
    .bind (.pure [] before M.empty) (.work (makeEdge entry.key.symbol entry.key.constraint []) before M.empty)
  have group : G.Run clear (G.group [edge]) before M.empty [rebuilt.1] middle M.empty := by
    change G.Run clear (G.map G.small [edge]) before M.empty [rebuilt.1] middle M.empty
    exact .bind small (.bind (.pure [] middle M.empty) (.pure [rebuilt.1] middle M.empty))
  have groups : G.Run clear (G.map G.group [[edge]]) before M.empty [[rebuilt.1]] middle M.empty :=
    .bind group (.bind (.pure [] middle M.empty) (.pure [[rebuilt.1]] middle M.empty))
  have root : G.Run clear (G.root [[edge]]) before M.empty nodeBuilt.1 after M.empty :=
    .bind groups (.work (makeNode [rebuilt.1]) middle M.empty)
  have grouped : MergedSourceGrouping.groups [edge] = [[edge]] := by
    simp [MergedSourceGrouping.groups, Sized.groups]
  have body : G.Run clear (G.body input) before M.empty nodeBuilt.1 after M.empty := by
    change G.Run clear (G.root (MergedSourceGrouping.groups [edge])) before M.empty nodeBuilt.1 after M.empty
    rw [grouped]
    exact root
  have actual : G.Call clear input before M.empty nodeBuilt.1 after saved := by
    have cold : G.Call clear input before M.empty (M.winner M.empty input nodeBuilt.1).result after saved := .miss rfl body
    rw [(M.remember_absent (M.empty : G.Memo) input nodeBuilt.1 rfl).2] at cold
    exact cold
  have checked := SourceCurrentAllocatedFiniteOrdinaryMerge.allocated actual ready
    (SourceCurrentMemoMergeEffects.stored_empty before.heap)
    SourceCurrentAllocatedFiniteOrdinaryMergeCache.empty_stored available (.ordinary (.cons .nil .nil))
  exact ⟨actual, checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1, checked.2.2.2.2, rfl⟩
end FiniteOrdinaryMergeKernels
#print axioms FiniteOrdinaryMergeKernels.cold_empty_then_warm
#check @FiniteOrdinaryMergeKernels.cold_empty_then_warm
#print axioms FiniteOrdinaryMergeKernels.finite_then_finite_warm
#check @FiniteOrdinaryMergeKernels.finite_then_finite_warm
#print axioms FiniteOrdinaryMergeKernels.constrained_small_group
#check @FiniteOrdinaryMergeKernels.constrained_small_group
