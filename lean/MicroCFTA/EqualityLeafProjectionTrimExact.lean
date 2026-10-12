import MicroCFTA.EqualityLeafProjectionTrimTransport
import MicroCFTA.EqualityRawLeafPullback

/-!
# Exact occurrence witnesses in the runtime cache

A finite later proof witness can be trimmed into the cache retaining its
actual result. The resulting compiler is allocation-free there. No common
extension of divergent runtime and proof allocation histories is required.
-/
namespace MicroCFTA.EqualityLeafProjectionTrimExact
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open EqualityLeafProjectionSyntax (Tree Edge)
open EqualityLeafProjectionCompile (Tag)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionTrim EqualityLeafProjectionTrimTransport

/-- Local leaf reconstruction derives complete runtime-cache reconstruction by trimming dead rows. -/
theorem pullback [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leafAvailable : LeafAvailable leaf)
    (leafPullback : ∀ input, Pullback leaf (.leaf input)) (tree : Tree (Tag Symbol Guard) Leaf) : Pullback leaf tree := by
  intro before after beforeFacts afterFacts value available represented
  cases tree with
  | empty =>
      have same : value = .empty := (congrArg (fun result : Value Symbol Guard × State Symbol Guard => result.1) represented).symm
      subst value
      exact ⟨.empty, .empty _, rfl⟩
  | leaf input => exact leafPullback input before after beforeFacts afterFacts value available represented
  | node edges =>
      apply EqualityLeafProjectionTrimTransport.node leaf leafAvailable edges ?_ before after beforeFacts afterFacts value available represented
      intro edge member child present
      exact pullback leaf leafAvailable leafPullback child
termination_by sizeOf tree
decreasing_by
  have edgeSmall := List.sizeOf_lt_of_mem member
  cases edge with
  | mk tag children =>
      have childSmall := List.sizeOf_lt_of_mem present
      simp only [EqualityLeafProjectionSyntax.Edge.children] at childSmall
      simp_wf
      simp only [EqualityLeafProjectionSyntax.Edge.mk.sizeOf_spec] at edgeSmall
      subst tree
      simp only [EqualityLeafProjectionSyntax.Tree.node.sizeOf_spec]
      omega

noncomputable local instance : DecidableEq EqualityLeafProjectionLeafCache.ConstraintKey := by classical exact inferInstance

/-- Finite raw leaves reconstruct from resident complete records, with no cache-growth premise. -/
theorem raw_pullback
    (tree : Tree (Tag (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey)
      (EqualityRawLeafInventory.Leaf initial symbols)) : Pullback EqualityRawLeafCompiler.build tree :=
  pullback EqualityRawLeafCompiler.build EqualityRawLeafCompiler.leaves_available
    (fun input before after beforeFacts afterFacts value available represented =>
      ⟨.leaf input, .leaf input, EqualityRawLeafPullback.represented_pullback input before after beforeFacts afterFacts value available.resident represented⟩) tree

/-- The runtime witness retains the exact source result and can only decrease the occurrence rank. -/
theorem raw_rank
    (rank : EqualityRawLeafInventory.Leaf initial symbols → Nat)
    (tree : Tree (Tag (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey)
      (EqualityRawLeafInventory.Leaf initial symbols))
    (before after : State (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey)
    (beforeFacts : Facts before) (afterFacts : Facts after)
    (value : Value (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey) (available : Available before value)
    (represented : Represents EqualityRawLeafCompiler.build tree after value) :
    ∃ trimmed, EqualityLeafProjectionSyntax.Progress (EqualityLeafProjectionSyntax.weight rank) trimmed tree ∧
      Represents EqualityRawLeafCompiler.build trimmed before value := by
  obtain ⟨trimmed, removed, closed⟩ := raw_pullback tree before after beforeFacts afterFacts value available represented
  exact ⟨trimmed, EqualityLeafProjectionTrim.progress rank removed, closed⟩

end MicroCFTA.EqualityLeafProjectionTrimExact
