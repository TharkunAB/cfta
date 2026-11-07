import MicroCFTA.InternedNestedFacts
import MicroCFTA.InternedFreshProbeKeys

/-!
# Exact replay of resident canonical probe nodes

The current cache contains the complete node with the actual surviving
canonical rows. The constructor therefore returns that record and the
same cache. It does not allocate a replacement node.
-/
namespace MicroCFTA.SourceSynthesisUniverseNodeReplay
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)

variable {Symbol Guard : Type}

/-- A resident nonempty canonical node is the exact result of the original raw-row request. -/
theorem resident_node_replay [DecidableEq (EdgeKey Symbol Guard)]
    (rows : List (EdgeValue Symbol Guard)) (entry : Interned NodeKey)
    (depth : Nat) (free : List Reference) (heap : State Symbol Guard) (facts : Facts heap)
    (available : Available heap (.node entry (canonicalEdges (surviving rows)) depth free))
    (nonempty : canonicalEdges (surviving rows) ≠ []) :
    run (makeNode rows) heap = (.node entry (canonicalEdges (surviving rows)) depth free, heap) := by
  have stored := available.resident entry rfl
  have installed := InternedFreshProbeKeys.resident_entry heap facts.coherent _ available.resident entry rfl
  cases kept : canonicalEdges (surviving rows) with
  | nil => exact False.elim (nonempty kept)
  | cons first rest =>
      rw [kept] at stored
      obtain ⟨_, _, fields⟩ := facts.coherent.nodes entry.key _ stored
      have key : entry.key = .node ((first :: rest).map (fun edge => edge.entry.identity)) := fields.2.1
      rw [key] at installed stored
      simp only [makeNode, kept, run, nodeStep, Cache.intern, installed, keepFirst, stored, Option.getD_some]

end MicroCFTA.SourceSynthesisUniverseNodeReplay
