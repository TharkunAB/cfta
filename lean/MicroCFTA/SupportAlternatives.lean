import MicroCFTA.SupportClosing

/-!
# Closing retained private alternatives

Grouping can store several Apply edges in one ordinary support node.
The old single-edge recognizer wrapped that complete node. The term callback
instead closed each Apply term. The repaired source closes those edges one
at a time and concatenates their complete labelled roots.
-/
namespace MicroCFTA.SupportAlternatives
open Language GeneratorCombinators BinderLanguage SupportGraph SupportClosing

/-- An ordinary node retaining all of its original source alternatives. -/
def node (layers : List (Layer Symbol)) : Support Symbol := .alternatives (layers.map graph)

/-- The repaired source distributes closing over each retained private edge. -/
def closeNode (symbol : Symbol) (layers : List (Layer Symbol)) : Support Symbol :=
  .alternatives (layers.flatMap (roots symbol))

/-- Distribution over ordinary alternatives gives exactly the callback image. -/
theorem closeNode_exact (environment : Env (Label Symbol)) (symbol : Symbol)
    (layers : List (Layer Symbol)) (valid : ∀ layer ∈ layers, Valid layer)
    (term : Term (Label Symbol)) :
    meaning environment (closeNode symbol layers) term ↔
      ∃ original, meaning environment (node layers) original ∧ term = SupportTerms.labelTerm symbol original := by
  simp only [closeNode, node, alternatives_exact]
  constructor
  · rintro ⟨shape, member, accepted⟩
    obtain ⟨layer, layerMember, shapeMember⟩ := List.mem_flatMap.mp member
    have closed := (alternatives_exact environment (roots symbol layer) term).mpr ⟨shape, shapeMember, accepted⟩
    obtain ⟨original, originalAccepted, same⟩ := (close_exact environment symbol layer (valid layer layerMember) term).mp closed
    exact ⟨original, ⟨_, List.mem_map.mpr ⟨layer, layerMember, rfl⟩, originalAccepted⟩, same⟩
  · rintro ⟨original, ⟨shape, member, accepted⟩, same⟩
    obtain ⟨layer, layerMember, rfl⟩ := List.mem_map.mp member
    have closed := (close_exact environment symbol layer (valid layer layerMember) term).mpr ⟨original, accepted, same⟩
    obtain ⟨shape, shapeMember, accepted⟩ := (alternatives_exact environment (roots symbol layer) term).mp closed
    exact ⟨shape, List.mem_flatMap.mpr ⟨layer, layerMember, shapeMember⟩, accepted⟩

/-- One retained grouped pair with the source's private indexed leaves. -/
def pairLayer (index : Nat) : Layer Nat :=
  .application (.base ⟨.index index, fun _ => True⟩ []) (singleton (.node (.index index) []))

/-- The corresponding decoder term before closing the grouped layer. -/
def pairTerm (index : Nat) : Term (Label Nat) :=
  .node .apply [.node (.index index) [], .node (.index index) []]

/-- A grouped pair still belongs to its source support before the faulty closing step. -/
theorem pair_accepted (environment : Env (Label Nat)) (index : Nat) :
    meaning environment (graph (pairLayer index)) (pairTerm index) := by
  simp only [pairLayer, graph, SupportSpine.graph]
  apply (SupportSpine.apply_exact environment _ _ _).mpr
  refine ⟨_, _, ?_, (singleton_exact environment _ _).mpr rfl, rfl⟩
  simp only [meaning]
  exact ⟨[], rfl, by simp [forest], trivial⟩

/-- Grouped pairs meet the same private-shape conditions as ungrouped application. -/
theorem pair_valid (index : Nat) : Valid (pairLayer index) := by
  simp [pairLayer, Valid, SupportSpine.Valid]

/-- The old multi-edge fallback rejects a concrete term returned by the decoder. -/
theorem old_closing_loses_term (environment : Env (Label Nat)) :
    meaning environment (node [pairLayer 0, pairLayer 1]) (pairTerm 0) ∧
      ¬meaning environment (edge (.user 7) [node [pairLayer 0, pairLayer 1]])
        (SupportTerms.labelTerm 7 (pairTerm 0)) := by
  constructor
  · apply (alternatives_exact environment _ _).mpr
    exact ⟨_, List.mem_map.mpr ⟨pairLayer 0, by simp, rfl⟩, pair_accepted environment 0⟩
  · rw [unary_exact]
    simp [pairTerm, SupportTerms.labelTerm, SupportTerms.applicationTermChildren,
      SupportTerms.applicationLeftChildren]

/-- Per-edge closing restores that term and the full callback image of both pairs. -/
theorem repaired_closing_accepts (environment : Env (Label Nat)) :
    meaning environment (closeNode 7 [pairLayer 0, pairLayer 1])
      (SupportTerms.labelTerm 7 (pairTerm 0)) := by
  apply (closeNode_exact environment 7 _ (by intro layer member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> exact pair_valid _) _).mpr
  exact ⟨pairTerm 0, (old_closing_loses_term environment).1, rfl⟩

end MicroCFTA.SupportAlternatives
