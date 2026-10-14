import MicroCFTA.MergedFreshOrdinaryExposureCoverage

/-!
# Exact guarded language of general repaired cold reads

Each successful read returns exactly the constructor edges reached through
actual repaired unfolding in its final cache. Replay retains that language
in later complete caches. All source guards and child order remain present.
This does not identify the initial discarded-cache graph with the final one.
-/
namespace MicroCFTA.MergedFreshOrdinaryExposureLanguage
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedFreshProbeKeys
open MergedFreshOrdinaryGraph
open MergedFreshOrdinaryExposureOrigins
open MergedFreshOrdinaryExposureCoverage (nodeEdges_covers_fixed)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Every accepted finite term has a constructor edge at a finite repaired epsilon origin. -/
theorem accepts_origin [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (meaning : Guard → Language.Term Symbol → Bool) (value : Value Symbol Guard) (term : Language.Term Symbol)
    (accepted : EpsilonUnion.Accepts (graph state meaning) value term) :
    ∃ edge, Origin state [value] edge ∧ EdgeAccepts state meaning edge term := by
  induction accepted using EpsilonUnion.Accepts.rec (motive_2 := fun _ _ _ => True) with
  | @reference root target term member accepted ih =>
      obtain ⟨edge, origin, accepted⟩ := ih
      obtain ⟨source, reached, original⟩ := origin
      exact ⟨edge, ⟨source, EpsilonUnion.reach_trans _ root target source
        (.step (.seed List.mem_cons_self) member) reached, original⟩, accepted⟩
  | @node root edge terms member children guard ih =>
      cases root with
      | empty | reference | union | mu => simp [graph, MergedPhysicalComparison.constructorRows] at member
      | node entry own depth free =>
          obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
          exact ⟨original, ⟨_, .seed List.mem_cons_self, selected⟩, terms, rfl, children, guard⟩
  | nil => trivial
  | cons => trivial

/-- An accepted constructor edge at a repaired epsilon origin gives a complete accepted term. -/
theorem origin_accepts [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (meaning : Guard → Language.Term Symbol → Bool) (value : Value Symbol Guard) (edge : EdgeValue Symbol Guard)
    (origin : Origin state [value] edge) (term : Language.Term Symbol) (accepted : EdgeAccepts state meaning edge term) :
    EpsilonUnion.Accepts (graph state meaning) value term := by
  obtain ⟨source, reached, original⟩ := origin
  apply EpsilonUnion.along_reference (graph state meaning) value source reached term
  cases source with
  | empty | reference | union | mu => simp [InternedEdgeResidency.nodeEdges] at original
  | node entry own depth free => exact (node_exact state meaning entry own depth free term).mpr ⟨edge, original, accepted⟩

/-- Exact replay gives both edge coverage and guarded language in each later complete source cache. -/
theorem nodeEdges_exact [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Available before value) (edges : List (EdgeValue Symbol Guard)) (after view : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done edges after)
    (growth : Grows after view) (viewSemantic : SemanticHeap view) (viewCovered : Covered [] view)
    (viewAvailable : Available view value) (closed : value.free = []) :
    (∀ edge, edge ∈ edges ↔ Origin view [value] edge) ∧
      ∀ meaning term, EpsilonUnion.Accepts (graph view meaning) value term ↔
        ∃ edge ∈ edges, EdgeAccepts view meaning edge term := by
  have replay := MergedFreshOrdinaryColdReplay.nodeEdges_replay fuel value before view
    semantic.1.normal.facts.coherent.valid edges after done growth
  have exactEdges : ∀ edge, edge ∈ edges ↔ Origin view [value] edge := fun edge =>
    ⟨nodeEdges_origins fuel value before semantic covered available edges after done view growth edge,
      nodeEdges_covers_fixed fuel view viewSemantic viewCovered value viewAvailable closed edges replay edge⟩
  refine ⟨exactEdges, ?_⟩
  intro meaning term
  constructor
  · intro accepted
    obtain ⟨edge, origin, accepted⟩ := accepts_origin view meaning value term accepted
    exact ⟨edge, (exactEdges edge).mpr origin, accepted⟩
  · rintro ⟨edge, member, accepted⟩
    exact origin_accepts view meaning value edge ((exactEdges edge).mp member) term accepted

/-- Each actual completed closed read has its exact guarded language in the actual returned cache. -/
theorem actual_exact [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Available before value) (closed : value.free = []) (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done edges after) :
    (∀ edge, edge ∈ edges ↔ Origin after [value] edge) ∧
      ∀ meaning term, EpsilonUnion.Accepts (graph after meaning) value term ↔
        ∃ edge ∈ edges, EdgeAccepts after meaning edge term := by
  have checked := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel value before semantic covered available closed
  have afterSemantic : SemanticHeap after := by simpa only [done, MergedSourceExposure.Result.state] using checked.semantic
  have afterCovered : Covered [] after := by simpa only [done, MergedSourceExposure.Result.state] using checked.covered
  have growth : Grows before after := by simpa only [done, MergedSourceExposure.Result.state] using checked.growth
  have history : Extends before.nodes.issued after.nodes.issued := by
    simpa only [done, MergedSourceExposure.Result.state] using checked.history
  exact nodeEdges_exact fuel value before semantic covered available edges after after done (grows_refl _)
    afterSemantic afterCovered (available.grows before after growth history) closed

end MicroCFTA.MergedFreshOrdinaryExposureLanguage
