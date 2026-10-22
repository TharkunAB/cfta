import MicroCFTA.SourcePhysicalSharedRows

/-!
# Exact language of physical plain rows in the shared adapter

The proof reads each reachable physical payload at its canonical identity.
It derives child provenance and exact ordered row copying locally. No
whole-graph language equivalence or product-row premise is assumed.
-/
namespace MicroCFTA.SourcePhysicalSharedRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency SourceInternedIntersectionRows
open Language SymbolicGraphView

/-- Replace an ordered relation using membership in both original lists. -/
theorem all₂_both_imp (R S : A → B → Prop) (as : List A) (bs : List B)
    (related : All₂ R as bs) (change : ∀ a ∈ as, ∀ b ∈ bs, R a b → S a b) : All₂ S as bs := by
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons (change _ List.mem_cons_self _ List.mem_cons_self head)
        (ih (fun a member b included => change a (List.mem_cons_of_mem _ member) b (List.mem_cons_of_mem _ included)))

/-- Every interpreted physical row retains plain available children in their original positions. -/
theorem row_children (state : State Symbol Unit) (facts : Facts state) (value : Value Symbol Unit)
    (available : Available state value) (plain : Plain value) (edge : Language.Edge (Value Symbol Unit) Symbol)
    (member : edge ∈ rows value) (child : Value Symbol Unit) (inside : child ∈ edge.children) :
    Available state child ∧ Plain child := by
  obtain ⟨stored, selected, rfl⟩ := List.mem_map.mp member
  exact ⟨child_available state facts value available stored selected child inside,
    plain.children value stored selected child inside⟩

/-- Shared-row root language is derived from actual physical record readback. -/
theorem language_exact (state : State Symbol Unit) (facts : Facts state) (value : Value Symbol Unit)
    (available : Available state value) (plain : Plain value) (term : Term Symbol) :
    Language.Accepts (SourceInternedRows.graph (heap state) (fun _ _ => true)) (encode value) term ↔
      SourceInternedIntersectionRows.Accepts value term := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ value, Available state value → Plain value →
      (Language.Accepts (SourceInternedRows.graph (heap state) (fun _ _ => true)) (encode value) term ↔
        SourceInternedIntersectionRows.Accepts value term)) generalizing value with
  | node symbol children ih =>
      unfold SourceInternedIntersectionRows.Accepts
      rw [Language.accepts_node_iff, Language.accepts_node_iff, graph_readback state facts value available plain]
      constructor
      · rintro ⟨edge, member, label, runs, guard⟩
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        have mapped := (all₂_map_iff _ encode original.children children).mp runs
        refine ⟨original, present, label, ?_, guard⟩
        apply all₂_both_imp _ _ _ _ mapped
        intro child childIn term termIn accepted
        have provenance := row_children state facts value available plain original present child childIn
        exact (ih term termIn child provenance.1 provenance.2).mp accepted
      · rintro ⟨edge, member, label, runs, guard⟩
        refine ⟨renameEdge encode edge, List.mem_map.mpr ⟨edge, member, rfl⟩, label, ?_, guard⟩
        apply (all₂_map_iff _ encode edge.children children).mpr
        apply all₂_both_imp _ _ _ _ runs
        intro child childIn term termIn accepted
        have provenance := row_children state facts value available plain edge member child childIn
        exact (ih term termIn child provenance.1 provenance.2).mpr accepted
  | nil => simp_all
  | cons first rest head tail =>
      rename_i term member value available plain
      rcases List.mem_cons.mp member with rfl | member
      · exact head value available plain
      · exact tail term member value available plain

/-- Actual completed toRows output has precisely the original physical plain language. -/
theorem toRows_language (state : State Symbol Unit) (facts : Facts state) (value : Value Symbol Unit)
    (available : Available state value) (plain : Plain value) (fuel : Nat)
    (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Unit)))
    (done : SourceInternedRows.toRows (heap state) fuel (reference value) = some raw) (term : Term Symbol) :
    Language.Accepts (SourceRowsMinimumAdapter.automaton raw) (encode value) term ↔
      SourceInternedIntersectionRows.Accepts value term :=
  (SourceRowsMinimumPublic.root_language (heap state) fuel (reference value) raw done term).trans
    (language_exact state facts value available plain term)

/-- Physical epsilon semantics agrees with the actual shared-row language on plain inputs. -/
theorem physical_exact [DecidableEq Symbol] (state : State Symbol Unit) (facts : Facts state) (value : Value Symbol Unit)
    (available : Available state value) (plain : Plain value) (term : Term Symbol) :
    Language.Accepts (SourceInternedRows.graph (heap state) (fun _ _ => true)) (encode value) term ↔
      EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state (fun _ _ => true)) value term :=
  (language_exact state facts value available plain term).trans (plain_exact state value plain term).symm

/-- Later physical effects preserve the exposed language of every earlier available plain root. -/
theorem language_stable (before after : State Symbol Unit) (beforeFacts : Facts before) (afterFacts : Facts after)
    (growth : Grows before after) (history : Cache.Extends before.nodes.issued after.nodes.issued)
    (value : Value Symbol Unit) (available : Available before value) (plain : Plain value) (term : Term Symbol) :
    Language.Accepts (SourceInternedRows.graph (heap after) (fun _ _ => true)) (encode value) term ↔
      Language.Accepts (SourceInternedRows.graph (heap before) (fun _ _ => true)) (encode value) term :=
  (language_exact after afterFacts value (available.grows before after growth history) plain term).trans
    (language_exact before beforeFacts value available plain term).symm

end MicroCFTA.SourcePhysicalSharedRows
