import MicroCFTA.SourceInternedIntersectionRowsPhysical

/-!
# Completion of the ordinary physical construction kernel

A sufficient descent bound fixes the complete constructor computation.
Extra fuel changes neither the returned record nor any cache state. The
bound is derived from the immutable left record. This statement concerns
the ordinary kernel. It does not assert native binder or memo completion.
-/
namespace MicroCFTA.SourceInternedIntersectionRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency MergedPhysicalGroupCalls Language

/-- Ordered list evaluation needs agreement only on its actual requests. -/
theorem mapCalls_congr (first second : A → Work Symbol Guard B) (requests : List A)
    (same : ∀ request ∈ requests, first request = second request) :
    mapCalls first requests = mapCalls second requests := by
  induction requests with
  | nil => rfl
  | cons request rest ih =>
      simp only [mapCalls, same request List.mem_cons_self,
        ih (fun value member => same value (List.mem_cons_of_mem _ member))]

/-- Equal child computations produce the identical complete edge computation. -/
theorem edge_congr (first second : Value Symbol Unit × Value Symbol Unit → Work Symbol Unit (Value Symbol Unit))
    (pair : EdgeValue Symbol Unit × EdgeValue Symbol Unit)
    (same : ∀ request ∈ pair.1.children.zip pair.2.children, first request = second request) :
    edge first pair = edge second pair := by
  unfold edge
  split
  · rw [mapCalls_congr first second _ same]
  · rfl

/-- Equal computations on actual matching child pairs fix the complete node computation. -/
theorem node_congr [DecidableEq Symbol]
    (first second : Value Symbol Unit × Value Symbol Unit → Work Symbol Unit (Value Symbol Unit))
    (left right : List (EdgeValue Symbol Unit))
    (same : ∀ pair ∈ pairs left right, ∀ request ∈ pair.1.children.zip pair.2.children, first request = second request) :
    node first left right = node second left right := by
  unfold node
  rw [mapCalls_congr (edge first) (edge second) _ (fun pair member => edge_congr first second pair (same pair member))]

/-- Once descent completes, extra fuel leaves the entire effectful computation unchanged. -/
theorem intersect_stable [DecidableEq Symbol] (fuel : Nat) (pair : Value Symbol Unit × Value Symbol Unit)
    (bounded : Bounded fuel pair.1) (extra : Nat) :
    intersect (fuel + extra) pair = intersect fuel pair := by
  induction fuel generalizing pair extra with
  | zero =>
      cases extra with
      | zero => rfl
      | succ extra =>
          change nodeEdges pair.1 = [] at bounded
          simp [intersect, node, bounded, pairs, SymbolicHashJoin.hashJoin, mapCalls, Work.bind,
            makeNode, surviving, canonicalEdges, EnumerationBuilderCaches.canonicalIds]
  | succ fuel ih =>
      rw [Nat.succ_add]
      simp only [intersect]
      apply node_congr
      intro edgePair member request included
      have original := (pairs_member _ _ edgePair).mp member
      exact ih request (bounded edgePair.1 original.1 request.1 (List.of_mem_zip included).1) extra

/-- The derived structural-size bound fixes both actual output and final cache. -/
theorem run_complete [DecidableEq Symbol] (left right : Value Symbol Unit) (state : State Symbol Unit) (extra : Nat) :
    run (intersect (sizeOf left + extra) (left, right)) state =
      run (intersect (sizeOf left) (left, right)) state := by
  rw [intersect_stable (sizeOf left) (left, right) (bounded_size _ _ (Nat.le_refl _)) extra]

/-- A completed plain ordinary intersection combines exact physical language and stable effects. -/
theorem completed_physical_exact [DecidableEq Symbol] (left right : Value Symbol Unit) (state : State Symbol Unit)
    (facts : Facts state) (leftAvailable : Available state left) (rightAvailable : Available state right)
    (leftPlain : Plain left) (rightPlain : Plain right) :
    ∃ fuel result,
      (∀ extra, run (intersect (fuel + extra) (left, right)) state = result) ∧
      Facts result.2 ∧ Available result.2 result.1 ∧ Plain result.1 ∧
      ∀ term, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph result.2 (fun _ _ => true)) result.1 term ↔
        EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state (fun _ _ => true)) left term ∧
        EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state (fun _ _ => true)) right term := by
  exact ⟨sizeOf left, run (intersect (sizeOf left) (left, right)) state, run_complete left right state,
    physical_finite_exact left right state facts leftAvailable rightAvailable leftPlain rightPlain⟩

end MicroCFTA.SourceInternedIntersectionRows
