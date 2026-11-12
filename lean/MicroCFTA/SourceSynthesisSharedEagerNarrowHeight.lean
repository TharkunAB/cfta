import MicroCFTA.SourcePruningOuterNarrow
import MicroCFTA.SourcePruningEnumerationIdentity
import MicroCFTA.MergedOrdinaryHeight

/-!
# Ordinary height at actual outer narrowing results

Narrowing filters complete ordinary rows before actual node reconstruction.
The result retains an ordinary head and cannot exceed the input height.
Recursive boundaries and complete eager traversal are outside this law.
-/
namespace MicroCFTA.SourceSynthesisSharedEagerNarrowHeight
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourcePruningRecordTypes (Metadata)
variable {Guard Typing Key : Type}
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Node" => Value Symbol Guard
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Guard
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual successful narrowing retains the original ordinary height bound. -/
theorem narrow_ordinary_height
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Node → Bool) (metadata : Metadata Typing)
    (fuel uv : Nat) (value : Node) (before : NativeHeap)
    (result : Node) (after : NativeHeap)
    (facts : InternedNestedFacts.Facts before) (available : Available before value)
    (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (observed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value before =
      .done result after) :
    SourceEqualityRequiredCache.Ordinary result ∧
      MergedOrdinaryHeight.height result ≤ MergedOrdinaryHeight.height value := by
  by_cases inside : uv ∈ metadata.types
  · have same : value = result := (MergedSourceComparison.Result.done.inj
      ((SourcePruningOuterNarrow.narrow_type holeKey fits admits metadata fuel uv value before inside).symm.trans
        observed)).1
    rw [← same]
    exact ⟨ordinary, Nat.le_refl _⟩
  · cases value with
    | empty =>
        have fallback := SourcePruningOuterNarrow.narrow_fallback holeKey fits admits metadata fuel uv
          .empty before (by intro entry body depth shape impossible; cases impossible) inside
        have same : (.empty : Node) = result := (MergedSourceComparison.Result.done.inj
          ((fallback.trans (SourcePruningEnumerationIdentity.narrowAt_empty fits admits fuel _ before)).symm.trans
            observed)).1
        rw [← same]
        exact ⟨trivial, Nat.le_refl _⟩
    | node entry rows depth free =>
        rw [SourcePruningOuterNarrow.narrow_fallback holeKey fits admits metadata fuel uv
          (.node entry rows depth free) before
          (by intro other body nested shape impossible; cases impossible) inside] at observed
        change MergedSourceComparison.Result.done
          (run (makeNode (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv)))) before).1
          (run (makeNode (rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv)))) before).2 =
            .done result after at observed
        let selected := rows.filter (SourcePruningNativeView.keeps fits admits (holeKey metadata.typing uv))
        have resident : InternedNestedProvenance.Edges before selected := by
          intro edge member
          exact resident_edges before facts.linked _ available.resident edge (List.mem_filter.mp member).1
        have bounded : ∀ edge ∈ selected,
            MergedOrdinaryHeight.edgeHeight edge + 1 ≤
              MergedOrdinaryHeight.height (.node entry rows depth free) := by
          intro edge member
          have edgeBound := (MergedOrdinaryHeight.edgesHeight_le rows (MergedOrdinaryHeight.edgesHeight rows)).mp
            (Nat.le_refl _) edge (List.mem_filter.mp member).1
          exact Nat.succ_le_succ edgeBound
        have same : (run (makeNode selected) before).1 = result :=
          (MergedSourceComparison.Result.done.inj observed).1
        rw [← same]
        exact ⟨SourceEqualityRequiredCache.node_ordinary selected before facts resident,
          MergedOrdinaryHeight.makeNode_bound selected before facts.coherent facts.linked resident _ bounded⟩
    | reference | union | mu => exact False.elim ordinary

end MicroCFTA.SourceSynthesisSharedEagerNarrowHeight
