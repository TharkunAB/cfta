import MicroCFTA.InternedNormalizedCombinedCompletion
import MicroCFTA.InternedDeepErasureExamples
import MicroCFTA.InternedCombinedConstruction

/-!
# Retained pending frames contain nested parent and grandparent erasure

The outer two binders retain their enclosing references directly. Their
live nested subprogram reads both active names and removes those reads
below nested Mu and root self unions. One symbol is shared throughout.
-/
namespace MicroCFTA.InternedNormalizedCombinedExamples
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedDependencies InternedOuterErasure InternedNormalizedPreparedSites
open InternedNormalizedCombinedConstruction InternedNestedFacts InternedNestedProvenance
open InternedProbeProvenance InternedNestedCoverage
open InternedDeepErasureExamples (tower leaf tower_admitted tower_scoped)

/-- Each declared discarded edge can erase its selected slot without reading any other outer input. -/
theorem leaf_outer_erased (slot count : Nat) : OuterErased count (leaf slot) :=
  .dead count slot [.mk 0 () []] 0 () (fun index member => by simp [edgeInputs, manyInputs] at member)

/-- The complete nested family erases all enclosing inputs together, while protecting its own local prefix. -/
theorem tower_outer_erased (smart : Bool) (count protectedCount : Nat) : OuterErased protectedCount (tower smart count) := by
  induction count generalizing protectedCount with
  | zero => exact .unused protectedCount _ (fun index member => by simp [tower, inputs, edgeInputs, manyInputs] at member)
  | succ count ih =>
      rw [tower]
      apply OuterErased.binder
      apply OuterErased.union
      intro child member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .unused _ _ (fun index member => by simp only [inputs, List.mem_singleton] at member; subst index; omega)
      · apply OuterErased.node
        intro symbol constraint children member selected included
        have same : EdgeSyntax.mk symbol constraint children = EdgeSyntax.mk 0 () [.var 0, tower smart count, leaf 1, leaf 2] := by simpa using member
        cases same
        simp only [List.mem_cons, List.not_mem_nil, or_false] at included
        rcases included with rfl | rfl | rfl | rfl
        · exact .unused _ _ (fun index member => by simp only [inputs, List.mem_singleton] at member; subst index; omega)
        · exact ih (protectedCount + 1)
        · exact leaf_outer_erased 1 _
        · exact leaf_outer_erased 2 _

/-- The new prepared-leaf rule admits actual erased enclosing reads at every finite inner depth. -/
theorem tower_leaf (smart : Bool) (count : Nat) : Leaf (tower smart count) :=
  .inr ⟨tower_outer_erased smart count 0, tower_admitted smart count⟩

/-- The retained middle frame supplies both active enclosing names to its normalized inner subprogram. -/
def middle (smart : Bool) (count : Nat) : Syntax Nat Unit := .binder smart (.node
  [.mk 0 () [.var 0], .mk 0 () [.var 1], .mk 0 () [tower smart count]])

/-- The outer retained frame constructs the middle frame after retaining its own local reference. -/
def program (smart : Bool) (count : Nat) : Syntax Nat Unit := .binder smart (.node
  [.mk 0 () [.var 0], .mk 0 () [middle smart count]])

/-- Both retained frames and the normalized erased leaf satisfy one source-derived completion grammar. -/
theorem program_combined (smart : Bool) (count : Nat) : Combined 0 (program smart count) := by
  have varCombined (depth index : Nat) : Combined depth (.var index : Syntax Nat Unit) := by rw [Combined]; exact .inr trivial
  have leafCombined : Combined 2 (tower smart count) := by rw [Combined.eq_def]; exact .inl (tower_leaf smart count)
  have inner : Combined 1 (middle smart count) := by
    rw [middle, Combined]
    right
    constructor
    · intro index bound
      have same : index = 0 := by omega
      subst index
      exact ⟨0, (), by simp⟩
    · simp only [EdgesCombined, ManyCombined]
      exact ⟨⟨varCombined 2 0, trivial⟩, ⟨varCombined 2 1, trivial⟩, ⟨leafCombined, trivial⟩, trivial⟩
  rw [program, Combined]
  right
  constructor
  · intro index impossible
    omega
  · simp only [EdgesCombined, ManyCombined]
    exact ⟨⟨varCombined 1 0, trivial⟩, ⟨inner, trivial⟩, trivial⟩

/-- Every variable read in the whole mixed family has an actual enclosing source binder. -/
theorem program_scoped (smart : Bool) (count : Nat) : Scoped 0 (program smart count) := by
  simp only [program, middle, Scoped, EdgesScoped, ManyScoped]
  exact ⟨⟨by omega, trivial⟩, ⟨⟨⟨by omega, trivial⟩, ⟨by omega, trivial⟩,
    ⟨tower_scoped smart count 2 (by omega), trivial⟩, trivial⟩, trivial⟩, trivial⟩

/-- A grandparent-reading tower cannot use the earlier lexically closed prepared-leaf rule. -/
theorem outside_previous (smart : Bool) (count depth : Nat) :
    ¬ InternedCombinedConstruction.Combined depth (tower smart (count + 1)) := by
  intro earlier
  rw [InternedCombinedConstruction.Combined.eq_def] at earlier
  rcases earlier with leaf | direct
  · have member := InternedDeepErasureExamples.tower_reads_grandparent smart count
    rw [leaf.1] at member
    cases member
  · simp only [tower] at direct

/-- Actual first execution completes with both pending retention and normalized erasure in the same source trace. -/
theorem program_complete (smart : Bool) (count : Nat) :
    ∃ value final, build (program smart count) [] empty = .done value final ∧
      Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build (program smart count) [] after = .done value after := by
  obtain ⟨value, final, completed⟩ := closed_completes (program smart count) (program_combined smart count)
  have verified := closed_verified (program smart count)
  refine ⟨value, final, completed, ?_, closed_covered _ value final completed,
    verified.result value final completed, fun after growth => empty_replay _ value final after completed growth⟩
  simpa only [completed, Outcome.state] using verified.facts

/-- No finite mixed raw or smart program can report an unfinished canonical request. -/
theorem program_not_pending (smart : Bool) (count : Nat) (key : InternedBinderProtocol.NodeKey) (state : State Nat Unit) :
    build (program smart count) [] empty ≠ .pending key state := by
  obtain ⟨value, final, completed, _⟩ := program_complete smart count
  rw [completed]
  intro impossible
  cases impossible

end MicroCFTA.InternedNormalizedCombinedExamples
