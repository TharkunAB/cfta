import MicroCFTA.SourceSymbolicIndex

/-!
# One source index at every sufficiently large execution bound

Every inverse query eventually has one fixed answer. A finite accepted
language gives one bound for all its inverse queries. This bound fixes
the decoder order as well as the inverse ranks.
-/
namespace MicroCFTA.SourceSymbolicStableIndex
open Language SourceGuards SourceObservations SymbolicDriver SymbolicGraphView
open SymbolicInternedView DistinctRank SourceSymbolicIndex

/-- Pointwise eventual answers give one common stabilization bound on a finite input list. -/
theorem finite_stabilization (inputs : List Input) (observe : Nat → Input → Output)
    (eventual : ∀ input ∈ inputs, ∃ bound answer, ∀ fuel, bound ≤ fuel → observe fuel input = answer) :
    ∃ bound, ∀ input ∈ inputs, ∀ first second, bound ≤ first → bound ≤ second →
      observe first input = observe second input := by
  induction inputs with
  | nil => exact ⟨0, by simp⟩
  | cons head rest ih =>
      obtain ⟨headBound, answer, headStable⟩ := eventual head (by simp)
      obtain ⟨tailBound, tailStable⟩ := ih (fun input member => eventual input (by simp [member]))
      refine ⟨max headBound tailBound, ?_⟩
      intro input member first second firstEnough secondEnough
      rcases List.mem_cons.mp member with rfl | member
      · exact (headStable first (by omega)).trans (headStable second (by omega)).symm
      · exact tailStable input member first second (by omega) (by omega)

/-- One fixed distinct index agrees with every later source decoder and inverse worker. -/
theorem stable_source_index [DecidableEq Formula] [Ord (Label Formula)] [Ord Order] [DecidableEq Payload]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (shape : Payload → List (Language.Edge Nat (Label Formula)))
    (graph : Graph (Label Formula)) (order : Label Formula → Order)
    (constraints : SymbolicDriver.Edge (Label Formula) → Constraint Formula)
    (compiled : CompiledRows graph constraints)
    (view : ClosedOperationRows graph (fun edge => acceptsConstraint formulas solver (constraints edge)))
    (allocated : AllocatedRows shape
      (automaton graph (fun edge => acceptsConstraint formulas solver (constraints edge))))
    (fallback : Term (Label Formula)) (root : Nat) :
    let valid := Accepts (automaton graph (fun edge => acceptsConstraint formulas solver (constraints edge))) root
    ∃ index : Index valid, ∃ bound,
      (∀ fuel, bound ≤ fuel →
        cardinality graph fuel root = .ok (index.count : Int) ∧
        (∀ rank : Fin index.count,
          unrank graph order fuel root rank.val = .ok (index.decode rank).val) ∧
        (∀ term : {t // valid t},
          rankOf graph order fuel root term.val = .ok (some (index.encode term).val))) ∧
      (∀ term, ∃ inverseBound, ∀ fuel, max bound inverseBound ≤ fuel →
        (rankOf graph order fuel root term = .ok none ↔ ¬ valid term)) := by
  classical
  let guard := fun edge => acceptsConstraint formulas solver (constraints edge)
  have scores := compiled_score formulas solver graph constraints compiled
  obtain ⟨count, sourceBound, sourceCorrect⟩ :=
    source_index formulas solver shape graph order constraints compiled view allocated fallback root
  obtain ⟨initial, _, _, _, _, _⟩ := sourceCorrect sourceBound (Nat.le_refl _)
  obtain ⟨apiBound, _, inverse⟩ :=
    allocated_total_api shape graph order guard view allocated fallback scores root
  have eventual : ∀ term ∈ initial.members, ∃ bound answer, ∀ fuel, bound ≤ fuel →
      rankOf graph order fuel root term = answer := by
    intro term _
    obtain ⟨inverseBound, answer, correct⟩ := inverse term
    exact ⟨max apiBound inverseBound, .ok answer, fun fuel enough => (correct fuel enough).1⟩
  obtain ⟨uniformBound, stable⟩ :=
    finite_stabilization initial.members (fun fuel term => rankOf graph order fuel root term) eventual
  let bound := max sourceBound uniformBound
  obtain ⟨index, indexCount, _, _, indexInverse, rejected⟩ := sourceCorrect bound (Nat.le_max_left _ _)
  refine ⟨index, bound, ?_, rejected⟩
  intro fuel enough
  obtain ⟨later, laterCount, counted, laterDecode, laterInverse, _⟩ := sourceCorrect fuel (by dsimp [bound] at enough; omega)
  have fixedInverse : ∀ term : {t // Accepts (automaton graph guard) root t},
      rankOf graph order fuel root term.val = .ok (some (index.encode term).val) := by
    intro term
    have same := stable term.val ((initial.exact term.val).mpr term.property) fuel bound
      (by dsimp [bound] at enough; omega) (Nat.le_max_right _ _)
    exact same.trans (indexInverse term)
  refine ⟨by simpa only [indexCount] using counted, ?_, fixedInverse⟩
  intro rank
  let term := index.decode rank
  have laterRank := laterInverse term
  have fixedRank := fixedInverse term
  rw [Index.encode_decode] at fixedRank
  have rankSame : (later.encode term).val = rank.val := by
    have answers := laterRank.symm.trans fixedRank
    exact Int.ofNat.inj (Option.some.inj (Except.ok.inj answers))
  have decoded := laterDecode (later.encode term)
  rw [Index.decode_encode, rankSame] at decoded
  exact decoded

end MicroCFTA.SourceSymbolicStableIndex
