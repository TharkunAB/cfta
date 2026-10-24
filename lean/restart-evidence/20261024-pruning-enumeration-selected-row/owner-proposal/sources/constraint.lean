import MicroCFTA.SourceIndicatorCompiler
import MicroCFTA.SymbolicTotalAPI
import MicroCFTA.System

/-!
# Source constraints, actual rank order, and requested term weights

Successful source indicator compilation supplies the numeric guard law.
The allocated graph workers then give an index in their actual decoder order.
The proof list records that order; the symbolic worker does not enumerate it.
-/
namespace MicroCFTA.SourceSymbolicIndex
open Language SourceGuards SourceObservations SymbolicDriver SymbolicGraphView
open SymbolicInternedView DistinctRank

/-- The two constraint fields read by the source indicator compiler. -/
structure Constraint (Formula : Type) where
  equalities : Option (List (List Path))
  guard : Guard Formula

/-- Complete acceptance checks stored equalities and the current public guard evaluator. -/
noncomputable def acceptsConstraint [DecidableEq Formula] (formulas : Formulas Formula)
    (solver : Entailment Formula) (constraint : Constraint Formula)
    (term : Term (Label Formula)) : Bool :=
  ConstraintIndicators.equalityValue (classTest term) constraint.equalities &&
    decide (SourceBooleanEntry.evaluateGuard formulas solver constraint.guard term = .yes)

/-- Row readback retains the exact successful source compiler output. -/
def CompiledRows (graph : Graph (Label Formula))
    (constraints : SymbolicDriver.Edge (Label Formula) → Constraint Formula) : Prop :=
  ∀ node edge, edge ∈ graph.edges node →
    SourceIndicatorCompiler.constraintIndicators (constraints edge).equalities (constraints edge).guard =
      .ok edge.indicators

/-- The source adapter derives the semantic premise of the symbolic workers. -/
theorem compiled_score [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (graph : Graph (Label Formula)) (constraints : SymbolicDriver.Edge (Label Formula) → Constraint Formula)
    (compiled : CompiledRows graph constraints) (node edge) (present : edge ∈ graph.edges node)
    (term : Term (Label Formula)) :
    ConstraintIndicators.score (classTest term) edge.indicators =
      Lattice.indicator (acceptsConstraint formulas solver (constraints edge) term) :=
  SourceIndicatorCompiler.successful_constraint_score formulas solver term _ _ _ (compiled node edge present)

/-- Read a successful worker value. The fallback is unreachable at certified valid ranks. -/
def decoded [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel root : Nat) (fallback : Term Symbol)
    (rank : Fin count) : Term Symbol :=
  match unrank graph order fuel root rank.val with
  | .ok term => term
  | .error _ => fallback

private theorem decoded_eq [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel root : Nat) (fallback : Term Symbol)
    (rank : Fin count) (term : Term Symbol)
    (success : unrank graph order fuel root rank.val = .ok term) :
    decoded graph order fuel root fallback rank = term := by
  simp only [decoded, success]

/-- Worker totality, acceptedness, and its unique inverse construct a distinct index in source order. -/
def workerIndex [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (fuel root count : Nat)
    (fallback : Term Symbol) (Valid : Term Symbol → Prop)
    (total : ∀ rank : Fin count, ∃ term,
      unrank graph order fuel root rank.val = .ok term ∧ Valid term)
    (cover : ∀ term, Valid term → ∃ rank : Fin count,
      unrank graph order fuel root rank.val = .ok term ∧
      rankOf graph order fuel root term = .ok (some rank.val) ∧
      ∀ other : Fin count, unrank graph order fuel root other.val = .ok term → other = rank) : Index Valid where
  members := List.ofFn (decoded graph order fuel root fallback)
  nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro first second firstBound secondBound same
    have firstBound' : first < count := by simpa using firstBound
    have secondBound' : second < count := by simpa using secondBound
    let a : Fin count := ⟨first, firstBound'⟩
    let b : Fin count := ⟨second, secondBound'⟩
    obtain ⟨left, leftDecode, leftValid⟩ := total a
    obtain ⟨right, rightDecode, _⟩ := total b
    have equality : left = right := by
      simp only [List.getElem_ofFn] at same
      change decoded graph order fuel root fallback a = decoded graph order fuel root fallback b at same
      rw [decoded_eq graph order fuel root fallback a left leftDecode,
        decoded_eq graph order fuel root fallback b right rightDecode] at same
      exact same
    subst right
    obtain ⟨rank, _, _, unique⟩ := cover left leftValid
    exact congrArg Fin.val ((unique a leftDecode).trans (unique b rightDecode).symm)
  exact term := by
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨rank, same⟩
      obtain ⟨value, success, valid⟩ := total rank
      rw [decoded_eq graph order fuel root fallback rank value success] at same
      exact same ▸ valid
    · intro valid
      obtain ⟨rank, success, _, _⟩ := cover term valid
      exact ⟨rank, decoded_eq graph order fuel root fallback rank term success⟩

/-- The actual source compiler and workers yield a complete rank interface in decoder order. -/
theorem source_index [DecidableEq Formula] [Ord (Label Formula)] [Ord Order] [DecidableEq Payload]
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
    ∃ count bound, ∀ fuel, bound ≤ fuel →
      ∃ index : Index valid,
        index.count = count ∧ cardinality graph fuel root = .ok (count : Int) ∧
        (∀ rank : Fin index.count,
          unrank graph order fuel root rank.val = .ok (index.decode rank).val) ∧
        (∀ term : {t // valid t},
          rankOf graph order fuel root term.val = .ok (some (index.encode term).val)) ∧
        (∀ term, ∃ inverseBound, ∀ later, max fuel inverseBound ≤ later →
          (rankOf graph order later root term = .ok none ↔ ¬ valid term)) := by
  classical
  let guard := fun edge => acceptsConstraint formulas solver (constraints edge)
  have scores := compiled_score formulas solver graph constraints compiled
  obtain ⟨fullBound, full⟩ := allocated_full_index shape graph order guard view allocated fallback scores root
  obtain ⟨apiBound, api, inverse⟩ := allocated_total_api shape graph order guard view allocated fallback scores root
  let budget := closedSourceBudget graph guard view id (allocated_rank shape _ allocated)
  let meaning := closedMeaning graph guard view budget
  let count := (meaning.terms root).length
  refine ⟨count, max fullBound apiBound, ?_⟩
  intro fuel enough
  obtain ⟨counted, _, covered⟩ := full fuel (by omega)
  obtain ⟨_, total⟩ := api fuel (by omega)
  let index := workerIndex graph order fuel root count fallback (Accepts (automaton graph guard) root) total covered
  have indexCount : index.count = count := List.length_ofFn
  have decode : ∀ rank : Fin index.count,
      unrank graph order fuel root rank.val = .ok (index.decode rank).val := by
    intro rank
    let original : Fin count := ⟨rank.val, by simpa [indexCount] using rank.isLt⟩
    obtain ⟨term, success, _⟩ := total original
    have value : (index.decode rank).val = term := by
      change (List.ofFn (decoded (count := count) graph order fuel root fallback))[rank.val]'(by simpa only [List.length_ofFn] using original.isLt) = term
      simp only [List.getElem_ofFn]
      exact decoded_eq graph order fuel root fallback original term success
    rw [value]
    exact success
  refine ⟨index, indexCount, counted, decode, ?_, ?_⟩
  · intro term
    obtain ⟨rank, success, ranked, unique⟩ := covered term.val term.property
    have ours := decode (index.encode term)
    rw [index.decode_encode term] at ours
    have equal := unique ⟨(index.encode term).val, by simpa [indexCount] using (index.encode term).isLt⟩ ours
    rw [ranked]
    exact congrArg (fun n : Nat => Except.ok (some (n : Int))) (congrArg Fin.val equal).symm
  · intro term
    obtain ⟨inverseBound, answer, eventual⟩ := inverse term
    refine ⟨inverseBound, ?_⟩
    intro later sufficient
    obtain ⟨ranked, answerLaw⟩ := eventual later (by omega)
    rw [ranked]
    cases answer with
    | none => exact ⟨fun _ => answerLaw, fun _ => rfl⟩
    | some rank =>
      constructor
      · intro impossible; cases impossible
      · intro rejected; exact False.elim (rejected answerLaw.1)

/-- Every source rank has the requested term mass, independently of decoder order. -/
theorem source_probability [DecidableEq Symbol] (index : Index (α := Term Symbol) Valid)
    (weight : Term Symbol → Rat) (rank : Fin index.count) :
    Probability.eventMass (fun term => decide (term = (index.decode rank).val)) (System.requested index weight) =
      weight (index.decode rank).val / Probability.total (System.weightedMembers index weight) :=
  System.requested_term_probability index weight _ (index.decode rank).property

/-- Requested nonnegative weights with positive total mass normalize to a probability law. -/
theorem source_probability_normalized (index : Index (α := Term Symbol) Valid)
    (weight : Term Symbol → Rat) (nonnegative : ∀ term, Valid term → 0 ≤ weight term)
    (positive : 0 < Probability.total (System.weightedMembers index weight)) :
    Probability.IsProbability (System.requested index weight) :=
  System.requested_probability index weight nonnegative positive

end MicroCFTA.SourceSymbolicIndex
