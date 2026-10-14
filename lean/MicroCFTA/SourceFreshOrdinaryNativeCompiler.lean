import MicroCFTA.SourceFreshOrdinaryColdCyclicInput
import MicroCFTA.SourceFreshOrdinaryNativeKeyScan

/-!
# Actual native scans in the cyclic compiler

Empty, open, and constrained roots stop before native overlap checks.
The native scan retains its actual returned cache. A false scan result
continues to finite canonical preparation. The complete compiler result
is compared with the reference result, including every source error.
-/
namespace MicroCFTA.SourceFreshOrdinaryNativeCompiler
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceGuards SourceObservations SourceSymbolicIndex
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows Supported ResidentRows CoveredRows)
open SourceFreshOrdinaryColdSharedRows (ReplayedRows)

section Input
variable {width : Nat} {Formula Key : Type} [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))]
    (emptyGuard : Constraint Formula) (conjoin : Constraint Formula → Constraint Formula → Constraint Formula)
    (source : InternedConstructorTemplates.State (Label Formula) (Constraint Formula))
    (rows : Rows (Label Formula) (Constraint Formula)) (keys : List Nat)
    (value : Value (Label Formula) (Constraint Formula))
    (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (supported : Supported rows value)
    (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows keys value))
    (freeVariables : List Nat)
    (active : ∀ state edge, edge ∈ SourceInternedRows.lookup (SourceColdSharedRows.table rows keys value) state →
      SourceCompactGuards.ActiveOption edge.constraint.equalities)
    (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key)

local notation "raw" => SourceColdSharedRows.table rows keys value
local notation "input" => SourceFreshOrdinaryColdCyclic.input rows keys value domain supported closed freeVariables active
local notation "base" => SourceCyclicRows.preparedInput input order (fun _ => 0)
local notation "K" => SourceDenseRows.Member (SourceDenseRows.keys raw)
local notation "N" => SourceRecursiveIntersectionThunks.State width (Label Formula) (Constraint Formula)
local notation "A" => SourceDenseRowsRestrict.automaton raw closed (fun _ _ => true)
local notation "queries" => SourceFreshOrdinaryNativeKeyScan.edgeQueries (List.attach (SourceDenseRows.keys raw)) A
local notation "edgeStep" => SourceFreshOrdinaryNativeKeyScan.EdgeExecution emptyGuard conjoin source Subtype.val
local notation "edgeRange" => SourceFreshOrdinaryNativeKeyScan.EdgeAllowed emptyGuard conjoin source Subtype.val
local notation "invariant" => SourceFreshOrdinaryNativeKeyScan.Invariant emptyGuard conjoin source

/-- Only the actual scan branch requires reached-query native word checks. -/
noncomputable def Ranges (state : N) : Prop :=
  if (input).emptyRoot then True
  else if !(input).freeVariables.isEmpty then True
  else if SourceCyclicAutomaton.hasConstraints base then True
  else SourceShortCircuitScan.Ranges false edgeStep edgeRange queries state

/-- Actual compiler execution preserves source precheck order and all native scan cache effects. -/
inductive Execution : N → Except SourceCyclicAutomaton.Error (Automaton K (Label Formula)) → N → Prop where
  | empty (state : N) (emptyRoot : (input).emptyRoot = true) : Execution state (.ok (fun _ => [])) state
  | openRoot (state : N) (nonempty : (input).emptyRoot = false) (openRoot : (input).freeVariables.isEmpty = false) :
      Execution state (.error .openAutomaton) state
  | constrained (state : N) (nonempty : (input).emptyRoot = false) (closedRoot : (input).freeVariables.isEmpty = true)
      (checked : SourceCyclicAutomaton.hasConstraints base = true) : Execution state (.error .constrainedEdges) state
  | ambiguous (state after : N) (nonempty : (input).emptyRoot = false) (closedRoot : (input).freeVariables.isEmpty = true)
      (checked : SourceCyclicAutomaton.hasConstraints base = false)
      (scan : SourceShortCircuitScan.Run false edgeStep queries state true after) : Execution state (.error .ambiguousAutomaton) after
  | accepted (state after : N) (classes : K → Nat) (nonempty : (input).emptyRoot = false) (closedRoot : (input).freeVariables.isEmpty = true)
      (checked : SourceCyclicAutomaton.hasConstraints base = false)
      (scan : SourceShortCircuitScan.Run false edgeStep queries state false after)
      (canonical : SourceCyclicRows.canonical formulas solver input order = some classes) :
      Execution state (.ok (SourceCyclicAutomaton.ordered formulas solver (SourceCyclicRows.preparedInput input order classes))) after

local notation "execution" => Execution emptyGuard conjoin source rows keys value domain supported closed freeVariables active formulas solver order
local notation "rangeCheck" => Ranges emptyGuard conjoin source rows keys value domain supported closed freeVariables active order

variable (semantic : SemanticHeap source) (covered : Covered [] source)
    (guarded : InternedGuardedProbeHeap.Heap source) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap source)
    (replayed : ReplayedRows source rows) (resident : ResidentRows source rows) (closedRows : CoveredRows rows rows)

include semantic covered guarded budgetHeap replayed resident closedRows

/-- Every actual completed compiler preserves the next native cache invariant and the literal reference result. -/
theorem execution_correct (state : N) (valid : invariant state) (ranges : rangeCheck state)
    (result : Except SourceCyclicAutomaton.Error (Automaton K (Label Formula))) (after : N)
    (actual : execution state result after) :
    invariant after ∧ SourceCyclicRows.compile formulas solver input order = some result := by
  cases actual with
  | empty emptyRoot =>
      exact ⟨valid, by simp [SourceCyclicRows.compile, emptyRoot]⟩
  | openRoot nonempty openRoot =>
      exact ⟨valid, by simp [SourceCyclicRows.compile, nonempty, openRoot]⟩
  | constrained nonempty closedRoot checked =>
      exact ⟨valid, by simp [SourceCyclicRows.compile, nonempty, closedRoot, checked]⟩
  | ambiguous after nonempty closedRoot checked scan =>
      have reached : SourceShortCircuitScan.Ranges false edgeStep edgeRange queries state := by
        simpa only [Ranges, nonempty, closedRoot, checked, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using ranges
      obtain ⟨retained, exact⟩ := SourceFreshOrdinaryNativeKeyScan.scan_correct emptyGuard conjoin source semantic covered guarded budgetHeap
        rows replayed resident closedRows keys domain value closed state valid reached true after scan
      have classified := SourceFreshOrdinaryColdCyclic.checked_ambiguity rows keys value domain supported closed freeVariables active
        formulas solver order checked
      have ambiguous : SourceCyclicAutomaton.hasAmbiguity formulas solver base
          (SourceCyclicRows.pairs (SourceDenseRows.keys raw)) (SourceCyclicRows.pairs_complete _) = true := classified.trans exact.symm
      exact ⟨retained, by simp [SourceCyclicRows.compile, nonempty, closedRoot, checked, ambiguous]⟩
  | accepted after classes nonempty closedRoot checked scan canonical =>
      have reached : SourceShortCircuitScan.Ranges false edgeStep edgeRange queries state := by
        simpa only [Ranges, nonempty, closedRoot, checked, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using ranges
      obtain ⟨retained, exact⟩ := SourceFreshOrdinaryNativeKeyScan.scan_correct emptyGuard conjoin source semantic covered guarded budgetHeap
        rows replayed resident closedRows keys domain value closed state valid reached false after scan
      have classified := SourceFreshOrdinaryColdCyclic.checked_ambiguity rows keys value domain supported closed freeVariables active
        formulas solver order checked
      have unambiguous : SourceCyclicAutomaton.hasAmbiguity formulas solver base
          (SourceCyclicRows.pairs (SourceDenseRows.keys raw)) (SourceCyclicRows.pairs_complete _) = false := classified.trans exact.symm
      exact ⟨retained, by simp [SourceCyclicRows.compile, nonempty, closedRoot, checked, unambiguous, canonical]⟩

/-- Every actual compiler branch has finite execution and the same complete result as the reference compiler. -/
theorem complete (state : N) (valid : invariant state) (ranges : rangeCheck state) :
    ∃ result after, execution state result after ∧ invariant after ∧
      SourceCyclicRows.compile formulas solver input order = some result := by
  have finish (result : Except SourceCyclicAutomaton.Error (Automaton K (Label Formula))) (after : N)
      (actual : execution state result after) :
      ∃ result after, execution state result after ∧ invariant after ∧
        SourceCyclicRows.compile formulas solver input order = some result := by
    have correct := execution_correct emptyGuard conjoin source rows keys value domain supported closed freeVariables active formulas solver order
      semantic covered guarded budgetHeap replayed resident closedRows state valid ranges result after actual
    exact ⟨result, after, actual, correct⟩
  cases emptyRoot : (input).emptyRoot with
  | true => exact finish _ _ (.empty state emptyRoot)
  | false =>
      cases closedRoot : (input).freeVariables.isEmpty with
      | false => exact finish _ _ (.openRoot state emptyRoot closedRoot)
      | true =>
          cases checked : SourceCyclicAutomaton.hasConstraints base with
          | true => exact finish _ _ (.constrained state emptyRoot closedRoot checked)
          | false =>
              have reached : SourceShortCircuitScan.Ranges false edgeStep edgeRange queries state := by
                simpa only [Ranges, emptyRoot, closedRoot, checked, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using ranges
              obtain ⟨result, after, scan, _, _⟩ := SourceFreshOrdinaryNativeKeyScan.scan_complete emptyGuard conjoin
                source semantic covered guarded budgetHeap rows replayed resident closedRows keys domain value closed state valid reached
              cases result with
              | true => exact finish _ _ (.ambiguous state after emptyRoot closedRoot checked scan)
              | false =>
                  obtain ⟨classes, canonical⟩ := SourceCyclicRows.canonical_finite formulas solver input order
                  exact finish _ _ (.accepted state after classes emptyRoot closedRoot checked scan canonical)

variable (available : Available source value) (valueClosed : value.free = [])
include available valueClosed

/-- Actual successful native compilation has finite exact distinct classes and the same class sequence as the reference worker. -/
theorem class_correct (state : N) (valid : invariant state) (ranges : rangeCheck state)
    (output : Automaton K (Label Formula)) (after : N) (actual : execution state (.ok output) after)
    (ambient : InternedGuardedLanguage.Env (Label Formula)) (size : Nat) :
    SourceSizedTableEvaluation.Evaluation output (size + 1) size (input).root
      (RecursiveSize.countAt output size (input).root) (RecursiveSize.compileAt output size (input).root) ∧
      (RecursiveSize.enumerate output size (input).root).Nodup ∧
      (∀ term, term ∈ RecursiveSize.enumerate output size (input).root ↔
        InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term ∧ RecursiveSize.nodeSize term = size) ∧
      RecursiveSize.countAt output size (input).root = (RecursiveSize.enumerate output size (input).root).length ∧
      (∀ rank, Decoder.decode (RecursiveSize.compileAt output size (input).root) rank =
        (RecursiveSize.enumerate output size (input).root)[rank]?) ∧
      SourceSizedReference.classes output size (input).root = RecursiveSize.enumerate output size (input).root := by
  have success := (execution_correct emptyGuard conjoin source rows keys value domain supported closed freeVariables active formulas solver order
    semantic covered guarded budgetHeap replayed resident closedRows state valid ranges (.ok output) after actual).2
  obtain ⟨finite, unique, language, counted, decoded⟩ := SourceCyclicRows.class_correct formulas solver input order output success size
  obtain ⟨plain, unambiguous, _⟩ := SourceCyclicRows.compile_exact formulas solver input order output success
  refine ⟨finite, unique, ?_, counted, decoded, SourceSizedReference.classes_eq_enumerate output plain unambiguous size (input).root⟩
  intro term
  exact (language term).trans (and_congr
    (SourceFreshOrdinaryColdCyclic.root_language rows keys value domain supported closed freeVariables active source
      semantic covered guarded budgetHeap replayed resident closedRows available valueClosed formulas solver ambient term) Iff.rfl)

/-- Both actual distinct-term inverse APIs and exact bounded rejection follow the same native compiler result. -/
theorem query_inverses (state : N) (valid : invariant state) (ranges : rangeCheck state)
    (output : Automaton K (Label Formula)) (after : N) (actual : execution state (.ok output) after)
    (ambient : InternedGuardedLanguage.Env (Label Formula)) :
    (∀ position term, TablePosition.positionsOf output term (input).root = some position ↔
      SizedRank.replayPosition output (input).root position = some term) ∧
      (∀ bound rank, (∃ term, RecursiveUnambiguous.selectAtMost output (input).root bound rank = some term) ↔
        rank < RecursiveSize.countAtMost output bound (input).root) ∧
      (∀ bound rank term, RecursiveUnambiguous.rankAtMost output (input).root bound term = some rank ↔
        RecursiveUnambiguous.selectAtMost output (input).root bound rank = some term) ∧
      (∀ bound term, RecursiveUnambiguous.rankAtMost output (input).root bound term = none ↔
        ¬(InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term ∧ RecursiveSize.nodeSize term ≤ bound)) := by
  have success := (execution_correct emptyGuard conjoin source rows keys value domain supported closed freeVariables active formulas solver order
    semantic covered guarded budgetHeap replayed resident closedRows state valid ranges (.ok output) after actual).2
  obtain ⟨positions, total, inverses, rejected⟩ := SourceCyclicRows.query_inverses formulas solver input order output success
  refine ⟨positions, total, inverses, ?_⟩
  intro bound term
  exact (rejected bound term).trans (not_congr (and_congr
    (SourceFreshOrdinaryColdCyclic.root_language rows keys value domain supported closed freeVariables active source
      semantic covered guarded budgetHeap replayed resident closedRows available valueClosed formulas solver ambient term) Iff.rfl))

/-- The reference sequence of an actual native compiler result has finite classes, distinct size order, and both term-rank inverses. -/
theorem reference_laws (state : N) (valid : invariant state) (ranges : rangeCheck state)
    (output : Automaton K (Label Formula)) (after : N) (actual : execution state (.ok output) after)
    (ambient : InternedGuardedLanguage.Env (Label Formula)) :
    let classes := fun size => SourceSizedReference.classes output size (input).root
    (∀ size, SourceSizedReference.ClassEvaluation output (size + 1) size (input).root (classes size)) ∧
      (∀ bound, (SourceSizedQueries.through classes bound).Nodup ∧
        (SourceSizedQueries.through classes bound).Pairwise (fun first second => RecursiveSize.nodeSize first ≤ RecursiveSize.nodeSize second) ∧
        ∀ term, term ∈ SourceSizedQueries.through classes bound ↔
          InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term ∧ RecursiveSize.nodeSize term ≤ bound) ∧
      (∀ term, (∃ position, SourceSizedQueries.rank classes RecursiveSize.nodeSize term = some position) ↔
        InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term) ∧
      (∀ term position, SourceSizedQueries.rank classes RecursiveSize.nodeSize term = some position ↔
        SourceSizedQueries.unrank classes position = some term) := by
  have success := (execution_correct emptyGuard conjoin source rows keys value domain supported closed freeVariables active formulas solver order
    semantic covered guarded budgetHeap replayed resident closedRows state valid ranges (.ok output) after actual).2
  obtain ⟨_, _, outputLanguage⟩ := SourceCyclicRows.compile_exact formulas solver input order output success
  have language (term : Term (Label Formula)) : Accepts output (input).root term ↔
      InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term :=
    (outputLanguage term).trans (SourceFreshOrdinaryColdCyclic.root_language rows keys value domain supported closed freeVariables active source
      semantic covered guarded budgetHeap replayed resident closedRows available valueClosed formulas solver ambient term)
  refine ⟨(fun size => SourceSizedReference.classes_evaluation_bound output size (input).root), ?_, ?_, ?_⟩
  · intro bound
    refine ⟨SourceSizedReferenceAPI.through_nodup output (input).root bound,
      SourceSizedReferenceAPI.through_ordered output (input).root bound, ?_⟩
    intro term
    rw [SourceSizedReferenceAPI.through_exact, language]
  · intro term
    rw [SourceSizedReferenceAPI.rank_exists_iff, language]
  · intro term position
    exact ⟨SourceSizedReferenceAPI.unrank_rank output (input).root term position,
      SourceSizedReferenceAPI.rank_unrank output (input).root term position⟩

end Input
end MicroCFTA.SourceFreshOrdinaryNativeCompiler
