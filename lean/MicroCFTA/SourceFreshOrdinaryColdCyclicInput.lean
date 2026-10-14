import MicroCFTA.SourceFreshOrdinaryColdKeys
import MicroCFTA.SourceCyclicRowsReadback
import MicroCFTA.SourceCyclicRowsNativeGate

/-!
# Cyclic compiler input from actual repaired cold rows

The actual finite row domain declares its root. Each compiler row copies
the complete source symbol, ordered children, and constraint. The empty
root retains its empty row. No snapshot traversal or row adapter is assumed.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdCyclic
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceGuards SourceObservations SourceSymbolicIndex
open SourcePreparedSharedRows (reference encode)
open SourceColdSharedRows (Rows Supported)

/-- Actual row support and the exact finite domain declare the encoded root. -/
theorem root_key {Symbol Guard : Type} (rows : Rows Symbol Guard) (keys : List Nat) (value : Value Symbol Guard)
    (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys) (supported : Supported rows value) :
    encode value ∈ SourceDenseRows.keys (SourceColdSharedRows.table rows keys value) := by
  rw [SourceDenseRows.mem_keys]
  cases same : reference value with
  | none => simp only [SourceColdSharedRows.table, same, encode, SourceInternedRows.stateOf, List.map_cons, List.map_nil, List.mem_singleton]
  | some identity =>
      have present := (domain identity).mp (supported identity same)
      simp only [SourceColdSharedRows.table, same, SourceInternedRows.table, List.map_map, Function.comp_def,
        encode, SourceInternedRows.stateOf]
      exact List.mem_map.mpr ⟨identity, (CanonicalClasses.mem_sortedSet keys identity).mpr present, rfl⟩

variable (rows : Rows (Label Formula) (Constraint Formula)) (keys : List Nat)
    (value : Value (Label Formula) (Constraint Formula))
    (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (supported : Supported rows value)
    (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows keys value))
    (freeVariables : List Nat)
    (active : ∀ state edge, edge ∈ SourceInternedRows.lookup (SourceColdSharedRows.table rows keys value) state →
      SourceCompactGuards.ActiveOption edge.constraint.equalities)

local notation "raw" => SourceColdSharedRows.table rows keys value

/-- Construct every cyclic input field directly from the actual cold table. -/
def input : SourceCyclicRows.Input (SourceDenseRows.keys raw) Formula where
  root := ⟨encode value, root_key rows keys value domain supported⟩
  emptyRoot := (reference value).isNone
  freeVariables := freeVariables
  rows state := (SourceDenseRowsRestrict.rows raw closed state).map SourceCyclicRowsReadback.cyclicRow
  emptyRows := by
    intro empty
    have same : reference value = none := Option.isNone_iff_eq_none.mp empty
    simp [SourceDenseRowsRestrict.rows, SourceColdSharedRows.table, same, encode, SourceInternedRows.stateOf, SourceInternedRows.lookup]
  active := by
    intro state edge member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact active state.val (SourceDenseRowsRestrict.forget original)
      (SourceDenseRowsRestrict.rows_origin raw closed state original present)

/-- The constructed compiler root is the actual encoded physical root. -/
theorem root_value : (input rows keys value domain supported closed freeVariables active).root.val = encode value := rfl

/-- The constructed input retains the exact original guarded row function. -/
theorem original_eq [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula) :
    SourceCyclicRows.original formulas solver (input rows keys value domain supported closed freeVariables active) =
      SourceDenseRowsRestrict.automaton raw closed (acceptsConstraint formulas solver) := by
  funext state
  simp only [SourceCyclicRows.original, input, SourceDenseRowsRestrict.automaton,
    SourceSizedDecided.automaton, List.map_map]
  rfl

/-- The actual constraint precheck derives equality with structural rows before native ambiguity checks. -/
theorem checked_structural [DecidableEq Formula] [Ord Key]
    (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key)
    (checked : SourceCyclicAutomaton.hasConstraints (SourceCyclicRows.preparedInput
      (input rows keys value domain supported closed freeVariables active) order (fun _ => 0)) = false) :
    SourceCyclicRows.original formulas solver (input rows keys value domain supported closed freeVariables active) =
      SourceDenseRowsRestrict.automaton raw closed (fun _ _ => true) := by
  have plain := SourceCyclicAutomaton.checked_plain formulas solver _ checked
  change Decoder.Plain (SourceCyclicRows.original formulas solver (input rows keys value domain supported closed freeVariables active)) at plain
  rw [original_eq rows keys value domain supported closed freeVariables active formulas solver] at plain ⊢
  exact SourceCyclicRowsNativeGate.plain_rows raw closed (acceptsConstraint formulas solver) plain

/-- The real constraint precheck identifies the literal reference ambiguity scan with the structural finite-row scan. -/
theorem checked_ambiguity [DecidableEq Formula] [Ord Key]
    (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key)
    (checked : SourceCyclicAutomaton.hasConstraints (SourceCyclicRows.preparedInput
      (input rows keys value domain supported closed freeVariables active) order (fun _ => 0)) = false) :
    SourceCyclicAutomaton.hasAmbiguity formulas solver (SourceCyclicRows.preparedInput
      (input rows keys value domain supported closed freeVariables active) order (fun _ => 0))
      (SourceCyclicRows.pairs (SourceDenseRows.keys raw)) (SourceCyclicRows.pairs_complete _) =
      (SourceDenseRows.keys raw).attach.any (fun state => AutomatonAmbiguity.ambiguous (fun left right =>
        AutomatonAmbiguity.productiveRows
          (Language.intersect (SourceDenseRowsRestrict.automaton raw closed (fun _ _ => true))
            (SourceDenseRowsRestrict.automaton raw closed (fun _ _ => true)))
          (SourceCyclicRows.pairs (SourceDenseRows.keys raw)) (SourceCyclicRows.pairs_complete _) (left, right))
        (SourceDenseRowsRestrict.automaton raw closed (fun _ _ => true) state)) := by
  change (SourceDenseRows.keys raw).attach.any (fun state => AutomatonAmbiguity.ambiguous (fun left right =>
    AutomatonAmbiguity.productiveRows
      (Language.intersect (SourceCyclicRows.original formulas solver (input rows keys value domain supported closed freeVariables active))
        (SourceCyclicRows.original formulas solver (input rows keys value domain supported closed freeVariables active)))
      (SourceCyclicRows.pairs (SourceDenseRows.keys raw)) (SourceCyclicRows.pairs_complete _) (left, right))
    (SourceCyclicRows.original formulas solver (input rows keys value domain supported closed freeVariables active) state)) = _
  rw [checked_structural rows keys value domain supported closed freeVariables active formulas solver order checked]

/-- Actual input-table metadata recovers the complete guarded language of its original physical root. -/
theorem root_language [DecidableEq Formula] [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))]
    (source : InternedConstructorTemplates.State (Label Formula) (Constraint Formula))
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap source) (covered : Covered [] source)
    (guarded : InternedGuardedProbeHeap.Heap source) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap source)
    (replayed : SourceFreshOrdinaryColdSharedRows.ReplayedRows source rows)
    (resident : SourceColdSharedRows.ResidentRows source rows) (closedRows : SourceColdSharedRows.CoveredRows rows rows)
    (available : Available source value) (valueClosed : value.free = [])
    (formulas : Formulas Formula) (solver : Entailment Formula) (ambient : InternedGuardedLanguage.Env (Label Formula))
    (term : Term (Label Formula)) :
    Accepts (SourceCyclicRows.original formulas solver (input rows keys value domain supported closed freeVariables active))
      (input rows keys value domain supported closed freeVariables active).root term ↔
      InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term := by
  rw [original_eq rows keys value domain supported closed freeVariables active formulas solver]
  have language := SourceFreshOrdinaryColdKeys.finite_language source semantic covered guarded budgetHeap rows replayed resident closedRows
    keys domain value closed (input rows keys value domain supported closed freeVariables active).root (acceptsConstraint formulas solver) ambient term
  rw [root_value rows keys value domain supported closed freeVariables active,
    SourceFreshOrdinaryColdKeys.root_physical source semantic value available valueClosed] at language
  exact language

end MicroCFTA.SourceFreshOrdinaryColdCyclic
