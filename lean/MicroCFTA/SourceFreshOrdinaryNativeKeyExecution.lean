import MicroCFTA.SourceFreshOrdinaryNativeCallbackDeterministic
import MicroCFTA.SourceFreshOrdinaryColdKeys
import MicroCFTA.SourceCyclicRows

/-!
# Complete warm callbacks for the actual finite input carrier

The input cold table supplies canonical original operands and their exact
languages. Later ready caches retain those operands. Every checked key-pair
callback completes and returns the finite reference product test, with its
actual cache available to the next source query.
-/
namespace MicroCFTA.SourceFreshOrdinaryNativeKeyCallback
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows ResidentRows CoveredRows)
open SourceFreshOrdinaryColdSharedRows (ReplayedRows)
open SourceFreshOrdinaryColdKeys (physical)

/-- Actual finite keys derive complete exact warm callbacks in every later ready source cache. -/
theorem complete_keys [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (source : InternedConstructorTemplates.State Symbol Guard)
    (semantic : SemanticHeap source) (covered : Covered [] source)
    (guarded : InternedGuardedProbeHeap.Heap source) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap source)
    (rows : Rows Symbol Guard) (replayed : ReplayedRows source rows)
    (resident : ResidentRows source rows) (closedRows : CoveredRows rows rows)
    (keys : List Nat) (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (root : Value Symbol Guard) (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows keys root))
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ready : SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin state)
    (growth : Grows source state.machine.heap) (history : Extends source.nodes.issued state.machine.heap.nodes.issued)
    (left right : SourceDenseRows.Member (SourceDenseRows.keys (SourceColdSharedRows.table rows keys root)))
    (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, physical source left.val, physical source right.val⟩ .pure) state) :
    ∃ result after,
      SourceFreshOrdinaryNativeCallback.Execution emptyGuard conjoin (physical source left.val) (physical source right.val) state result after ∧
      SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin after ∧ Extension state.machine after.machine ∧
      result = AutomatonAmbiguity.productiveRows
        (Language.intersect
          (SourceDenseRowsRestrict.automaton (SourceColdSharedRows.table rows keys root) closed (fun _ _ => true))
          (SourceDenseRowsRestrict.automaton (SourceColdSharedRows.table rows keys root) closed (fun _ _ => true)))
        (SourceCyclicRows.pairs (SourceDenseRows.keys (SourceColdSharedRows.table rows keys root)))
        (SourceCyclicRows.pairs_complete _) (left, right) := by
  have first := SourceFreshOrdinaryColdKeys.physical_record source semantic rows resident left.val
    (SourceFreshOrdinaryColdKeys.table_declared rows keys domain root left.val left.property)
  have second := SourceFreshOrdinaryColdKeys.physical_record source semantic rows resident right.val
    (SourceFreshOrdinaryColdKeys.table_declared rows keys domain root right.val right.property)
  obtain ⟨result, after, execution, retained, extension, common⟩ :=
    SourceFreshOrdinaryNativeCallback.complete emptyGuard conjoin state ready (physical source left.val) (physical source right.val)
      first.2.2.1 second.2.2.1 (first.1.grows source state.machine.heap growth history)
      (second.1.grows source state.machine.heap growth history) first.2.1 second.2.1 ranges
  refine ⟨result, after, execution, retained, extension, ?_⟩
  apply Bool.eq_iff_iff.mpr
  rw [common (fun _ _ => False)]
  let A := SourceDenseRowsRestrict.automaton (SourceColdSharedRows.table rows keys root) closed (fun _ _ => true)
  let pairs := SourceCyclicRows.pairs (SourceDenseRows.keys (SourceColdSharedRows.table rows keys root))
  have pairComplete := SourceCyclicRows.pairs_complete (SourceDenseRows.keys (SourceColdSharedRows.table rows keys root))
  have language (key : SourceDenseRows.Member (SourceDenseRows.keys (SourceColdSharedRows.table rows keys root))) (term : Term Symbol) :
      Accepts A key term ↔ InternedGuardedLanguage.meaning (fun _ _ => true) (fun _ _ => False) (physical source key.val) term :=
    SourceFreshOrdinaryColdKeys.finite_language source semantic covered guarded budgetHeap rows replayed resident closedRows
      keys domain root closed key (fun _ _ => true) (fun _ _ => False) term
  have plain : Decoder.Plain A := by
    intro key edge member term
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
    rfl
  constructor
  · rintro ⟨term, leftTerm, rightTerm⟩
    exact AutomatonAmbiguity.table_test_covers A pairs pairComplete left right term
      ((language left term).mpr leftTerm) ((language right term).mpr rightTerm)
  · intro found
    obtain ⟨term, leftTerm, rightTerm⟩ := AutomatonAmbiguity.table_test_witness A plain pairs pairComplete left right found
    exact ⟨term, (language left term).mp leftTerm, (language right term).mp rightTerm⟩

end MicroCFTA.SourceFreshOrdinaryNativeKeyCallback
