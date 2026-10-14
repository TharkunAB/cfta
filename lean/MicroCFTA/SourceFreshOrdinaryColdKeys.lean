import MicroCFTA.SourceFreshOrdinaryColdGuardedExact
import MicroCFTA.SourceDenseRowsRestrict

/-!
# Physical operands at actual finite cold-table keys

Each declared nonempty key reads its canonical closed source record.
The empty key reads the empty value. The complete table language at every
such key equals the independent guarded language of that physical operand.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdKeys
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows ResidentRows CoveredRows Supported)
open SourceFreshOrdinaryColdSharedRows (ReplayedRows)
open SourcePreparedSharedRows (reference encode)

/-- Read the canonical physical operand of an explicit source state. -/
def physical (state : State Symbol Guard) : SourceInternedRows.State → Value Symbol Guard
  | .empty => .empty
  | .interned identity => (SourcePreparedSharedRows.read state identity).getD .empty

/-- A key is empty or names a row in the actual completed map. -/
def Declared (rows : Rows Symbol Guard) : SourceInternedRows.State → Prop
  | .empty => True
  | .interned identity => ∃ edges, rows identity = some edges

/-- Resident rows supply closed original operands and exact state readback. -/
theorem physical_record (state : State Symbol Guard) (semantic : SemanticHeap state)
    (rows : Rows Symbol Guard) (resident : ResidentRows state rows)
    (key : SourceInternedRows.State) (declared : Declared rows key) :
    Available state (physical state key) ∧ (physical state key).free = [] ∧
      SourceRecursiveIntersectionInputView.Original (physical state key) ∧
      encode (physical state key) = key ∧ Supported rows (physical state key) := by
  cases key with
  | empty =>
      refine ⟨empty_available state, rfl, .empty, rfl, ?_⟩
      intro identity impossible
      cases impossible
  | interned identity =>
      obtain ⟨edges, present⟩ := declared
      obtain ⟨value, available, same, closed, _, _⟩ := resident identity edges present
      have read := SourcePreparedSharedRows.read_identity state semantic.1.normal.facts value available identity same
      have decoded : physical state (.interned identity) = value := by simp only [physical, read, Option.getD_some]
      rw [decoded]
      refine ⟨available, closed, SourceRecursiveIntersectionOriginalOutput.closed_original value state
        semantic.1.normal.facts.coherent available closed, ?_, ?_⟩
      · simp only [encode, same, SourceInternedRows.stateOf]
      · intro other otherRef
        have equal := Option.some.inj (same.symm.trans otherRef)
        simpa only [← equal] using Exists.intro edges present

/-- Later constructor effects retain the identical canonical physical operand at every declared key. -/
theorem physical_grows (before after : State Symbol Guard) (semantic : SemanticHeap before)
    (afterSemantic : SemanticHeap after) (rows : Rows Symbol Guard) (resident : ResidentRows before rows)
    (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued)
    (key : SourceInternedRows.State) (declared : Declared rows key) : physical after key = physical before key := by
  cases key with
  | empty => rfl
  | interned identity =>
      obtain ⟨edges, present⟩ := declared
      obtain ⟨value, available, same, _, _, _⟩ := resident identity edges present
      have first := SourcePreparedSharedRows.read_identity before semantic.1.normal.facts value available identity same
      have second := SourcePreparedSharedRows.read_identity after afterSemantic.1.normal.facts value
        (available.grows before after growth history) identity same
      simp only [physical, first, second]

/-- The actual raw-table key inventory contains only declared physical operands. -/
theorem table_declared (rows : Rows Symbol Guard) (keys : List Nat)
    (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (root : Value Symbol Guard) (key : SourceInternedRows.State)
    (member : key ∈ SourceDenseRows.keys (SourceColdSharedRows.table rows keys root)) : Declared rows key := by
  rw [SourceDenseRows.mem_keys] at member
  cases found : reference root with
  | none =>
      simp only [SourceColdSharedRows.table, found, List.map_cons, List.map_nil, List.mem_singleton] at member
      subst key
      trivial
  | some identity =>
      simp only [SourceColdSharedRows.table, found, SourceInternedRows.table, List.map_map, Function.comp_def] at member
      obtain ⟨selected, inside, rfl⟩ := List.mem_map.mp member
      exact (domain selected).mpr ((CanonicalClasses.mem_sortedSet keys selected).mp inside)

/-- Every declared key of a complete finite table has its own exact independent physical language. -/
theorem table_language [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (guarded : InternedGuardedProbeHeap.Heap state)
    (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state) (rows : Rows Symbol Guard)
    (replayed : ReplayedRows state rows) (resident : ResidentRows state rows) (closedRows : CoveredRows rows rows)
    (keys : List Nat) (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (key : SourceInternedRows.State) (declared : Declared rows key)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows holds
      (SourceInternedRows.table (SourceColdSharedRows.heap rows) keys))) key term ↔
      InternedGuardedLanguage.meaning holds ambient (physical state key) term := by
  obtain ⟨available, closed, _, same, supported⟩ := physical_record state semantic rows resident key declared
  rw [SourceColdSharedRows.table_graph rows keys domain holds]
  have exactLanguage := (SourceFreshOrdinaryColdTableLanguage.language_exact state semantic covered rows holds replayed resident closedRows
    (physical state key) available closed supported term).trans
    (SourceFreshOrdinaryColdGuardedExact.graph_exact state semantic covered guarded budgetHeap rows replayed resident closedRows
      (physical state key) available closed supported holds ambient term)
  simpa only [same] using exactLanguage

/-- The empty-root special case and every actual nonempty table key have exact physical language. -/
theorem actual_table_language [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (guarded : InternedGuardedProbeHeap.Heap state)
    (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state) (rows : Rows Symbol Guard)
    (replayed : ReplayedRows state rows) (resident : ResidentRows state rows) (closedRows : CoveredRows rows rows)
    (keys : List Nat) (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (root : Value Symbol Guard) (key : SourceInternedRows.State)
    (member : key ∈ SourceDenseRows.keys (SourceColdSharedRows.table rows keys root))
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows holds
      (SourceColdSharedRows.table rows keys root))) key term ↔
      InternedGuardedLanguage.meaning holds ambient (physical state key) term := by
  have declared := table_declared rows keys domain root key member
  cases found : reference root with
  | some identity =>
      simpa only [SourceColdSharedRows.table, found] using
        table_language state semantic covered guarded budgetHeap rows replayed resident closedRows keys domain key declared holds ambient term
  | none =>
      have same : key = .empty := by
        simpa only [SourceDenseRows.mem_keys, SourceColdSharedRows.table, found, List.map_cons, List.map_nil,
          List.mem_singleton] using member
      subst key
      simp only [physical, InternedGuardedLanguage.meaning]
      constructor
      · intro accepted
        cases accepted with
        | node edge children present runs guard =>
            simp [SourceColdSharedRows.table, found, SourceInternedRows.interpretedRows, FTAValidation.rowFor] at present
      · intro impossible
        cases impossible

/-- Finite compiler states recover the language of their actual closed physical operands. -/
theorem finite_language [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (guarded : InternedGuardedProbeHeap.Heap state)
    (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state) (rows : Rows Symbol Guard)
    (replayed : ReplayedRows state rows) (resident : ResidentRows state rows) (closedRows : CoveredRows rows rows)
    (keys : List Nat) (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (root : Value Symbol Guard) (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows keys root))
    (key : SourceDenseRows.Member (SourceDenseRows.keys (SourceColdSharedRows.table rows keys root)))
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    Accepts (SourceDenseRowsRestrict.automaton (SourceColdSharedRows.table rows keys root) closed holds) key term ↔
      InternedGuardedLanguage.meaning holds ambient (physical state key.val) term :=
  (SourceDenseRowsRestrict.accepts_exact _ closed holds key term).trans
    (actual_table_language state semantic covered guarded budgetHeap rows replayed resident closedRows keys domain root
      key.val key.property holds ambient term)

end MicroCFTA.SourceFreshOrdinaryColdKeys
