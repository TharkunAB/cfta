import MicroCFTA.SourceCurrentOriginalRowClusterScan
import MicroCFTA.SourceCurrentSameSymbolEdgeComparisonDomains

namespace MicroCFTA.SourceCurrentOriginalRowClusterCompletion
open Cache Language IntersectSchedule InternedConstructorTemplates InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionInputView InternedProbeProvenance
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Wrapper" => SourceCurrentSameSymbolEdgeControl.State
local notation "ScanControl" => SourceCurrentOriginalRowClusterScan.Control
local notation "Stable" => SourceCurrentSameSymbolEdgeStable.Stable
local notation "NativeIdle" => SourceRecursiveIntersectionNative.Idle
local notation "guardHolds" => (@SourceEqualityPCSGuard.holds FullSyntax.Formula FormulaExecutable.formulaDecidableEq)
variable {width : Nat}

/-- Compose a yielded scan prefix with the remaining scan fuel. -/
private theorem execute_yielded_add
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (used rest : Nat) (control next : ScanControl) (before middle : Wrapper width)
    (observed : SourceCurrentOriginalRowClusterScan.execute used control before = .yielded next middle) :
    SourceCurrentOriginalRowClusterScan.execute (used + rest) control before =
      SourceCurrentOriginalRowClusterScan.execute rest next middle := by
  induction used generalizing control before with
  | zero =>
      have same : control = next ∧ before = middle := by
        simpa only [SourceCurrentOriginalRowClusterScan.execute,
          SourceCurrentOriginalRowClusterScan.Outcome.yielded.injEq] using observed
      rcases same with ⟨rfl, rfl⟩
      simp only [Nat.zero_add]
  | succ used ih =>
      cases one : SourceCurrentOriginalRowClusterScan.step control before <;>
        simp only [SourceCurrentOriginalRowClusterScan.execute, one] at observed
      case yielded following after =>
        simpa only [Nat.succ_add, SourceCurrentOriginalRowClusterScan.execute, one] using
          ih following after observed
      all_goals cases observed

/-- Complete the current scan to a smaller cluster boundary with the same global history. -/
private theorem scan_boundary_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputModel : InputMeaning (view source (guardHolds formulas solver)))
    (inputRanked : RankedInput (view source (guardHolds formulas solver)) inputModel.valid)
    (parent : Value Symbol Guard)
    (original : OriginalInput source (inputOf parent))
    (available : Available source parent) (closed : parent.free = [])
    (symbol : Symbol)
    (initialDomains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (initialValid : Cache.Valid initialDomains)
    (pivot : Edge) (remaining incomparableReversed keptReversed : List Edge)
    (before : Wrapper (bits + 2))
    (stable : Stable (view source (guardHolds formulas solver)) inputModel inputRanked
      (guardHolds formulas solver) before)
    (good : Good before.checked)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (guardHolds formulas solver)) inputModel inputRanked
      (guardHolds formulas solver) before.checked.native)
    (semantic : SemanticReady before.checked.native.machine.heap)
    (growth : Grows source before.checked.native.machine.heap)
    (history : Extends source.nodes.issued before.checked.native.machine.heap.nodes.issued)
    (allocations : SourceRecursiveIntersectionDomainAllocation.Trace
      (SourceRecursiveIntersectionSourceInventory.domains source)
      initialDomains before.checked.native.machine.domains)
    (idle : NativeIdle before.checked.native)
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits
      ⟨source.nodes.next, source.edges.next,
        initialDomains.next + (SourceRecursiveIntersectionSourceInventory.domains source).length, 0⟩) :
    let rows := (nodeEdges parent).filter (fun edge => decide (edge.entry.key.symbol = symbol))
    pivot ∈ rows →
    (∀ edge ∈ remaining, edge ∈ rows) →
    (∀ edge ∈ incomparableReversed, edge ∈ rows) →
    (∀ edge ∈ keptReversed, edge ∈ rows) →
    ∃ (used : Nat) (next newKept : List Edge) (after : Wrapper (bits + 2)),
      0 < used ∧
      SourceCurrentOriginalRowClusterScan.execute used
        (.scan pivot remaining incomparableReversed keptReversed) before =
          .yielded (.cluster next newKept) after ∧
      next.length < 1 + remaining.length + incomparableReversed.length ∧
      next.length + newKept.length ≤
        1 + remaining.length + incomparableReversed.length + keptReversed.length ∧
      (∀ edge ∈ next, edge ∈ rows) ∧
      (∀ edge ∈ newKept, edge ∈ rows) ∧
      Good after.checked ∧
      SourceCurrentAllocatedNativeContextCache.Contextual
        (view source (guardHolds formulas solver)) inputModel inputRanked
        (guardHolds formulas solver) after.checked.native ∧
      SemanticReady after.checked.native.machine.heap ∧
      Extension before.checked.native.machine after.checked.native.machine ∧
      Stable (view source (guardHolds formulas solver)) inputModel inputRanked
        (guardHolds formulas solver) after ∧
      NativeIdle after.checked.native ∧
      Extends before.memo.table after.memo.table ∧
      FlatMemoThunk.Returned before.memo after.memo ∧
      SourceRecursiveIntersectionDomainAllocation.Trace
        (SourceRecursiveIntersectionSourceInventory.domains source)
        initialDomains after.checked.native.machine.domains := by
  dsimp only
  revert stable good contextual semantic growth history allocations idle
  induction remaining generalizing incomparableReversed keptReversed before with
  | nil =>
      intro stable good contextual semantic _growth _history allocations idle
        pivotMember _remainingMembers incomparableMembers keptMembers
      refine ⟨1, incomparableReversed.reverse, pivot :: keptReversed, before, by omega,
        rfl, ?_, ?_, ?_, ?_, good, contextual, semantic, Extension.refl _, stable, idle,
        extends_refl _, FlatMemoThunk.Returned.refl _, allocations⟩
      · simp only [List.length_reverse, List.length_nil]
        omega
      · simp only [List.length_reverse, List.length_cons, List.length_nil]
        omega
      · simpa only [List.mem_reverse] using incomparableMembers
      · intro edge member
        rcases List.mem_cons.mp member with rfl | member
        · exact pivotMember
        · exact keptMembers edge member
  | cons candidate tail ih =>
      intro stable good contextual semantic growth history allocations idle
        pivotMember remainingMembers incomparableMembers keptMembers
      have candidateMember := remainingMembers candidate List.mem_cons_self
      have tailMembers := fun edge member =>
        remainingMembers edge (List.mem_cons_of_mem candidate member)
      have symbols : pivot.entry.key.symbol = candidate.entry.key.symbol :=
        (of_decide_eq_true (List.mem_filter.mp pivotMember).2).trans
          (of_decide_eq_true (List.mem_filter.mp candidateMember).2).symm
      obtain ⟨fuel, common, middle, done, _resident, _law, midGood, midContextual,
          midSemantic, extension, midStable, midIdle, tables, retained, midTrace⟩ :=
        SourceCurrentSameSymbolEdgeComparisonDomains.original_rows_complete bits source facts
          formulas solver inputModel inputRanked parent parent original original available available
          closed closed pivot candidate (List.mem_filter.mp pivotMember).1
          (List.mem_filter.mp candidateMember).1 symbols initialDomains initialValid before stable
          good contextual semantic growth history allocations idle room
      obtain ⟨used, _positive, _bound, resumed⟩ :=
        SourceCurrentOriginalRowClusterScan.comparison_lift fuel pivot candidate common tail
          incomparableReversed keptReversed (.call (pivot, candidate) []) before middle done
      have prefixRun : SourceCurrentOriginalRowClusterScan.execute (used + 1)
          (.scan pivot (candidate :: tail) incomparableReversed keptReversed) before =
          .yielded
            (if common.entry.identity = candidate.entry.identity then
               .scan pivot tail incomparableReversed keptReversed
             else if common.entry.identity = pivot.entry.identity then
               .cluster (candidate :: (incomparableReversed.reverse ++ tail)) keptReversed
             else .scan pivot tail (candidate :: incomparableReversed) keptReversed) middle := by
        simpa only [SourceCurrentOriginalRowClusterScan.execute,
          SourceCurrentOriginalRowClusterScan.step] using resumed
      by_cases promoted : common.entry.identity ≠ candidate.entry.identity ∧
          common.entry.identity = pivot.entry.identity
      · rcases promoted with ⟨notDropped, promoted⟩
        refine ⟨used + 1, candidate :: (incomparableReversed.reverse ++ tail),
          keptReversed, middle, by omega, ?_, ?_, ?_, ?_, keptMembers, midGood,
          midContextual, midSemantic, extension, midStable, midIdle, tables, retained, midTrace⟩
        · simpa only [ite_eq_right notDropped, ite_eq_left promoted] using prefixRun
        · simp only [List.length_cons, List.length_append, List.length_reverse]
          omega
        · simp only [List.length_cons, List.length_append, List.length_reverse]
          omega
        · intro edge member
          rcases List.mem_cons.mp member with rfl | member
          · exact candidateMember
          · rcases List.mem_append.mp member with member | member
            · exact incomparableMembers edge (List.mem_reverse.mp member)
            · exact tailMembers edge member
      · let nextIncomparable := if common.entry.identity = candidate.entry.identity then
          incomparableReversed else candidate :: incomparableReversed
        have nextMembers : ∀ edge ∈ nextIncomparable,
            edge ∈ (nodeEdges parent).filter (fun row => decide (row.entry.key.symbol = symbol)) := by
          dsimp only [nextIncomparable]
          split
          · exact incomparableMembers
          · intro edge member
            rcases List.mem_cons.mp member with rfl | member
            · exact candidateMember
            · exact incomparableMembers edge member
        have nextLength : nextIncomparable.length ≤ incomparableReversed.length + 1 := by
          dsimp only [nextIncomparable]
          split
          · omega
          · simp only [List.length_cons]
            omega
        have resumedScan : SourceCurrentOriginalRowClusterScan.execute (used + 1)
            (.scan pivot (candidate :: tail) incomparableReversed keptReversed) before =
            .yielded (.scan pivot tail nextIncomparable keptReversed) middle := by
          by_cases dropped : common.entry.identity = candidate.entry.identity
          · simpa only [dropped, ↓reduceIte, nextIncomparable] using prefixRun
          · have notPromoted : common.entry.identity ≠ pivot.entry.identity :=
              fun equal => promoted ⟨dropped, equal⟩
            simpa only [dropped, notPromoted, ↓reduceIte, nextIncomparable] using prefixRun
        obtain ⟨more, next, newKept, after, _positive, scanned, shorter, total,
            nextMembers, newKeptMembers, afterGood, afterContextual, afterSemantic,
            laterExtension, afterStable, afterIdle, laterTables, laterReturned, afterTrace⟩ :=
          ih (incomparableReversed := nextIncomparable) (keptReversed := keptReversed)
            (before := middle) midStable midGood midContextual midSemantic
            (grows_trans growth extension.heap) (extends_trans history extension.history)
            midTrace midIdle pivotMember tailMembers nextMembers keptMembers
        refine ⟨used + 1 + more, next, newKept, after, by omega, ?_, ?_, ?_, nextMembers,
          newKeptMembers, afterGood, afterContextual, afterSemantic,
          extension.trans laterExtension, afterStable, afterIdle,
          extends_trans tables laterTables, retained.trans laterReturned, afterTrace⟩
        · rw [execute_yielded_add (used + 1) more _ _ _ _ resumedScan]
          exact scanned
        · simp only [List.length_cons]
          omega
        · simp only [List.length_cons]
          omega

/-- Complete one original symbol group and retain its current packet and domain history. -/
theorem cluster_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputModel : InputMeaning (view source (guardHolds formulas solver)))
    (inputRanked : RankedInput (view source (guardHolds formulas solver)) inputModel.valid)
    (parent : Value Symbol Guard)
    (original : OriginalInput source (inputOf parent))
    (available : Available source parent) (closed : parent.free = [])
    (symbol : Symbol)
    (initialDomains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (initialValid : Cache.Valid initialDomains)
    (before : Wrapper (bits + 2))
    (stable : Stable (view source (guardHolds formulas solver)) inputModel inputRanked
      (guardHolds formulas solver) before)
    (good : Good before.checked)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (guardHolds formulas solver)) inputModel inputRanked
      (guardHolds formulas solver) before.checked.native)
    (semantic : SemanticReady before.checked.native.machine.heap)
    (growth : Grows source before.checked.native.machine.heap)
    (history : Extends source.nodes.issued before.checked.native.machine.heap.nodes.issued)
    (allocations : SourceRecursiveIntersectionDomainAllocation.Trace
      (SourceRecursiveIntersectionSourceInventory.domains source)
      initialDomains before.checked.native.machine.domains)
    (idle : NativeIdle before.checked.native)
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits
      ⟨source.nodes.next, source.edges.next,
        initialDomains.next + (SourceRecursiveIntersectionSourceInventory.domains source).length, 0⟩) :
    let rows := (nodeEdges parent).filter (fun edge => decide (edge.entry.key.symbol = symbol))
    ∃ (fuel : Nat) (kept : List Edge) (after : Wrapper (bits + 2)),
      SourceCurrentOriginalRowClusterScan.execute fuel (.cluster rows []) before = .done kept after ∧
      (∀ edge ∈ kept, edge ∈ rows) ∧
      kept.length ≤ rows.length ∧
      Good after.checked ∧
      SourceCurrentAllocatedNativeContextCache.Contextual
        (view source (guardHolds formulas solver)) inputModel inputRanked
        (guardHolds formulas solver) after.checked.native ∧
      SemanticReady after.checked.native.machine.heap ∧
      Extension before.checked.native.machine after.checked.native.machine ∧
      Stable (view source (guardHolds formulas solver)) inputModel inputRanked
        (guardHolds formulas solver) after ∧
      NativeIdle after.checked.native ∧
      Extends before.memo.table after.memo.table ∧
      FlatMemoThunk.Returned before.memo after.memo ∧
      SourceRecursiveIntersectionDomainAllocation.Trace
        (SourceRecursiveIntersectionSourceInventory.domains source)
        initialDomains after.checked.native.machine.domains := by
  dsimp only
  let rows := (nodeEdges parent).filter (fun edge => decide (edge.entry.key.symbol = symbol))
  have complete : ∀ size (candidates keptReversed : List Edge) (current : Wrapper (bits + 2)),
      candidates.length = size →
      (∀ edge ∈ candidates, edge ∈ rows) → (∀ edge ∈ keptReversed, edge ∈ rows) →
      Stable (view source (guardHolds formulas solver)) inputModel inputRanked
        (guardHolds formulas solver) current → Good current.checked →
      SourceCurrentAllocatedNativeContextCache.Contextual
        (view source (guardHolds formulas solver)) inputModel inputRanked
        (guardHolds formulas solver) current.checked.native →
      SemanticReady current.checked.native.machine.heap →
      Grows source current.checked.native.machine.heap →
      Extends source.nodes.issued current.checked.native.machine.heap.nodes.issued →
      SourceRecursiveIntersectionDomainAllocation.Trace
        (SourceRecursiveIntersectionSourceInventory.domains source)
        initialDomains current.checked.native.machine.domains → NativeIdle current.checked.native →
      ∃ (fuel : Nat) (kept : List Edge) (after : Wrapper (bits + 2)),
        SourceCurrentOriginalRowClusterScan.execute fuel (.cluster candidates keptReversed) current =
          .done kept after ∧
        (∀ edge ∈ kept, edge ∈ rows) ∧ kept.length ≤ candidates.length + keptReversed.length ∧
        Good after.checked ∧
        SourceCurrentAllocatedNativeContextCache.Contextual
          (view source (guardHolds formulas solver)) inputModel inputRanked
          (guardHolds formulas solver) after.checked.native ∧
        SemanticReady after.checked.native.machine.heap ∧
        Extension current.checked.native.machine after.checked.native.machine ∧
        Stable (view source (guardHolds formulas solver)) inputModel inputRanked
          (guardHolds formulas solver) after ∧ NativeIdle after.checked.native ∧
        Extends current.memo.table after.memo.table ∧
        FlatMemoThunk.Returned current.memo after.memo ∧
        SourceRecursiveIntersectionDomainAllocation.Trace
          (SourceRecursiveIntersectionSourceInventory.domains source)
          initialDomains after.checked.native.machine.domains := by
    intro size
    induction size using Nat.strongRecOn with
    | ind size ih =>
        intro candidates keptReversed current sized members keptMembers currentStable currentGood
          currentContextual currentSemantic currentGrowth currentHistory currentTrace currentIdle
        cases candidates with
        | nil =>
            refine ⟨1, keptReversed.reverse, current, rfl, ?_, ?_, currentGood,
              currentContextual, currentSemantic, Extension.refl _, currentStable,
              currentIdle, extends_refl _, FlatMemoThunk.Returned.refl _, currentTrace⟩
            · simpa only [List.mem_reverse] using keptMembers
            · simp only [List.length_reverse, List.length_nil, Nat.zero_add]
              exact Nat.le_refl _
        | cons pivot tail =>
            obtain ⟨used, next, newKept, middle, _positive, scanned, shorter, total,
                nextMembers, newKeptMembers, midGood, midContextual, midSemantic,
                extension, midStable, midIdle, tables, retained, midTrace⟩ :=
              scan_boundary_complete bits source facts formulas solver inputModel inputRanked
                parent original available closed symbol initialDomains initialValid
                pivot tail [] keptReversed current currentStable currentGood currentContextual
                currentSemantic currentGrowth currentHistory currentTrace currentIdle room
                (members pivot List.mem_cons_self)
                (fun edge member => members edge (List.mem_cons_of_mem pivot member))
                (by simp only [List.not_mem_nil, false_implies, implies_true]) keptMembers
            have smaller : next.length < size := by
              simp only [List.length_cons, List.length_nil] at shorter sized
              omega
            obtain ⟨fuel, kept, after, done, finalMembers, finalLength, afterGood,
                afterContextual, afterSemantic, laterExtension, afterStable, afterIdle,
                laterTables, laterReturned, afterTrace⟩ :=
              ih next.length smaller next newKept middle rfl nextMembers newKeptMembers
                midStable midGood midContextual midSemantic (grows_trans currentGrowth extension.heap)
                (extends_trans currentHistory extension.history) midTrace midIdle
            have prefixRun : SourceCurrentOriginalRowClusterScan.execute (used + 1)
                (.cluster (pivot :: tail) keptReversed) current =
                .yielded (.cluster next newKept) middle := by
              simpa only [SourceCurrentOriginalRowClusterScan.execute,
                SourceCurrentOriginalRowClusterScan.step] using scanned
            refine ⟨used + 1 + fuel, kept, after, ?_, finalMembers, ?_, afterGood,
              afterContextual, afterSemantic, extension.trans laterExtension, afterStable,
              afterIdle, extends_trans tables laterTables, retained.trans laterReturned, afterTrace⟩
            · rw [execute_yielded_add (used + 1) fuel _ _ _ _ prefixRun]
              exact done
            · simp only [List.length_cons, List.length_nil] at total ⊢
              omega
  obtain ⟨fuel, kept, after, done, members, bound, packet⟩ :=
    complete rows.length rows [] before rfl (fun _ member => member)
      (by simp only [List.not_mem_nil, false_implies, implies_true])
      stable good contextual semantic growth history allocations idle
  exact ⟨fuel, kept, after, done, members, by simpa only [List.length_nil, Nat.add_zero] using bound, packet⟩

end MicroCFTA.SourceCurrentOriginalRowClusterCompletion
