import MicroCFTA.SourceCurrentOriginalRowClusterLanguage
import MicroCFTA.SourceCurrentPrependGrouping

namespace MicroCFTA.SourceCurrentOriginalRowGroupChain
open Cache Language IntersectSchedule InternedConstructorTemplates InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionInputView InternedProbeProvenance
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Wrapper" => SourceCurrentSameSymbolEdgeControl.State
local notation "Stable" => SourceCurrentSameSymbolEdgeStable.Stable
local notation "NativeIdle" => SourceRecursiveIntersectionNative.Idle
local notation "guardHolds" => (@SourceEqualityPCSGuard.holds FullSyntax.Formula FormulaExecutable.formulaDecidableEq)

/-- Read each reversed iterator bucket as the complete original symbol filter. -/
private theorem bucket_readback [DecidableEq Symbol]
    (parent : Value Symbol Guard) (entries : List (Symbol × List Edge))
    (iteration : SourceCurrentMergeGrouping.Iteration
      (SourceCurrentPrependGrouping.fromRows (fun edge : Edge => edge.entry.key.symbol)
        (nodeEdges parent)) entries)
    (entry : Symbol × List Edge) (included : entry ∈ entries) :
    entry.2.reverse = (nodeEdges parent).filter
      (fun edge => decide (edge.entry.key.symbol = entry.1)) := by
  have reversed := SourceCurrentPrependGrouping.iteration_reverse
    (SourceCurrentPrependGrouping.fromRows (fun edge : Edge => edge.entry.key.symbol)
      (nodeEdges parent)) entries iteration
  have member : (entry.1, entry.2.reverse) ∈
      entries.map (fun stored => (stored.1, stored.2.reverse)) :=
    List.mem_map.mpr ⟨entry, included, rfl⟩
  have found := (reversed.lookup entry.1 entry.2.reverse).mp member
  rw [SourceCurrentPrependGrouping.reverse_fromRows] at found
  exact ((SourceCurrentMergeGrouping.lookup_some
    (fun edge : Edge => edge.entry.key.symbol) (nodeEdges parent) entry.1 entry.2.reverse).mp found).2

/- The chain retains one fixed source and the full caller at each boundary.
   The literal modeled Mu row list is empty. No outer interpreter is added. -/

/-- Complete the supplied symbol buckets through one evolving caller and preserve their union. -/
theorem groups_complete
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
    (admitted : inputModel.valid (inputOf parent))
    (entries : List (Symbol × List Edge))
    (iteration : SourceCurrentMergeGrouping.Iteration
      (SourceCurrentPrependGrouping.fromRows (fun edge : Edge => edge.entry.key.symbol)
        (nodeEdges parent)) entries)
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
    ∃ (fuels : Fin entries.length → Nat) (kept : Fin entries.length → List Edge)
      (states : Fin (entries.length + 1) → Wrapper (bits + 2)),
      let after := states (Fin.last entries.length)
      let output := (List.ofFn kept).flatten
      states 0 = before ∧
      (∀ index : Fin entries.length,
        SourceCurrentOriginalRowClusterScan.execute (fuels index)
          (.cluster (entries.get index).2.reverse []) (states index.castSucc) =
          .done (kept index) (states index.succ) ∧
        (∀ edge ∈ kept index, edge ∈ (entries.get index).2.reverse) ∧
        (kept index).length ≤ (entries.get index).2.reverse.length) ∧
      (∀ index : Fin (entries.length + 1),
        Good (states index).checked ∧
        SourceCurrentAllocatedNativeContextCache.Contextual
          (view source (guardHolds formulas solver)) inputModel inputRanked
          (guardHolds formulas solver) (states index).checked.native ∧
        SemanticReady (states index).checked.native.machine.heap ∧
        Grows source (states index).checked.native.machine.heap ∧
        Extends source.nodes.issued (states index).checked.native.machine.heap.nodes.issued ∧
        Stable (view source (guardHolds formulas solver)) inputModel inputRanked
          (guardHolds formulas solver) (states index) ∧
        NativeIdle (states index).checked.native ∧
        SourceRecursiveIntersectionDomainAllocation.Trace
          (SourceRecursiveIntersectionSourceInventory.domains source)
          initialDomains (states index).checked.native.machine.domains) ∧
      Extension before.checked.native.machine after.checked.native.machine ∧
      Extends before.memo.table after.memo.table ∧
      FlatMemoThunk.Returned before.memo after.memo ∧
      (∀ edge ∈ output, edge ∈ nodeEdges parent) ∧
      output.length ≤ (nodeEdges parent).length ∧
      ∀ ambient : InternedGuardedLanguage.Env Symbol, ∀ term : Term Symbol,
        (∃ edge ∈ output, InternedGuardedLanguage.edgeMeaning
          (guardHolds formulas solver) ambient edge term) ↔
        ∃ edge ∈ nodeEdges parent, InternedGuardedLanguage.edgeMeaning
          (guardHolds formulas solver) ambient edge term := by
  have complete : ∀ (remaining : List (Symbol × List Edge)) (current : Wrapper (bits + 2)),
      (∀ entry ∈ remaining, entry ∈ entries) →
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
      ∃ (fuels : Fin remaining.length → Nat) (kept : Fin remaining.length → List Edge)
        (states : Fin (remaining.length + 1) → Wrapper (bits + 2)),
        let after := states (Fin.last remaining.length)
        let output := (List.ofFn kept).flatten
        let input := (remaining.map (fun entry => entry.2.reverse)).flatten
        states 0 = current ∧
        (∀ index : Fin remaining.length,
          SourceCurrentOriginalRowClusterScan.execute (fuels index)
            (.cluster (remaining.get index).2.reverse []) (states index.castSucc) =
            .done (kept index) (states index.succ) ∧
          (∀ edge ∈ kept index, edge ∈ (remaining.get index).2.reverse) ∧
          (kept index).length ≤ (remaining.get index).2.reverse.length) ∧
        (∀ index : Fin (remaining.length + 1),
          Good (states index).checked ∧
          SourceCurrentAllocatedNativeContextCache.Contextual
            (view source (guardHolds formulas solver)) inputModel inputRanked
            (guardHolds formulas solver) (states index).checked.native ∧
          SemanticReady (states index).checked.native.machine.heap ∧
          Grows source (states index).checked.native.machine.heap ∧
          Extends source.nodes.issued (states index).checked.native.machine.heap.nodes.issued ∧
          Stable (view source (guardHolds formulas solver)) inputModel inputRanked
            (guardHolds formulas solver) (states index) ∧
          NativeIdle (states index).checked.native ∧
          SourceRecursiveIntersectionDomainAllocation.Trace
            (SourceRecursiveIntersectionSourceInventory.domains source)
            initialDomains (states index).checked.native.machine.domains) ∧
        Extension current.checked.native.machine after.checked.native.machine ∧
        Extends current.memo.table after.memo.table ∧
        FlatMemoThunk.Returned current.memo after.memo ∧
        (∀ edge ∈ output, edge ∈ input) ∧ output.length ≤ input.length ∧
        ∀ ambient : InternedGuardedLanguage.Env Symbol, ∀ term : Term Symbol,
          (∃ edge ∈ output, InternedGuardedLanguage.edgeMeaning
            (guardHolds formulas solver) ambient edge term) ↔
          ∃ edge ∈ input, InternedGuardedLanguage.edgeMeaning
            (guardHolds formulas solver) ambient edge term := by
    intro remaining
    induction remaining with
    | nil =>
        intro current _members currentStable currentGood currentContextual currentSemantic
          currentGrowth currentHistory currentTrace currentIdle
        refine ⟨(fun index => Fin.elim0 index), (fun index => Fin.elim0 index),
          (fun _ => current), rfl, ?_, ?_, Extension.refl _, extends_refl _,
          FlatMemoThunk.Returned.refl _, ?_, ?_, ?_⟩
        · intro index
          exact Fin.elim0 index
        · intro _index
          exact ⟨currentGood, currentContextual, currentSemantic, currentGrowth,
            currentHistory, currentStable, currentIdle, currentTrace⟩
        · simp
        · simp
        · intro _ambient _term
          simp
    | cons entry rest ih =>
        intro current members currentStable currentGood currentContextual currentSemantic
          currentGrowth currentHistory currentTrace currentIdle
        have contents := bucket_readback parent entries iteration entry (members entry List.mem_cons_self)
        obtain ⟨headFuel, headKept, middle, headDone, headMembers, headLength, midGood,
            midContextual, midSemantic, extension, midStable, midIdle, tables, retained,
            midTrace, headMeaning⟩ :=
          SourceCurrentOriginalRowClusterLanguage.cluster_complete bits source facts formulas solver
            inputModel inputRanked parent original available closed admitted entry.1
            initialDomains initialValid current currentStable currentGood currentContextual
            currentSemantic currentGrowth currentHistory currentTrace currentIdle room
        rw [← contents] at headDone headMembers headLength headMeaning
        obtain ⟨tailFuels, tailKept, tailStates, tailStart, tailSteps, tailPackets,
            laterExtension, laterTables, laterReturned, tailMembers, tailLength, tailMeaning⟩ :=
          ih middle (fun stored member => members stored (List.mem_cons_of_mem entry member))
            midStable midGood midContextual midSemantic
            (grows_trans currentGrowth extension.heap)
            (extends_trans currentHistory extension.history) midTrace midIdle
        let fuels : Fin (rest.length + 1) → Nat := Fin.cases headFuel tailFuels
        let kept : Fin (rest.length + 1) → List Edge := Fin.cases headKept tailKept
        let states : Fin (rest.length + 1 + 1) → Wrapper (bits + 2) :=
          Fin.cases current tailStates
        have outputShape : (List.ofFn kept).flatten =
            headKept ++ (List.ofFn tailKept).flatten := by
          simp only [kept, List.ofFn_succ, Fin.cases_zero, Fin.cases_succ, List.flatten_cons]
        refine ⟨fuels, kept, states, rfl, ?_, ?_, extension.trans laterExtension,
          extends_trans tables laterTables, retained.trans laterReturned, ?_, ?_, ?_⟩
        · intro index
          refine Fin.cases ?_ (fun next => ?_) index
          · change SourceCurrentOriginalRowClusterScan.execute headFuel
                (.cluster entry.2.reverse []) current = .done headKept (tailStates 0) ∧
              (∀ edge ∈ headKept, edge ∈ entry.2.reverse) ∧
              headKept.length ≤ entry.2.reverse.length
            rw [tailStart]
            exact ⟨headDone, headMembers, headLength⟩
          · change SourceCurrentOriginalRowClusterScan.execute (tailFuels next)
                (.cluster (rest.get next).2.reverse []) (tailStates next.castSucc) =
                .done (tailKept next) (tailStates next.succ) ∧
              (∀ edge ∈ tailKept next, edge ∈ (rest.get next).2.reverse) ∧
              (tailKept next).length ≤ (rest.get next).2.reverse.length
            exact tailSteps next
        · intro index
          refine Fin.cases ?_ (fun next => ?_) index
          · exact ⟨currentGood, currentContextual, currentSemantic, currentGrowth,
              currentHistory, currentStable, currentIdle, currentTrace⟩
          · exact tailPackets next
        · rw [outputShape]
          intro edge member
          rcases List.mem_append.mp member with inHead | inTail
          · exact List.mem_append.mpr (Or.inl (headMembers edge inHead))
          · exact List.mem_append.mpr (Or.inr (tailMembers edge inTail))
        · rw [outputShape]
          simpa only [List.map_cons, List.flatten_cons, List.length_append] using
            Nat.add_le_add headLength tailLength
        · intro ambient term
          rw [outputShape]
          simpa only [List.map_cons, List.flatten_cons, List.mem_append, or_and_right,
            exists_or] using or_congr (headMeaning ambient term) (tailMeaning ambient term)
  obtain ⟨fuels, kept, states, start, steps, packets, extension, tables, retained,
      members, lengthBound, meaning⟩ :=
    complete entries before (fun _ member => member) stable good contextual semantic
      growth history allocations idle
  have coverage : (entries.map (fun entry => entry.2.reverse)).flatten.Perm (nodeEdges parent) := by
    have grouped : (entries.map (fun entry => entry.2.reverse)).flatten.Perm
        (Sized.groups (fun edge : Edge => edge.entry.key.symbol) (nodeEdges parent)).flatten := by
      simpa only [List.map_map, Function.comp_def] using
        (SourceCurrentPrependGrouping.iteration_permutation
          (fun edge : Edge => edge.entry.key.symbol) (nodeEdges parent) entries iteration).flatten
    exact grouped.trans (Sized.groups_perm (fun edge : Edge => edge.entry.key.symbol) (nodeEdges parent))
  refine ⟨fuels, kept, states, start, steps, packets, extension, tables, retained, ?_, ?_, ?_⟩
  · intro edge member
    exact coverage.mem_iff.mp (members edge member)
  · simpa only [coverage.length_eq] using lengthBound
  · intro ambient term
    refine (meaning ambient term).trans ?_
    constructor
    · rintro ⟨edge, member, accepted⟩
      exact ⟨edge, coverage.mem_iff.mp member, accepted⟩
    · rintro ⟨edge, member, accepted⟩
      exact ⟨edge, coverage.mem_iff.mpr member, accepted⟩

end MicroCFTA.SourceCurrentOriginalRowGroupChain
