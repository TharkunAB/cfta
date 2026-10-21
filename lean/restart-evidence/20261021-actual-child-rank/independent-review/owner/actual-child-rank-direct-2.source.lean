import MicroCFTA.SourceCurrentResourceOwnerInheritedDispatch
import MicroCFTA.SourceCurrentResourceParentPositiveBack
import MicroCFTA.SourceCurrentPositiveQuotientCount

namespace MicroCFTA.SourceCurrentActualChildRank
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Reached)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
local notation "prefixState" => SourceCurrentAllocatedPartialGraph.prefixState
local notation "descend" => SourceCurrentAllocatedPartialGraph.descend
variable {bits : Nat}

private theorem reservation [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {budget : Nat} {request : EdgeRequest}
    {before : Caller (bits + 2)} {memos : Memos} {profile : Profile} {alphabet : List Guard}
    (initial : Context formulas solver inventory before memos) (fits : Fits profile before.checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet)
      before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value)
    (uniform : SourceCurrentParentAlphabetReservation.UniformReserved bits budget alphabet profile) :
    SourceCurrentEdgeCallNumeric.Reserved bits budget request before profile := by
  generalize started : beginEdge request before = observation
  obtain ⟨handle,action,running⟩ := observation
  cases action with
  | evaluate captured =>
      obtain ⟨runningContext,owner,_key,_cell⟩ :=
        SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial inherited resident started
      have checked := (beginEdge_components request before).1
      rw [started] at checked
      dsimp only at checked
      have bounded : Fits profile running.checked := by simpa only [checked] using fits
      have carrier : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet)
          running.checked.native.machine.heap := by simpa only [checked] using known
      have room := SourceCurrentParentAlphabetReservation.resident_reserved formulas solver inventory budget alphabet captured
        running memos runningContext profile bounded carrier owner.inherited owner.input uniform
      simpa only [SourceCurrentEdgeCallNumeric.Reserved,started] using room
  | ready | busy | absent => simp only [SourceCurrentEdgeCallNumeric.Reserved,started]

private theorem prefix_data (original : Guard) (identity : Nat)
    (inherited : List SourceEqualityClassOrder.Record) (before : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (ready : SourceEqualityConstraintAllocation.Ready before.constraints (.live identity inherited))
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (combinedIdentity : Nat) (outputs : List SourceEqualityClassOrder.Record)
    (actual : (SourceCurrentAllocatedInheritedPrefix.run original (.live identity inherited) before).1 =
      .ok (some (.live combinedIdentity outputs))) :
    let after := (SourceCurrentAllocatedInheritedPrefix.run original (.live identity inherited) before).2
    SourceEqualityConstraintAllocation.Ready after.constraints (.live combinedIdentity outputs) ∧
      EqualityNormalize.congruenceStep (outputs.map SourceEqualityClassOrder.Record.paths) =
        some (outputs.map SourceEqualityClassOrder.Record.paths) ∧
      EqualityNormalize.Covers (inherited.map SourceEqualityClassOrder.Record.paths)
        (outputs.map SourceEqualityClassOrder.Record.paths) := by
  obtain ⟨own,loaded,accessorValid,ownReady,_ownClasses,_ownRead,accessorGrowth⟩ :=
    SourceCurrentConjunctionEquality.accessor_correct original before valid field
  obtain ⟨result,computed,_finalValid,resultReady,_growth,fixed,covers⟩ :=
    SourceCurrentOuterOriginDependencies.combine_covers (.live identity inherited) own
      (SourceCurrentConjunctionEquality.accessor original before).2 accessorValid
      (ready.grows accessorGrowth.constraint_growth) ownReady
  have equation : SourceCurrentAllocatedInheritedPrefix.run original (.live identity inherited) before =
      (.ok (some result), (SourceEqualityConstraintMemoAllocation.combine (.live identity inherited) own
        (SourceCurrentConjunctionEquality.accessor original before).2).2) := by
    rw [SourceCurrentAllocatedInheritedPrefix.run_combine original identity inherited before own loaded]
    simp only [computed,Except.map]
  have same := Option.some.inj (Except.ok.inj ((congrArg Prod.fst equation).symm.trans actual))
  subst result
  refine ⟨?_,(SourceCurrentEqualityNormalizationFixed.invariants _ (fixed outputs rfl)).2.2.2,?_⟩
  · rw [congrArg Prod.snd equation]; exact resultReady
  · intro paths member
    exact covers outputs rfl paths (List.mem_append.mpr (.inl member))

private theorem shape_mass {entry depth free} {rows : List Edge} {row returned : Edge} {child : Node}
    (member : row ∈ rows) (shape : SourceCurrentAllocatedPartialReturnedDomain.Shape row returned)
    (inside : child ∈ returned.children) :
    InternedValueMass.value child < InternedValueMass.value (.node entry rows depth free : Node) := by
  rcases shape with same | erased | sentinel
  · exact InternedValueMass.node_child_lt entry rows depth free row member child (same ▸ inside)
  · rw [erased] at inside
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp inside
    have small := InternedValueMass.edge_mem_lt row rows member
    have positive := InternedValueMass.edge_pos row
    simp only [InternedValueMass.value]; omega
  · rw [sentinel] at inside
    have same : child = .empty := List.mem_singleton.mp inside
    subst child
    have small := InternedValueMass.edge_mem_lt row rows member
    have positive := InternedValueMass.edge_pos row
    simp only [InternedValueMass.value]; omega

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

theorem dispatch
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s r e p h m c n budget fuel slot : Nat}
    {inherited : EqValue}
    {first : Phase (bits + 2)} {inventory : Inventory} {memos : Memos}
    (seed : List Guard × Profile)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      (caller first).checked.native.machine.heap)
    (inputs : SourceCurrentOuterPrefixInvariants.Inputs first)
    (room : Room bits (SourceCurrentOuterInitialPrefix.forecast budget first seed).2)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal (caller first).checked.native.machine.heap)
    (supported : SourceCurrentNativeRequestPositivePositions.Support
      (caller first).checked.native.machine.heap (caller first).checked.native)
    (causal : SourceCurrentNativeMuPublication.History empty (caller first).checked.native.machine.heap)
    (merged : SourceCurrentConstrainedCapMemoMerge.Stored
      (fun guard : Guard => SourceMemoGate.plain guard = true) (caller first).merge)
    (positiveMemo : SourceCurrentMergePositivePosition.Support (caller first).merge)
    (origins : SourceCurrentResourceParentWriters.Origins formulas solver (caller first))
    {ownerEntry ownerDepth ownerFree} {ownerRows : List Edge}
    {original parented : Edge} {rest : List Edge}
    {before afterParent start : Caller (bits + 2)} {earlier : List Node}
    {combined : EqValue} {value : Node}
    (past : Reached g s r e p h m c n budget first
      (.rows (fuel + slot + 2) inherited (original :: rest) before))
    (member : original ∈ ownerRows)
    (parent : edgeCall (fuel + slot + 1) g s r e p h m c n budget
      ⟨inherited, original⟩ before = .done parented afterParent)
    (combinedAt : (SourceCurrentAllocatedInheritedPrefix.run parented.entry.key.constraint
      inherited afterParent.checked.operations).1 = .ok (some combined))
    (live : combined ≠ .contradiction)
    (earlierCalls : walk (fuel + slot + 1) g s r e p h m c n budget combined 0
      (parented.children.take slot) (prefixState afterParent parented inherited) =
        .done earlier start)
    (selected : parented.children[slot]? = some value) :
    let child := descend start combined slot
    Reached g s r e p h m c n budget first (.node fuel ⟨child.1,value⟩ child.2) ∧
      Prod.Lex Nat.lt Nat.lt
        (SourceCurrentPositiveQuotientCount.count (child.1.payload.getD []) value,
          InternedValueMass.value value)
        (SourceCurrentPositiveQuotientCount.count (inherited.payload.getD [])
            (.node ownerEntry ownerRows ownerDepth ownerFree),
          InternedValueMass.value (.node ownerEntry ownerRows ownerDepth ownerFree : Node))

 := by
  obtain ⟨rowInventory,rowMemos,rowSeed,_rowTrace,rowPost,rowFrame,rowFits,rowKnown,
      rowInputs,_rowBelow,_rowAlphabet,rowRoom,_rowBounds,_rowCarrier,_rowNeed,
      rowSupport,⟨rowCausal⟩,rowMerged,rowPositive,rowNormal⟩ :=
    SourceCurrentOuterPrefixNativeStores.reached formulas solver seed past initial frame fits known inputs room
      normal supported causal merged positiveMemo
  have rowOrigins := SourceCurrentOuterResourceWriters.reached formulas solver seed past
    initial frame fits known inputs room normal supported causal merged positiveMemo origins
  have headRoom := rowRoom
  change Room bits (SourceCurrentOuterInitialSchedule.rows ((fuel + slot + 1) + 1) budget rowSeed).2 at headRoom
  rw [SourceCurrentOuterInitialSchedule.rows] at headRoom
  let parentSeed := SourceCurrentOuterInitialSchedule.parent budget rowSeed
  have parentRoom : Room bits parentSeed.2 := headRoom.mono
    ((SourceCurrentOuterInitialSchedule.descendants_ge (fuel + slot + 1) budget parentSeed).1.trans
      (SourceCurrentOuterInitialSchedule.rows_ge (fuel + slot + 1) budget
        (SourceCurrentOuterInitialSchedule.descendants (fuel + slot + 1) budget parentSeed)).1)
  have uniform := SourceCurrentOuterInitialSchedule.parent_reserved bits budget rowSeed parentRoom
  have reserved := reservation formulas solver (request := ⟨inherited,original⟩)
    rowPost.context rowFits rowKnown rowInputs.1 (rowInputs.2 _ List.mem_cons_self) uniform
  have written := (SourceCurrentResourceParentWriters.edge_call formulas solver rowInventory rowSeed.2 rowMemos
    parent rowPost.context rowFrame rowFits rowInputs.1 (rowInputs.2 _ List.mem_cons_self) reserved
    rowOrigins rowNormal rowSupport rowCausal rowMerged rowPositive).2
  have rowStep : Reached g s r e p h m c n budget
      (.rows (fuel + slot + 2) inherited (original :: rest) before)
      (.descendants (fuel + slot + 1) inherited parented afterParent) :=
    .snoc (.refl _) (.rows_edge parent)
  have descReached := past.trans rowStep
  have walkLocal := (rowStep.snoc (SourceCurrentOuterExecutionAncestry.Step.descendants_children combinedAt)).snoc
    (SourceCurrentOuterExecutionAncestry.Step.children_walk live)
  have walkReached := past.trans walkLocal
  have selectedPrefix := SourceCurrentOuterUntouchedProgress.walk_prefix earlierCalls selected
  have dispatchLocal : Reached g s r e p h m c n budget
      (.rows (fuel + slot + 2) inherited (original :: rest) before)
      (.node fuel ⟨(descend start combined slot).1,value⟩ (descend start combined slot).2) := by
    simpa only [Nat.zero_add] using walkLocal.trans selectedPrefix
  have dispatchReached := past.trans dispatchLocal
  obtain ⟨descInventory,descMemos,_descSeed,_descTrace,descPost,_descFrame,_descFits,_descKnown,
      descInputs,_descBelow,_descAlphabet,_descRoom,_descBounds,_descCarrier,_descNeed,
      _descSupport,_descHistory,_descMerged,_descPositive,_descNormal⟩ :=
    SourceCurrentOuterPrefixNativeStores.reached formulas solver seed descReached initial frame fits known inputs room
      normal supported causal merged positiveMemo
  have field := descPost.context.ready.good.fields parented.entry.key parented descInputs.2
  obtain ⟨walkInventory,walkMemos,walkSeed,_walkTrace,walkPost,walkFrame,walkFits,walkKnown,
      walkInputs,_walkBelow,_walkAlphabet,walkRoom,_walkBounds,_walkCarrier,_walkNeed,
      _walkSupport,_walkHistory,_walkMerged,_walkPositive,_walkNormal⟩ :=
    SourceCurrentOuterPrefixNativeStores.reached formulas solver seed walkReached initial frame fits known inputs room
      normal supported causal merged positiveMemo
  obtain ⟨startInventory,startMemos,_walkGraph,_walkReads,startPost,_startFrame,_startFits,
      _startKnown,_startValues,_startLaw⟩ :=
    SourceCurrentOuterInitialActual.walk formulas solver (fuel + slot + 1)
      (combined := combined) (index := 0) (values := parented.children.take slot)
      (before := prefixState afterParent parented inherited) (after := start)
      walkSeed walkPost.context walkFrame walkFits walkKnown walkInputs.1
      (fun child member => walkInputs.2 child (List.mem_of_mem_take member)) walkRoom earlierCalls
  refine ⟨dispatchReached,?_⟩
  cases inherited with
  | contradiction =>
      rw [SourceCurrentAllocatedInheritedPrefix.run_contradiction] at combinedAt
      have same := Option.some.inj (Except.ok.inj combinedAt)
      exact False.elim (live same.symm)
  | live inheritedIdentity inheritedRecords =>
      cases combined with
      | contradiction => exact False.elim (live rfl)
      | live combinedIdentity classes =>
          obtain ⟨combinedReady,fixed,covered⟩ := prefix_data parented.entry.key.constraint
            inheritedIdentity inheritedRecords afterParent.checked.operations
            descPost.context.ready.good.operations descInputs.1 field combinedIdentity classes combinedAt
          obtain ⟨shape,back⟩ := SourceCurrentResourceParentPositiveBack.children formulas solver written
            afterParent.checked.operations descPost.context.ready.good.operations descInputs.1 field
            combinedIdentity classes combinedAt
          have counted := SourceCurrentPositiveQuotientCount.child_count classes inheritedRecords
            (fun record member => (combinedReady.2 classes rfl record member).1) fixed covered slot value
            (entry := ownerEntry) (depth := ownerDepth) (free := ownerFree) original member
            (back slot value selected)
          have currentReady := combinedReady.grows startPost.effects.grows.constraint_growth
          have actualDescent := SourceEqualityConstraintMemoAllocation.descend_correct
            (.live combinedIdentity classes) slot start.checked.operations
            startPost.context.ready.good.operations currentReady
          have records : SourceEqualityDescend.descend (some classes) slot =
              some (SourceEqualityDescend.records slot classes) := by cases classes <;> rfl
          have payload : (descend start (.live combinedIdentity classes) slot).1.payload =
              some (SourceEqualityDescend.records slot classes) := actualDescent.2.2.1.trans records
          rw [payload]
          cases plain : SourceMemoGate.plain original.entry.key.constraint with
          | false => exact Prod.Lex.left _ _ (counted.2 plain)
          | true =>
              have ownEmpty : SourceCompactGuards.sourceEqualities original.entry.key.constraint = some [] :=
                of_decide_eq_true (Bool.and_eq_true_iff.mp plain).1
              have smaller := shape_mass member (shape ownEmpty) (List.mem_of_getElem? selected)
              rcases Nat.lt_or_eq_of_le counted.1 with strict | equal
              · exact Prod.Lex.left _ _ strict
              · rw [equal]; exact Prod.Lex.right _ smaller

end MicroCFTA.SourceCurrentActualChildRank
