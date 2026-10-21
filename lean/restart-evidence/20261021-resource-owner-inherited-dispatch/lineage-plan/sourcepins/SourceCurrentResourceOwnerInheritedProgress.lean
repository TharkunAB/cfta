import MicroCFTA.SourceCurrentResourceOwnerProgress
import MicroCFTA.SourceCurrentPositiveInheritedChildSeparation

/-!
# Resource-backed copied-owner separation for every inherited value

One actual Parent writer supplies the completed class ancestry. The same
current combination covers its inherited and selected own classes. Exact
physical descent then separates the child from that inherited owner key.
This theorem concerns one immediate copied child of the same literal row.
-/
namespace MicroCFTA.SourceCurrentResourceOwnerInheritedProgress
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState (EdgeRequest NodeRequest)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Valid" => SourceEqualityConstraintMemoAllocation.Valid
local notation "Grows" => SourceEqualityConstraintMemoAllocation.Grows
private theorem rel_covers {classes others : EqualityNormalize.Constraints}
    (covered : EqualityNormalize.Covers classes others) {left right}
    (related : SourceCurrentNormalizedChildSeparation.Rel classes left right) :
    SourceCurrentNormalizedChildSeparation.Rel others left right := by
  induction related with
  | refl path => exact .refl path
  | member paths selected left right first second suffix =>
      obtain ⟨larger, included, preserves⟩ := covered paths selected
      exact .member larger included left right (preserves left first) (preserves right second) suffix
  | trans _ _ first second => exact .trans first second

private theorem prefix_data (original : Guard) (identity : Nat)
    (inherited : List SourceEqualityClassOrder.Record) (before : Operations) (valid : Valid before)
    (ready : EqReady before.constraints (.live identity inherited))
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (combinedIdentity : Nat) (outputs : List SourceEqualityClassOrder.Record)
    (actual : (SourceCurrentAllocatedInheritedPrefix.run original (.live identity inherited) before).1 =
      .ok (some (.live combinedIdentity outputs)))
    (selected : EqualityNormalize.Constraints)
    (ownSelected : ∀ paths ∈ selected, paths ∈ (SourceCompactGuards.sourceEqualities original).getD []) :
    let after := (SourceCurrentAllocatedInheritedPrefix.run original (.live identity inherited) before).2
    EqReady after.constraints (.live combinedIdentity outputs) ∧ Grows before after ∧
      EqualityNormalize.congruenceStep (outputs.map SourceEqualityClassOrder.Record.paths) =
        some (outputs.map SourceEqualityClassOrder.Record.paths) ∧
      EqualityNormalize.Covers (inherited.map SourceEqualityClassOrder.Record.paths)
        (outputs.map SourceEqualityClassOrder.Record.paths) ∧
      EqualityNormalize.Covers selected (outputs.map SourceEqualityClassOrder.Record.paths) := by
  obtain ⟨own, loaded, accessorValid, ownReady, ownClasses, _ownRead, accessorGrowth⟩ :=
    SourceCurrentConjunctionEquality.accessor_correct original before valid field
  obtain ⟨result, computed, _finalValid, resultReady, growth, fixed, covers⟩ :=
    SourceCurrentOuterOriginDependencies.combine_covers (.live identity inherited) own
      (SourceCurrentConjunctionEquality.accessor original before).2 accessorValid
      (ready.grows accessorGrowth.constraint_growth) ownReady
  have equation : SourceCurrentAllocatedInheritedPrefix.run original (.live identity inherited) before =
      (.ok (some result), (SourceEqualityConstraintMemoAllocation.combine (.live identity inherited) own
        (SourceCurrentConjunctionEquality.accessor original before).2).2) := by
    rw [SourceCurrentAllocatedInheritedPrefix.run_combine original identity inherited before own loaded]
    simp only [computed, Except.map]
  have same := Option.some.inj (Except.ok.inj ((congrArg Prod.fst equation).symm.trans actual))
  subst result
  refine ⟨?_, ?_, (SourceCurrentEqualityNormalizationFixed.invariants _ (fixed outputs rfl)).2.2.2, ?_, ?_⟩
  · rw [congrArg Prod.snd equation]
    exact resultReady
  · rw [congrArg Prod.snd equation]
    exact SourceCurrentConjunctionEquality.grows_trans accessorGrowth growth
  · intro paths member
    exact covers outputs rfl paths (List.mem_append.mpr (.inl member))
  · intro paths member
    apply covers outputs rfl paths
    apply List.mem_append.mpr
    apply Or.inr
    rw [ownClasses]
    exact ownSelected paths member

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {bits : Nat}

theorem key_ne_inherited
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {request : EdgeRequest} {returned : Edge}
    (written : SourceCurrentResourceParentWriters.Written (bits := bits) formulas solver request returned)
    {ownerEntry ownerDepth ownerFree} {ownerRows : List Edge} {index : Nat}
    (member : request.value ∈ ownerRows)
    (found : returned.children[index]? = some (.node ownerEntry ownerRows ownerDepth ownerFree))
    (prefixBefore : Operations) (valid : Valid prefixBefore)
    (ready : EqReady prefixBefore.constraints request.inherited)
    (field : SourceCurrentConjunctionEquality.FieldAvailable prefixBefore returned.entry.key.constraint)
    (combined : EqValue)
    (prefixActual : (SourceCurrentAllocatedInheritedPrefix.run returned.entry.key.constraint
      request.inherited prefixBefore).1 = .ok (some combined))
    (live : combined ≠ .contradiction)
    (later : Operations) (laterValid : Valid later)
    (laterGrowth : Grows (SourceCurrentAllocatedInheritedPrefix.run returned.entry.key.constraint
      request.inherited prefixBefore).2 later)
    :
    let child := SourceEqualityConstraintMemoAllocation.descend combined index later
    returned.entry.key.constraint = request.value.entry.key.constraint ∧
      SourceMemoGate.plain request.value.entry.key.constraint = false ∧
      child.1.payload ≠ request.inherited.payload ∧
      (NodeRequest.mk child.1 (.node ownerEntry ownerRows ownerDepth ownerFree)).key ≠
        (NodeRequest.mk request.inherited (.node ownerEntry ownerRows ownerDepth ownerFree)).key := by
  obtain ⟨g,s,r,e,p,h,m,c,n,budget,writerBefore,writerAfter,savedFourth,savedMerge,
      globals,inventory,profile,observed,context,frame,fits,inheritedReady,resident,
      liveInputs,reserved,normal,supported,⟨causal⟩,merged,positiveMemo⟩ := written
  have nativeGood := SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked context.ready.good) context.ready.semantic context.ready.costs
  obtain ⟨loaded,middle,records,kept,scanned,scanFourth,preparedValues,preparedHeap,
      noncontradictory,loadedAt,_reduced,_built,_accepted,precheck,scanCall,nonempty,
      requiredCall,passCall,_sameFourth,primary⟩ :=
    SourceCurrentActualOwnerSelection.selected observed nativeGood context.stored liveInputs member found
  obtain ⟨fieldAt,_inherited,_available⟩ := liveInputs noncontradictory
  have parentLive : SourceCurrentParentNumeric.LiveInputs request.value.entry.key.constraint loaded
      request.inherited request.value.children writerBefore :=
    fun _ => ⟨fieldAt.1,loadedAt,inheritedReady,_available⟩
  have parentReserved : SourceCurrentParentForecast.Reserved bits budget request.value.children.length
      request.value.entry.key.constraint loaded request.inherited writerBefore.checked profile := by
    simpa only [SourceCurrentParentForecast.residentReserved,noncontradictory,
      Bool.false_eq_true,ite_false,loadedAt] using reserved
  obtain ⟨next,final,own,preparedInventory,scanMemos,preparedMemos,numeric,trace,retained,
      pass,_assembled,precheckReceipt,_scanReads,_requiredReads,passReads,requiredReceipt,
      preparedValid,scanReady,scanEffects,_extension,scanValues,scanCurrent,scanSupport,
      ⟨scanHistory⟩,scanNormal⟩ :=
    SourceCurrentActualParentSelectedCertificates.selected_certificates formulas solver inventory budget
      request.value.entry.key.symbol request.value.entry.key.constraint loaded request.inherited
      request.value.children writerBefore globals context frame profile fits parentLive parentReserved observed
      noncontradictory precheck scanCall requiredCall passCall normal supported causal
  have readback : SourceEqualityConjoinAllocation.readback loaded = request.value.entry.key.constraint :=
    (SourceEqualityConstraintFieldLookup.load_ready request.value.entry.key.constraint
      writerBefore.checked.operations.constraints context.ready.good.operations.constraints
      fieldAt.1 loaded loadedAt).2
  have returnedGuard : returned.entry.key.constraint = request.value.entry.key.constraint := by
    rcases numeric.semantic.construction with rejected | ⟨children,constructorBefore,_length,constructed⟩
    · have inside := List.mem_of_getElem? found
      rw [rejected.children] at inside
      cases List.mem_singleton.mp inside
    · cases keep : SourceEqualityMkEdgeAllocation.accepted
          (SourceEqualityConjoinAllocation.readback loaded) children.length with
      | false =>
          have emptyChildren : returned.children = [.empty] := by
            simpa only [keep,Bool.false_eq_true,ite_false] using constructed.children
          have inside := List.mem_of_getElem? found
          rw [emptyChildren] at inside
          cases List.mem_singleton.mp inside
      | true =>
          have acceptedGuard : returned.entry.key.constraint = SourceEqualityConjoinAllocation.readback loaded := by
            simpa only [keep,ite_true] using constructed.guard
          exact acceptedGuard.trans readback
  have physical : SourceCurrentMemoMergeEffects.Stored scanned.native.machine.heap writerBefore.merge :=
    context.stored.grows scanEffects.keeps
  have currentField : SourceCurrentConjunctionEquality.FieldAvailable prefixBefore request.value.entry.key.constraint := by
    simpa only [returnedGuard] using field
  have currentPrefix : (SourceCurrentAllocatedInheritedPrefix.run request.value.entry.key.constraint
      request.inherited prefixBefore).1 = .ok (some combined) := by
    simpa only [returnedGuard] using prefixActual
  have currentGrowth : Grows (SourceCurrentAllocatedInheritedPrefix.run request.value.entry.key.constraint
      request.inherited prefixBefore).2 later := by
    simpa only [returnedGuard] using laterGrowth
  obtain ⟨_proper, raw, _rawRead, sourceClasses, order, recordFields⟩ := precheckReceipt.classes records rfl
  have retainedFields := retained.fields
  have nonplain : SourceMemoGate.plain request.value.entry.key.constraint = false := by
    apply Bool.eq_false_iff.mpr
    intro plain
    have ownEmpty : SourceCompactGuards.sourceEqualities request.value.entry.key.constraint = some [] := by
      simpa only [SourceMemoGate.plain, Bool.and_eq_true, decide_eq_true_eq] using (Bool.and_eq_true_iff.mp plain).1
    have rawEmpty : raw = [] := List.map_eq_nil_iff.mp (Option.some.inj (sourceClasses.symm.trans ownEmpty))
    have recordsEmpty : records = [] := by rw [order, rawEmpty]; rfl
    exact nonempty (List.sublist_nil.mp (recordsEmpty ▸ retainedFields.1))
  have ownSelected : ∀ paths ∈ kept.map SourceEqualityClassOrder.Record.paths,
      paths ∈ (SourceCompactGuards.sourceEqualities request.value.entry.key.constraint).getD [] := by
    intro paths chosen
    obtain ⟨record, member, rfl⟩ := List.mem_map.mp chosen
    have rawMember : record ∈ raw := (SourceEqualityClassOrder.ordered_perm raw).mem_iff.mp
      (by simpa only [order] using retainedFields.1.subset member)
    rw [sourceClasses]
    exact List.mem_map.mpr ⟨record, rawMember, rfl⟩
  have coherent : ∀ record ∈ kept, SourceEqualityClassOrder.Coherent record :=
    fun record member => (recordFields record (retainedFields.1.subset member)).1
  have active : ∀ record ∈ kept, EqualityNormalize.Nontrivial record.paths :=
    fun record member => (recordFields record (retainedFields.1.subset member)).2.2
  have gates : ∀ paths ∈ kept.map SourceEqualityClassOrder.Record.paths,
      EndpointStatefulGateTrace.ClassTrace SourceMemoGate.unconstrained
        (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) request.value.children paths
        scanned.native.machine.heap false scanned.native.machine.heap := by
    intro paths selected
    obtain ⟨record, member, rfl⟩ := List.mem_map.mp selected
    exact primary record member
  obtain ⟨_next, _receipt, _currentAfter, _mergedAfter, _corridors,
      _supportedAfter, _causalAfter, _positiveAfter, back⟩ :=
    SourceCurrentRequiredPositiveChronology.pass formulas solver preparedInventory requiredReceipt
      scanReady.semantic scanNormal scanReady.costs scanValues gates scanCurrent scanSupport scanHistory
      kept rfl coherent active passReads physical context.covered preparedValid merged positiveMemo
  cases combined with
  | contradiction => exact False.elim (live rfl)
  | live combinedIdentity outputs =>
      cases inheritedShape : request.inherited with
      | contradiction =>
          rw [inheritedShape, SourceCurrentAllocatedInheritedPrefix.run_contradiction] at currentPrefix
          cases currentPrefix
      | live inheritedIdentity inheritedRecords =>
          have inputReady := ready
          rw [inheritedShape] at inputReady
          have computed := currentPrefix
          rw [inheritedShape] at computed
          obtain ⟨combinedReady, prefixGrowth, fixed, inheritedCovered, keptCovered⟩ :=
            prefix_data request.value.entry.key.constraint inheritedIdentity inheritedRecords prefixBefore valid
              inputReady currentField combinedIdentity outputs computed _ ownSelected
          have combinedCoherent : ∀ record ∈ outputs, SourceEqualityClassOrder.Coherent record :=
            fun record member => (combinedReady.2 outputs rfl record member).1
          have separated := SourceCurrentPositiveInheritedChildSeparation.same_child_payload_ne outputs
            inheritedRecords combinedCoherent fixed inheritedCovered index request.value member nonplain
            (fun q positive => by
              obtain ⟨j, p, original, chosen, positive, related⟩ :=
                back index (.node ownerEntry ownerRows ownerDepth ownerFree) found q positive
              exact ⟨j, p, original, chosen, positive, rel_covers keptCovered related⟩)
          have currentReady : EqReady later.constraints (.live combinedIdentity outputs) := by
            apply combinedReady.grows
            simpa only [inheritedShape] using currentGrowth.constraint_growth
          have checked := SourceEqualityConstraintMemoAllocation.descend_correct
            (.live combinedIdentity outputs) index later laterValid currentReady
          have payloadNe : (SourceEqualityConstraintMemoAllocation.descend
              (.live combinedIdentity outputs) index later).1.payload ≠ request.inherited.payload := by
            rw [checked.2.2.1, inheritedShape]
            exact separated
          have totalGrowth : Grows prefixBefore
              (SourceEqualityConstraintMemoAllocation.descend (.live combinedIdentity outputs) index later).2 := by
            have first : Grows prefixBefore (SourceCurrentAllocatedInheritedPrefix.run
                request.value.entry.key.constraint request.inherited prefixBefore).2 := by
              simpa only [inheritedShape] using prefixGrowth
            exact SourceCurrentConjunctionEquality.grows_trans first
              (SourceCurrentConjunctionEquality.grows_trans currentGrowth checked.2.2.2)
          rw [inheritedShape] at payloadNe
          refine ⟨returnedGuard, nonplain, payloadNe, ?_⟩
          intro sameKey
          have sameValues := SourceEqualityConstraintMemoAllocation.ready_eq_of_identity _ checked.1.constraints
            _ _ checked.2.1 (inputReady.grows totalGrowth.constraint_growth) (congrArg Prod.fst sameKey)
          exact payloadNe (congrArg SourceEqualityConstraintAllocation.Value.payload sameValues)

end MicroCFTA.SourceCurrentResourceOwnerInheritedProgress
