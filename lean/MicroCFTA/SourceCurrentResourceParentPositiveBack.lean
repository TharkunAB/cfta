import MicroCFTA.SourceCurrentResourceOwnerInheritedProgress
import MicroCFTA.SourceCurrentActualParentBranchCases
import MicroCFTA.SourceCurrentSelectedPrimaryOrigins
import MicroCFTA.SourceCurrentAllocatedPartialReturnedDomain

namespace MicroCFTA.SourceCurrentResourceParentPositiveBack
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState (EdgeRequest)
open SourceCurrentRequiredPositivePosition (PositiveAt)
open SourceCurrentNormalizedChildSeparation (Rel)
open SourceCurrentAllocatedPartialReturnedDomain (Shape)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Valid" => SourceEqualityConstraintMemoAllocation.Valid
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
    EqualityNormalize.Covers selected (outputs.map SourceEqualityClassOrder.Record.paths) := by
  obtain ⟨own,loaded,accessorValid,ownReady,ownClasses,_ownRead,accessorGrowth⟩ :=
    SourceCurrentConjunctionEquality.accessor_correct original before valid field
  obtain ⟨result,computed,_finalValid,_resultReady,_growth,_fixed,covers⟩ :=
    SourceCurrentOuterOriginDependencies.combine_covers (.live identity inherited) own
      (SourceCurrentConjunctionEquality.accessor original before).2 accessorValid
      (ready.grows accessorGrowth.constraint_growth) ownReady
  have equation : (SourceCurrentAllocatedInheritedPrefix.run original (.live identity inherited) before).1 =
      .ok (some result) := by
    rw [SourceCurrentAllocatedInheritedPrefix.run_combine original identity inherited before own loaded]
    simp only [computed,Except.map]
  have same := Option.some.inj (Except.ok.inj (equation.symm.trans actual))
  subst result
  intro paths member
  apply covers outputs rfl paths
  apply List.mem_append.mpr
  apply Or.inr
  rw [ownClasses]
  exact ownSelected paths member

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {bits : Nat}

theorem children
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {request : EdgeRequest} {returned : Edge}
    (written : SourceCurrentResourceParentWriters.Written (bits := bits) formulas solver request returned)
    (prefixBefore : Operations) (valid : Valid prefixBefore)
    (ready : EqReady prefixBefore.constraints request.inherited)
    (field : SourceCurrentConjunctionEquality.FieldAvailable prefixBefore returned.entry.key.constraint)
    (combinedIdentity : Nat) (classes : List Record)
    (prefixActual : (SourceCurrentAllocatedInheritedPrefix.run returned.entry.key.constraint
      request.inherited prefixBefore).1 = .ok (some (.live combinedIdentity classes))) :
    (SourceCompactGuards.sourceEqualities request.value.entry.key.constraint = some [] →
      Shape request.value returned) ∧
    ∀ outputIndex child, returned.children[outputIndex]? = some child →
      ∀ residual, PositiveAt child residual →
        ∃ inputIndex originalPath original, request.value.children[inputIndex]? = some original ∧
          PositiveAt original originalPath ∧
          Rel (classes.map SourceEqualityClassOrder.Record.paths)
            (outputIndex :: residual) (inputIndex :: originalPath)
 := by
  obtain ⟨g,s,r,e,p,h,m,c,n,budget,writerBefore,writerAfter,savedFourth,savedMerge,
      globals,inventory,profile,observed,context,frame,fits,inheritedReady,resident,
      liveInputs,reserved,normal,supported,⟨causal⟩,merged,positiveMemo⟩ := written
  have nativeGood := SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked context.ready.good) context.ready.semantic context.ready.costs
  rcases SourceCurrentActualParentBranchCases.edge_cases observed nativeGood context.stored liveInputs with
      unchanged | erased | sentinel | selected
  · refine ⟨fun _ => Or.inl unchanged,?_⟩
    intro index child found residual positive
    exact ⟨index,residual,child,by simpa only [unchanged] using found,positive,.refl _⟩
  · refine ⟨fun _ => Or.inr (Or.inl erased),?_⟩
    intro index child found residual positive
    have inside := List.mem_of_getElem? found
    rw [erased] at inside
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp inside
    cases positive
  · refine ⟨fun _ => Or.inr (Or.inr sentinel),?_⟩
    intro index child found residual positive
    have inside := List.mem_of_getElem? found
    rw [sentinel] at inside
    have same : child = .empty := List.mem_singleton.mp inside
    subst child
    cases positive
  · obtain ⟨loaded,middle,records,kept,scanned,scanFourth,preparedValues,preparedHeap,
        noncontradictory,loadedAt,_reduced,_built,_accepted,precheck,scanCall,nonempty,
        requiredCall,passCall,_sameFourth⟩ := selected
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
    obtain ⟨_proper,raw,_rawRead,sourceClasses,order,recordFields⟩ := precheckReceipt.classes records rfl
    have retainedFields := retained.fields
    have ownNonempty : SourceCompactGuards.sourceEqualities request.value.entry.key.constraint ≠ some [] := by
      intro ownEmpty
      have rawEmpty : raw = [] := List.map_eq_nil_iff.mp (Option.some.inj (sourceClasses.symm.trans ownEmpty))
      have recordsEmpty : records = [] := by rw [order,rawEmpty]; rfl
      exact nonempty (List.sublist_nil.mp (recordsEmpty ▸ retainedFields.1))
    have ownSelected : ∀ paths ∈ kept.map SourceEqualityClassOrder.Record.paths,
        paths ∈ (SourceCompactGuards.sourceEqualities request.value.entry.key.constraint).getD [] := by
      intro paths chosen
      obtain ⟨record,member,rfl⟩ := List.mem_map.mp chosen
      have rawMember : record ∈ raw := (SourceEqualityClassOrder.ordered_perm raw).mem_iff.mp
        (by simpa only [order] using retainedFields.1.subset member)
      rw [sourceClasses]
      exact List.mem_map.mpr ⟨record,rawMember,rfl⟩
    have coherent : ∀ record ∈ kept, SourceEqualityClassOrder.Coherent record :=
      fun record member => (recordFields record (retainedFields.1.subset member)).1
    have active : ∀ record ∈ kept, EqualityNormalize.Nontrivial record.paths :=
      fun record member => (recordFields record (retainedFields.1.subset member)).2.2
    have prefixGood := SourceCurrentNativeOperationHeap.Good.of_native
      (SourceCurrentNativeOperationInvariants.Good.of_checked precheckReceipt.ready.good)
      precheckReceipt.ready.semantic precheckReceipt.ready.costs
    have primary := SourceCurrentSelectedPrimaryOrigins.selected_class scanCall prefixGood _available
    have gates : ∀ paths ∈ kept.map SourceEqualityClassOrder.Record.paths,
        EndpointStatefulGateTrace.ClassTrace SourceMemoGate.unconstrained
          (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) request.value.children paths
          scanned.native.machine.heap false scanned.native.machine.heap := by
      intro paths chosen
      obtain ⟨record,member,rfl⟩ := List.mem_map.mp chosen
      exact primary record member
    have physical : SourceCurrentMemoMergeEffects.Stored scanned.native.machine.heap writerBefore.merge :=
      context.stored.grows scanEffects.keeps
    obtain ⟨_next,_receipt,_currentAfter,_mergedAfter,_corridors,
        _supportedAfter,_causalAfter,_positiveAfter,back⟩ :=
      SourceCurrentRequiredPositiveChronology.pass formulas solver preparedInventory requiredReceipt
        scanReady.semantic scanNormal scanReady.costs scanValues gates scanCurrent scanSupport scanHistory
        kept rfl coherent active passReads physical context.covered preparedValid merged positiveMemo
    refine ⟨fun ownEmpty => False.elim (ownNonempty ownEmpty),?_⟩
    intro outputIndex child found residual positive
    obtain ⟨inputIndex,originalPath,original,originalFound,originalPositive,related⟩ :=
      back outputIndex child found residual positive
    have readback : SourceEqualityConjoinAllocation.readback loaded = request.value.entry.key.constraint :=
      (SourceEqualityConstraintFieldLookup.load_ready request.value.entry.key.constraint
        writerBefore.checked.operations.constraints context.ready.good.operations.constraints
        fieldAt.1 loaded loadedAt).2
    have returnedGuard : returned.entry.key.constraint = request.value.entry.key.constraint := by
      rcases numeric.semantic.construction with rejected | ⟨children,constructorBefore,_length,constructed⟩
      · have inside := List.mem_of_getElem? found
        rw [rejected.children] at inside
        have same : child = .empty := List.mem_singleton.mp inside
        subst child
        cases positive
      · cases keep : SourceEqualityMkEdgeAllocation.accepted
            (SourceEqualityConjoinAllocation.readback loaded) children.length with
        | false =>
            have emptyChildren : returned.children = [.empty] := by
              simpa only [keep,Bool.false_eq_true,ite_false] using constructed.children
            have inside := List.mem_of_getElem? found
            rw [emptyChildren] at inside
            have same : child = .empty := List.mem_singleton.mp inside
            subst child
            cases positive
        | true =>
            have acceptedGuard : returned.entry.key.constraint = SourceEqualityConjoinAllocation.readback loaded := by
              simpa only [keep,ite_true] using constructed.guard
            exact acceptedGuard.trans readback
    have currentField : SourceCurrentConjunctionEquality.FieldAvailable prefixBefore request.value.entry.key.constraint := by
      simpa only [returnedGuard] using field
    have currentPrefix : (SourceCurrentAllocatedInheritedPrefix.run request.value.entry.key.constraint
        request.inherited prefixBefore).1 = .ok (some (.live combinedIdentity classes)) := by
      simpa only [returnedGuard] using prefixActual
    cases inheritedShape : request.inherited with
    | contradiction =>
        rw [inheritedShape,SourceCurrentAllocatedInheritedPrefix.run_contradiction] at currentPrefix
        cases currentPrefix
    | live inheritedIdentity inheritedRecords =>
        have inputReady := ready
        rw [inheritedShape] at inputReady
        have computed := currentPrefix
        rw [inheritedShape] at computed
        have covered := prefix_data request.value.entry.key.constraint inheritedIdentity inheritedRecords
          prefixBefore valid inputReady currentField combinedIdentity classes computed _ ownSelected
        exact ⟨inputIndex,originalPath,original,originalFound,originalPositive,rel_covers covered related⟩

end MicroCFTA.SourceCurrentResourceParentPositiveBack
