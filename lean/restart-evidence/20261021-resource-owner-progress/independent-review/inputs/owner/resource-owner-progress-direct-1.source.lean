import MicroCFTA.SourceCurrentResourceParentWriters
import MicroCFTA.SourceCurrentActualOwnerSelection
import MicroCFTA.SourceCurrentActualOwnerPair
import MicroCFTA.SourceCurrentDelayedCombinedOwnerProgress

namespace MicroCFTA.SourceCurrentResourceOwnerProgress
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
local notation "Written" => SourceCurrentResourceParentWriters.Written
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {bits : Nat}

theorem key_ne_top
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {request : EdgeRequest} {returned : Edge}
    (written : Written (bits := bits) formulas solver request returned)
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
    (identity : Nat) (top : EqReady prefixBefore.constraints (.live identity [])) :
    let child := SourceEqualityConstraintMemoAllocation.descend combined index later
    returned.entry.key.constraint = request.value.entry.key.constraint ∧
      SourceMemoGate.plain request.value.entry.key.constraint = false ∧
      child.1.payload ≠ some [] ∧
      (NodeRequest.mk child.1 (.node ownerEntry ownerRows ownerDepth ownerFree)).key ≠
        (NodeRequest.mk (.live identity []) (.node ownerEntry ownerRows ownerDepth ownerFree)).key := by
  obtain ⟨g,s,r,e,p,h,m,c,n,budget,writerBefore,writerAfter,savedFourth,savedMerge,
      globals,inventory,profile,observed,context,frame,fits,inheritedReady,resident,
      liveInputs,reserved,normal,supported,⟨causal⟩,merged,positiveMemo⟩ := written
  obtain ⟨loaded,middle,records,kept,scanned,scanFourth,preparedValues,preparedHeap,
      noncontradictory,loadedAt,_reduced,_built,_accepted,precheck,scanCall,nonempty,
      requiredCall,passCall,_sameFourth,primary⟩ :=
    SourceCurrentActualOwnerSelection.selected observed context.ready.good context.stored liveInputs member found
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
          simpa only [keep,ite_true,readback] using constructed.guard
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
  cases combined with
  | contradiction => exact False.elim (live rfl)
  | live combinedIdentity outputs =>
      obtain ⟨nonplain,_covered,_fixed,paths,selected,left,right,first,second,different⟩ :=
        SourceCurrentActualOwnerPair.required_pair formulas solver inventory preparedInventory member
          precheckReceipt retained nonempty requiredReceipt scanReady.semantic scanNormal scanReady.costs
          scanValues primary scanCurrent scanSupport scanHistory passReads physical context.covered
          preparedValid merged positiveMemo found prefixBefore valid ready currentField
          (.live combinedIdentity outputs) currentPrefix outputs rfl
      have child := SourceCurrentDelayedCombinedOwnerProgress.key_ne_top request.value.entry.key.constraint
        request.inherited prefixBefore valid ready currentField (.live combinedIdentity outputs) currentPrefix
        later laterValid currentGrowth paths selected index left right first second different identity top
        (.node ownerEntry ownerRows ownerDepth ownerFree) (.node ownerEntry ownerRows ownerDepth ownerFree)
      exact ⟨returnedGuard,nonplain,child.2.2.2.2.1,child.2.2.2.2.2⟩

end MicroCFTA.SourceCurrentResourceOwnerProgress
