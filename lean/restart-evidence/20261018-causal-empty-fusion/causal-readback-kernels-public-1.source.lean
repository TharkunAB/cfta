import MicroCFTA.SourceCurrentCausalStoredMuReadback
namespace MicroCFTA.CausalReadbackKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryDepthHeap (usesLocal)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceCurrentNativeMuPublication (History)
open SourceEqualityRequiredCache (Ready Keeps)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (NodeKey)
open InternedRootProfile (profile Equivalent)

private def source : Syntax Nat Bool := .binder true (.node [.mk 7 true [.var 0]])
private def snapshot : State Nat Bool := (build source [] empty).state
private def outer : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = .uninterned 93 then some .empty else none

private def rowValue (nodeId edgeId : Nat) (name : InternedBinderProtocol.Reference) : Value Nat Bool :=
  .node ⟨nodeId,.node [edgeId]⟩
    [.mk ⟨edgeId,⟨7,[.ref name],true⟩⟩ [.reference name]] 0 [name]

private theorem selected : ∃ (entry : Interned NodeKey) (body depth ordinary : Value Nat Bool),
    build source [] empty = .done (.mu entry body depth ordinary) snapshot ∧
    snapshot.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
    usesLocal depth ordinary = true := by
  refine ⟨⟨2,muKey (rowValue 0 0 .depth) (rowValue 1 1 (.uninterned 0))⟩,
    rowValue 3 2 (.interned 2),rowValue 0 0 .depth,rowValue 1 1 (.uninterned 0),?_,?_,?_⟩ <;> cbv

private theorem checked_witness :
    ∃ (reader : State Nat Bool) (entry : Interned NodeKey) (body depth ordinary : Value Nat Bool),
      build (.binder true (.node [.mk 7 true [.var 0]])) [] empty = .done (.mu entry body depth ordinary) reader ∧
      Ready reader ∧ Nonempty (History empty reader) ∧
      reader.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      usesLocal depth ordinary = true ∧
      ∃ left middle right after,
        execute body (bind (.interned entry.identity) .empty
          (fun name => if name = .uninterned 93 then some .empty else none)) reader = .done left middle ∧
        execute ordinary (bind (.uninterned (ordinaryLevel depth)) .empty
          (fun name => if name = .uninterned 93 then some .empty else none)) middle = .done right after ∧
        Keeps reader middle ∧ Keeps middle after ∧ Available after left ∧ Available after right ∧
        Nonempty (History reader middle) ∧ Nonempty (History middle after) ∧
        after.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
        Equivalent (profile left) (profile right) ∧
        (left.referenceOf == .empty) = (right.referenceOf == .empty) := by
  obtain ⟨entry,body,depth,ordinary,actual,present,used⟩ := selected
  have ready := SourceEqualityRequiredCache.constructed source (.mu entry body depth ordinary) snapshot actual
  have history : Nonempty (History empty snapshot) := by
    simpa only [actual,InternedNestedConstruction.Outcome.state] using
      SourceCurrentNativeMuPublication.build_history source [] empty SourceCurrentConstrainedCapSourceHistory.empty_context
  have replacements : InternedStoredSubstitution.Replacements snapshot outer := by
    intro name value found
    dsimp only [outer] at found
    split at found
    · cases found
      exact empty_available snapshot
    · cases found
  obtain ⟨left,middle,right,after,firstDone,secondDone,first,second,leftAvailable,rightAvailable,
    firstHistory,secondHistory,_middlePresent,finalPresent,profiles,flags⟩ :=
    SourceCurrentCausalStoredMuReadback.complete (muKey depth ordinary) entry body depth ordinary snapshot ready
      (Classical.choice history) present outer replacements .empty (empty_available snapshot)
  exact ⟨snapshot,entry,body,depth,ordinary,actual,ready,history,present,used,left,middle,right,after,
    firstDone,secondDone,first,second,leftAvailable,rightAvailable,firstHistory,secondHistory,finalPresent,profiles,flags⟩

theorem actual_used_empty_replacement :
    ∃ (reader : State Nat Bool) (entry : Interned NodeKey) (body depth ordinary : Value Nat Bool),
      build (.binder true (.node [.mk 7 true [.var 0]])) [] empty = .done (.mu entry body depth ordinary) reader ∧
      Ready reader ∧ Nonempty (History empty reader) ∧
      reader.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      usesLocal depth ordinary = true ∧
      ∃ left middle right after,
        execute body (bind (.interned entry.identity) .empty
          (fun name => if name = .uninterned 93 then some .empty else none)) reader = .done left middle ∧
        execute ordinary (bind (.uninterned (ordinaryLevel depth)) .empty
          (fun name => if name = .uninterned 93 then some .empty else none)) middle = .done right after ∧
        Keeps reader middle ∧ Keeps middle after ∧ Available after left ∧ Available after right ∧
        Nonempty (History reader middle) ∧ Nonempty (History middle after) ∧
        after.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
        Equivalent (profile left) (profile right) ∧
        (left.referenceOf == .empty) = (right.referenceOf == .empty) := checked_witness
end MicroCFTA.CausalReadbackKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.CausalReadbackKernels.actual_used_empty_replacement
#print MicroCFTA.CausalReadbackKernels.actual_used_empty_replacement
#print axioms MicroCFTA.CausalReadbackKernels.actual_used_empty_replacement
