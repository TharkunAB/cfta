import MicroCFTA.SourceCurrentConstrainedCapCallbackCertificates

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.PendingCallbackKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Outcome finish)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapPairOccurrences

private def key : NodeKey := muKey (Value.empty (Symbol := Nat) (Guard := Bool)) .empty
private def own : Interned NodeKey := (Cache.intern (empty (Symbol := Nat) (Guard := Bool)).nodes key).1
private def allocated : State Nat Bool := {empty with nodes := (Cache.intern empty.nodes key).2}
private def old : Reference := .intersection 4 5
private def weight (name : Reference) : Nat := if name = old then 1 else 0

/-- A real unfinished outer key permits the derived callback receipt and empty candidate. -/
theorem pending_outer :
    allocated.nodeRecords key = none ∧
      ∃ after, SourceRecursiveIntersectionMaybeMu.callback old (.reference old) (.interned own.identity) allocated =
          .done (.reference (.interned own.identity)) after ∧
        Covered [key] after ∧ after.nodeRecords key = none ∧
        SourceCurrentConstrainedCap.Cap (fun guard => guard = true) 0
          (finish true (.mu own (.reference (.interned own.identity)) .empty .empty)) ∧
        Classified weight 1 (finish true (.mu own (.reference (.interned own.identity)) .empty .empty)) := by
  have heap : SourceRecursiveIntersectionSemanticHeap.SemanticHeap allocated :=
    ⟨InternedFreshOrdinaryContext.empty_context.reserve key, InternedFreshOrdinaryDepthHeap.empty_heap⟩
  have source : Available allocated (Value.reference (Symbol := Nat) (Guard := Bool) old) := by
    apply reference_available
    intro identity member
    simp [Value.free, old] at member
  have marker : Available allocated (.reference (.interned own.identity)) :=
    (InternedConstructionProvenance.reserve_available key empty InternedNestedFacts.empty_facts.coherent
      InternedNestedFacts.empty_facts.cached).2
  have covered : Covered [key] allocated := InternedNestedCoverage.reserve_covered key empty empty_correct.2
  have stored : SourceCurrentHereditaryConstruction.MuStored (fun guard => guard = true) allocated :=
    (SourceCurrentHereditaryConstruction.MuStored.empty _).reserve key
  have classified : Classified weight 1 (Value.reference (Symbol := Nat) (Guard := Bool) old) :=
    reference weight 1 old (by simp [weight])
  have actual : SourceRecursiveIntersectionMaybeMu.callback old (.reference old) (.interned own.identity) allocated =
      .done (.reference (.interned own.identity)) allocated := by cbv
  have checked := SourceCurrentConstrainedCapCallbackCertificates.candidate_of_actual (fun guard => guard = true) 0
    (.reference old) old own allocated heap source marker (.plain 0 (.reference old)) stored weight 1 (by decide)
    (by simp [weight]) classified (by simp [Value.free, old]) [key] covered _ allocated actual .empty .empty
  exact ⟨rfl, allocated, actual, checked.2.2.2.2.1, rfl, checked.1, checked.2.1⟩

#print axioms pending_outer
#check @pending_outer
end MicroCFTA.PendingCallbackKernels
