import MicroCFTA.SourceCurrentConstrainedCapNativeBinderReturn

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000

namespace MicroCFTA.ProbeBinderKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapNativeProbeSupport (ProbeFree)

private def pendingKey : NodeKey := .mu ⟨.empty, .empty⟩
private def pending : State Nat Bool :=
  {(empty : State Nat Bool) with nodes := (Cache.intern (empty : State Nat Bool).nodes pendingKey).2}

private theorem semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap pending := by
  have initial : SourceCurrentConstrainedCapSourceHistory.Context (empty : State Nat Bool) [] :=
    SourceCurrentConstrainedCapSourceHistory.empty_context
  have joint := initial.reserve pendingKey
  exact ⟨joint.base, joint.depth⟩

/-- Actual interned source names are probe-free although they do not satisfy intersection-only support. -/
theorem original_interned_support :
    let name := (Cache.intern (empty : State Nat Bool).nodes pendingKey).1.identity
    Available pending (.reference (.interned name)) ∧ ProbeFree (Value.reference (Symbol := Nat) (Guard := Bool) (.interned name)) ∧
      ¬(∀ reference ∈ (Value.reference (Symbol := Nat) (Guard := Bool) (.interned name)).free,
          ∃ first second, reference = .intersection first second) := by
  dsimp only
  let name := (Cache.intern (empty : State Nat Bool).nodes pendingKey).1.identity
  have reserved := InternedConstructionProvenance.reserve_available pendingKey (empty : State Nat Bool)
    InternedNestedFacts.empty_facts.coherent InternedNestedFacts.empty_facts.cached
  have available : Available pending (.reference (.interned name)) := reserved.2
  refine ⟨available, SourceCurrentConstrainedCapNativeProbeSupport.of_original pending semantic.1.normal.facts
    _ (.reference name) available, ?_⟩
  intro supported
  obtain ⟨_, _, impossible⟩ := supported (.interned name) (by simp [Value.free])
  cases impossible

private def old : Reference := .intersection 0 1
private def body : Value Nat Bool := .reference old
private def weight (name : Reference) : Nat := if name = old then 1 else 0

set_option cbv.maxSteps 100000000 in
private theorem computed :
    (match SourceRecursiveIntersectionMaybeMu.maybeMu (0, 1) body pending with
    | .done value _ => value = .empty
    | .pending .. => False) := by cbv

/-- A literal used-marker binder returns with both local laws while an unrelated constructor key is unfinished. -/
theorem completed_during_reservation :
    ¬Covered [] pending ∧ ∃ after,
      SourceRecursiveIntersectionMaybeMu.maybeMu (0, 1) body pending = .done .empty after ∧
      SourceCurrentConstrainedCap.Cap (fun guard : Bool => guard = true) 1 (Value.empty (Symbol := Nat)) ∧
      SourceCurrentConstrainedCapPairOccurrences.Classified weight 1 (Value.empty (Symbol := Nat) (Guard := Bool)) ∧
      SourceCurrentConstrainedCapPairOccurrences.Classified (fun _ => 0) 0 (Value.empty (Symbol := Nat) (Guard := Bool)) ∧
      SourceCurrentConstrainedCapGuardHeap.Heap (fun guard : Bool => guard = true) after ∧
      SourceRecursiveIntersectionSemanticHeap.SemanticHeap after ∧ ProbeFree (Value.empty (Symbol := Nat) (Guard := Bool)) := by
  have notCovered : ¬Covered [] pending := by
    intro covered
    have table := (Cache.intern_correct (empty : State Nat Bool).nodes pendingKey Cache.empty_valid).2.1
    rcases covered.nodes pendingKey _ table with absent | ⟨value, present⟩
    · cases absent
    · cases present
  refine ⟨notCovered, ?_⟩
  have available : Available pending body := reference_available pending old (by
    intro name member
    simp [old, Value.free] at member)
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap (fun guard : Bool => guard = true) pending := by
    intro key entry body depth ordinary absent
    cases absent
  have classified : SourceCurrentConstrainedCapPairOccurrences.Classified weight 1 body :=
    SourceCurrentConstrainedCapPairOccurrences.reference weight 1 old (by simp [weight])
  have fresh : ProbeFree body := SourceCurrentConstrainedCapNativeProbeSupport.intersection 0 1
  cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu (0, 1) body pending with
  | pending key stopped => simpa only [actual] using computed
  | done value after =>
      have same : value = .empty := by simpa only [actual] using computed
      subst value
      have positive := SourceCurrentConstrainedCapNativeBinderReturn.positive (fun guard : Bool => guard = true) 1 (0, 1)
        body pending semantic available (.plain 1 (.reference old)) guards weight 1 (by decide)
        (by simp [weight, old]) classified fresh .empty after actual
      have zeroClassified : SourceCurrentConstrainedCapPairOccurrences.Classified (fun _ => 0) 0 body :=
        SourceCurrentConstrainedCapPairOccurrences.reference (fun _ => 0) 0 old (by decide)
      have zero := SourceCurrentConstrainedCapNativeBinderReturn.zero (fun guard : Bool => guard = true) 1 (0, 1)
        body pending semantic available (.reference old) guards (fun _ => 0) zeroClassified fresh .empty after actual
      exact ⟨after, rfl, positive.1, positive.2.1, zero.2.1, positive.2.2.1,
        positive.2.2.2.2.2.1, positive.2.2.2.2.2.2.2.2⟩

#print axioms original_interned_support
#check @original_interned_support
#print axioms completed_during_reservation
#check @completed_during_reservation
end MicroCFTA.ProbeBinderKernels
