import MicroCFTA.SourceCurrentNativeCallbackErasure

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 200000000
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs.threshold 254
set_option pp.maxSteps 10000000

namespace MicroCFTA.CallbackErasureKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedBinderProtocol (Reference NodeRef)
open SourceCurrentNativeCallbackErasure

private def old : Reference := .intersection 2 3
private def captured : Reference := .uninterned 7
private def marker : Reference := .uninterned 30
private def environment : List (Value Nat Unit) := [.reference old, .reference captured]

private def program (smart used : Bool) : Syntax Nat Unit :=
  .union [.var 0, .binder smart (.node [.mk 0 () (if used then [.var 0, .var 2] else [.var 2])])]

private def built (smart used : Bool) :=
  InternedFreshOrdinaryConstruction.build (program smart used) environment empty

private def valueOf (outcome : Outcome Nat Unit (Value Nat Unit)) : Value Nat Unit :=
  match outcome with
  | .done value _ => value
  | .pending _ _ => .empty

private def source (smart used : Bool) := valueOf (built smart used)
private def heap (smart used : Bool) := (built smart used).state

private def branch (smart used : Bool) : Value Nat Unit :=
  match source smart used with
  | .union _ members _ _ => members[1]?.getD .empty
  | _ => .empty

private def called (smart used : Bool) :=
  SourceRecursiveIntersectionMaybeMu.callback old (source smart used) marker (heap smart used)

private def returned (smart used : Bool) := valueOf (called smart used)
private def stopped (smart used : Bool) := (called smart used).state

private theorem inputs (state : State Nat Unit) : InternedNestedProvenance.Values state environment := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact reference_available state old (by intro identity impossible; cases impossible)
  · rcases List.mem_cons.mp member with rfl | impossible
    · exact InternedNestedProvenance.ordinary_available state 7
    · cases impossible

private theorem built_done (smart used : Bool) :
    built smart used = .done (source smart used) (heap smart used) := by
  cases smart <;> cases used <;> cbv

private theorem initial (smart used : Bool) :
    SourceRecursiveIntersectionSemanticHeap.SemanticHeap (heap smart used) ∧
      Available (heap smart used) (source smart used) := by
  have actual := built_done smart used
  have physical := InternedFreshOrdinaryFacts.build_verified (program smart used) environment empty
    InternedStoredMuOrigins.empty_normal.facts (inputs empty)
  refine ⟨?_, physical.result _ _ actual⟩
  simpa only [built, actual, Outcome.state] using
    SourceRecursiveIntersectionSemanticHeap.source (program smart used) environment empty
      SourceRecursiveIntersectionSemanticHeap.empty_heap (inputs empty)

private theorem called_done (smart used : Bool) :
    called smart used = .done (returned smart used) (stopped smart used) := by
  cases smart <;> cases used <;> cbv

private theorem unused (smart used : Bool) :
    marker ∉ InternedDeepFreeDepth.deepNames (returned smart used) := by
  cases smart <;> cases used <;> cbv <;> simp

/-- An actual open raw Mu is rebuilt before the callback erasure proves exact replacement independence. -/
theorem raw_nested_reconstruction :
    ∃ body before value after,
      SourceRecursiveIntersectionSemanticHeap.SemanticHeap before ∧ Available before body ∧
      body.free ≠ [] ∧
      (∃ entry inner depth ordinary,
        branch false false = .mu entry inner depth ordinary ∧ inner.free ≠ []) ∧
      SourceRecursiveIntersectionMaybeMu.callback old body marker before = .done value after ∧
      value.referenceOf ≠ (branch false false).referenceOf ∧
      Available after (eraseSelf marker value) ∧ marker ∉ (eraseSelf marker value).free ∧
      ∀ first second : Value Nat Unit,
        InternedFreshOrdinaryStoredSubstitution.execute (eraseSelf marker value)
            (InternedStoredSubstitutionRebind.replacement marker first) after =
          InternedFreshOrdinaryStoredSubstitution.execute (eraseSelf marker value)
            (InternedStoredSubstitutionRebind.replacement marker second) after := by
  have start := initial false false
  have argument := InternedNestedProvenance.ordinary_available (heap false false) 30
  have actual := called_done false false
  have result := native_callback_result old marker (source false false) (heap false false)
    start.1 start.2 argument (returned false false) (stopped false false) actual (unused false false)
  refine ⟨source false false, heap false false, returned false false, stopped false false,
    start.1, start.2, ?_, ?_, actual, ?_, result.2.1, result.2.2, ?_⟩
  · cbv; simp
  · exact ⟨_, _, _, _, by cbv, by cbv; simp⟩
  · cbv; simp
  · intro first second
    exact native_callback_replace old marker (source false false) (heap false false)
      start.1 start.2 argument (returned false false) (stopped false false) actual (unused false false)
      (stopped false false) (grows_refl _) (extends_refl _) result.1.normal.facts.coherent first second

/-- An actual retained open Mu reconstructs through its populated key and replays with every new replacement. -/
theorem warm_nested_replay :
    ∃ body before value after,
      SourceRecursiveIntersectionSemanticHeap.SemanticHeap before ∧ Available before body ∧
      SourceRecursiveIntersectionMaybeMu.callback old body marker before = .done value after ∧
      (∃ entry inner depth ordinary,
        value = .mu entry inner depth ordinary ∧ value.free ≠ [] ∧
        before.nodeRecords (muKey depth ordinary) = some value) ∧
      InternedFreshOrdinaryStoredSubstitution.execute (eraseSelf marker value)
        (InternedStoredSubstitutionRebind.replacement marker (.empty : Value Nat Unit)) after = .done value after ∧
      ∀ later, Grows after later → ∀ replacement : Value Nat Unit,
        InternedFreshOrdinaryStoredSubstitution.execute (eraseSelf marker value)
          (InternedStoredSubstitutionRebind.replacement marker replacement) later = .done value later := by
  have start := initial true true
  have argument := InternedNestedProvenance.ordinary_available (heap true true) 30
  have actual := called_done true true
  have original : InternedFreshOrdinaryStoredSubstitution.execute (eraseSelf marker (returned true true))
      (InternedStoredSubstitutionRebind.replacement marker (.empty : Value Nat Unit)) (stopped true true) =
      .done (returned true true) (stopped true true) := by cbv
  refine ⟨source true true, heap true true, returned true true, stopped true true,
    start.1, start.2, actual, ?_, original, ?_⟩
  · exact ⟨_, _, _, _, by cbv, by cbv; simp, by cbv⟩
  · intro later growth replacement
    rw [SourceRecursiveIntersectionMaybeMu.callback_eq old (source true true) marker (heap true true)
      (heap true true) start.1.1.normal.facts start.2] at actual
    exact callback_replay _ _ marker (heap true true) (by
      exact ⟨start.1.1.normal, InternedStoredSubstitution.leaves_available _ _ start.2,
        start.1.1.profiles, start.1.1.freeNames⟩)
      argument (returned true true) (stopped true true) actual (unused true true)
      .empty replacement (returned true true) (stopped true true) later original growth

#check @raw_nested_reconstruction
#print axioms raw_nested_reconstruction
#check @warm_nested_replay
#print axioms warm_nested_replay
end MicroCFTA.CallbackErasureKernels
