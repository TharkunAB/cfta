import MicroCFTA.SourceCurrentConstrainedCapWarmOccurrences

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.WarmOccurrenceKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome finish)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapPairOccurrences
open SourceCurrentConstrainedCapPairOccurrenceCallbacks (mark)

private def program : Syntax Nat Bool := .binder false (.node [.mk 7 false []])

private def cell : Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool × State Nat Bool :=
  match InternedFreshOrdinaryConstruction.build program [] empty with
  | .done (.mu entry body depth ordinary) state => (entry, body, depth, ordinary, state)
  | _ => (⟨0, muKey (Value.empty (Symbol := Nat) (Guard := Bool)) .empty⟩, .empty, .empty, .empty, empty)

private def warm
    (next : Reference → State Nat Bool → Outcome Nat Bool (Value Nat Bool)) : Outcome Nat Bool (Value Nat Bool) :=
  (InternedFreshOrdinaryConstruction.build program [] empty).bind fun value state =>
    match value with
    | .mu _ _ depth ordinary => InternedNestedConstruction.request true depth ordinary next state
    | _ => .done value state

/-- An actual cold source constructs the populated cell used by the next literal warm request. -/
theorem actual_warm
    (next : Reference → State Nat Bool → Outcome Nat Bool (Value Nat Bool)) :
    ∃ value state, warm next = .done value state ∧
      ¬ SourceEqualityAnnotationLanguage.Annotated (fun guard => guard = true) value ∧
      SourceCurrentConstrainedCap.Cap (fun guard => guard = true) 1 value ∧
      Classified (fun _ => 0) 1 value := by
  have produced : ∃ entry body depth ordinary state,
      InternedFreshOrdinaryConstruction.build program [] empty = .done (.mu entry body depth ordinary) state ∧
      state.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      body.free = [] ∧ depth.free = [] ∧ ordinary.free = [] ∧
      ¬ SourceEqualityAnnotationLanguage.Annotated (fun guard => guard = true) body ∧
      SourceCurrentConstrainedCap.Cap (fun guard => guard = true) 1 body := by
    refine ⟨cell.1, cell.2.1, cell.2.2.1, cell.2.2.2.1, cell.2.2.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · intro annotated
      cases annotated with
      | node _ _ _ _ guards _ =>
          have impossible : false = true := guards _ (by simp)
          cases impossible
    · exact .node 0 _ _ _ _ (by intro child member; simp at member)
  obtain ⟨entry, body, depth, ordinary, state, built, present, bodyFree, depthFree, ordinaryFree,
    notAnnotated, bounded⟩ := produced
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed program (.mu entry body depth ordinary) state built
  have verified := InternedFreshOrdinaryFacts.build_verified program [] empty empty_facts
    (by intro value member; cases member)
  have available := verified.result _ _ built
  have depthAvailable := available.children depth (by simp [children])
  have ordinaryAvailable := available.children ordinary (by simp [children])
  have depthClassified : Classified (mark (fun _ => 0) .depth 1) 1 depth := by
    apply of_below _ _ depth state semantic.1.normal.facts.coherent depthAvailable
    all_goals intro name member; rw [depthFree] at member; cases member
  have ordinaryClassified : Classified (mark (fun _ => 0)
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) 1) 1 ordinary := by
    apply of_below _ _ ordinary state semantic.1.normal.facts.coherent ordinaryAvailable
    all_goals intro name member; rw [ordinaryFree] at member; cases member
  have checked := SourceCurrentConstrainedCapWarmOccurrences.request_hit (fun _ => 0) 1 depth ordinary
    (.mu entry body depth ordinary) state next semantic depthAvailable ordinaryAvailable present (by decide)
    depthClassified ordinaryClassified
  have cleanup : finish true (.mu entry body depth ordinary) = body := by
    simp [finish, InternedConstructorTemplates.cleanup, bodyFree]
  rw [cleanup] at checked
  refine ⟨body, state, ?_, notAnnotated, bounded, checked.2⟩
  unfold warm
  rw [built]
  exact checked.1

#print axioms actual_warm
#check @actual_warm
end MicroCFTA.WarmOccurrenceKernels
