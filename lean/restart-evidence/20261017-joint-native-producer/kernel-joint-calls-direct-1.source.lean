import MicroCFTA.SourceCurrentConstrainedCapKernelJointEffects
import MicroCFTA.SourceCurrentConstrainedCapNativeBinderReturn
import MicroCFTA.SourceCurrentConstrainedCapNativePairWeight

/-!
# Joint laws through actual Mu and original binding calls

The original source supplies the exact numeric pair weight. A body request
can retain that weight. The proof uses the smaller actual execution rather
than strict rank descent. Actual optional-binder readback uses its selected
final record at both zero and positive ranks.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapKernelJoint
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionControl (identity pair)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapNativeOccurrenceCache (OriginalBindings NodeInputs)
open SourceCurrentConstrainedCapPairOccurrences (Classified sourceWeight)
open SourceCurrentConstrainedCapNonplainRank (rank pairRank)
open SourceRecursiveIntersectionResultScope (Scope)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- A capped Mu and its hereditary body have rank zero; other literal bodies retain their rank. -/
theorem body_rank (annotation : Guard → Prop) (depth : Nat) (value : Value Symbol Guard)
    (bounded : Cap annotation depth value) : rank annotation (body value) = rank annotation value := by
  cases value with
  | empty | reference | node | union => rfl
  | mu entry stored probe ordinary =>
      have annotated := SourceCurrentConstrainedCapNativeScope.mu_annotated bounded
      rw [body, SourceCurrentConstrainedCapNonplainRank.rank_zero annotation _
        (SourceCurrentHereditaryNativeScope.body_annotated annotation _ annotated),
        SourceCurrentConstrainedCapNonplainRank.rank_zero annotation _ annotated]

/-- Actual Mu entry and selected-winner cleanup derive all three laws from the smaller body request. -/
theorem mu_joint (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls annotation source call) (depth : Nat) (domain : Interned DomainKey)
    (left right : Value Symbol Guard) (state : Machine Symbol Guard) (context : Context annotation source state)
    (known : Domain state domain) (bindings : OriginalBindings annotation source domain.key)
    (inputs : NodeInputs source ⟨domain, left, right⟩) (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right) :
    Checked annotation source (mu call domain left right state)
      (fun after value => Available after.heap value ∧ Cap annotation depth value ∧
        Classified (sourceWeight annotation source) (pairRank annotation left right) value ∧ Scope domain.key.seen value) := by
  cases first : identity left <;> cases second : identity right <;> simp only [mu, first, second]
  all_goals try exact failed annotation source state _ _
  rename_i firstId secondId
  let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right firstId secondId
  let entered : Machine Symbol Guard := {state with domains := actual.2}
  have leftAvailable := inputs.2.2.1.grows source state.heap context.growth context.history
  have rightAvailable := inputs.2.2.2.1.grows source state.heap context.growth context.history
  obtain ⟨enteredValid, _extension, enteredDomain⟩ := SourceRecursiveIntersectionKernel.entered state context.valid domain known
    left right leftAvailable rightAvailable firstId secondId
  have enteredContext : Context annotation source entered :=
    ⟨enteredValid, context.semantic, context.guards, context.growth, context.history⟩
  have enteredBindings := SourceCurrentConstrainedCapOriginalSupport.enter annotation depth source domain bindings left right inputs
    leftCap rightCap state.domains context.valid.2 firstId secondId
  have key : actual.1.key = SourceRecursiveIntersectionDomain.extend domain.key
      ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst) (pair firstId secondId) :=
    SourceRecursiveIntersectionSchedule.entered_key state.domains context.valid.2 domain.key left right firstId secondId
  have leftBody := SourceCurrentConstrainedCapOriginalSupport.body_input source left inputs.1 inputs.2.2.1
  have rightBody := SourceCurrentConstrainedCapOriginalSupport.body_input source right inputs.2.1 inputs.2.2.2.1
  have bodyInputs : NodeInputs source ⟨actual.1, body left, body right⟩ := by
    refine ⟨leftBody.1, rightBody.1, leftBody.2, rightBody.2, ?_, ?_⟩
    · rw [key]
      exact SourceCurrentConstrainedCapNativeCoverage.left_body_covered domain.key left right inputs.2.2.2.2.1 _
    · rw [key]
      exact SourceCurrentConstrainedCapNativeCoverage.right_body_covered domain.key left right inputs.2.2.2.2.2 _
  have leftBound := SourceCurrentConstrainedCapNativeScope.body_cap annotation depth left leftCap
  have rightBound := SourceCurrentConstrainedCapNativeScope.body_cap annotation depth right rightCap
  have bodyRank : pairRank annotation (body left) (body right) = pairRank annotation left right := by
    simp only [pairRank, body_rank annotation depth left leftCap, body_rank annotation depth right rightCap]
  have oldWeight := SourceCurrentConstrainedCapNativePairWeight.pair_weight annotation source facts domain.key bindings.annotated
    left right inputs.2.2.1 inputs.2.2.2.1 inputs.2.2.2.2.1 inputs.2.2.2.2.2 firstId secondId first second
  apply bind annotation source _ _ _ _
    (calls depth actual.1 (body left) (body right) entered enteredContext enteredDomain enteredBindings bodyInputs leftBound rightBound)
  intro value middle called middleContext returned
  have bodyScope : Scope (pair firstId secondId :: domain.key.seen) value := by
    apply SourceRecursiveIntersectionResultScope.weaken actual.1.key.seen _ ?_ value returned.2.2.2
    intro next member
    rw [key] at member
    rcases (SourceRecursiveIntersectionDomain.extend_seen _ _ _ next).mp member with same | old
    · exact List.mem_cons.mpr (.inl same)
    · exact List.mem_cons.mpr (.inr old)
  have fresh := SourceCurrentConstrainedCapNativeProbeSupport.of_scope _ value bodyScope
  have classified : Classified (sourceWeight annotation source) (pairRank annotation left right) value := by
    simpa only [bodyRank] using returned.2.2.1
  intro result after completed
  cases outcome : SourceRecursiveIntersectionMaybeMu.maybeMu (pair firstId secondId) value middle.heap with
  | pending key heap => simp only [construction, outcome] at completed; cases completed
  | done result heap =>
      simp only [construction, outcome] at completed
      cases completed
      have selected : Cap annotation depth result ∧
          Classified (sourceWeight annotation source) (pairRank annotation left right) result ∧
          SourceCurrentConstrainedCapGuardHeap.Heap annotation heap ∧
          SourceCurrentHereditaryConstruction.MuStored annotation heap ∧ Available heap result ∧
          SourceRecursiveIntersectionSemanticHeap.SemanticHeap heap ∧ Grows middle.heap heap ∧
          Extends middle.heap.nodes.issued heap.nodes.issued ∧ SourceCurrentConstrainedCapNativeProbeSupport.ProbeFree result := by
        by_cases zero : pairRank annotation left right = 0
        · have leftZero : rank annotation left = 0 := by unfold pairRank at zero; omega
          have rightZero : rank annotation right = 0 := by unfold pairRank at zero; omega
          have leftPlain := (SourceCurrentConstrainedCapNonplainRank.rank_zero_iff annotation left).mp leftZero
          have rightPlain := (SourceCurrentConstrainedCapNonplainRank.rank_zero_iff annotation right).mp rightZero
          have zeroCall := calls 0 actual.1 (body left) (body right) entered enteredContext enteredDomain enteredBindings bodyInputs
            (SourceCurrentConstrainedCapNativeScope.body_cap annotation 0 left (.plain 0 leftPlain))
            (SourceCurrentConstrainedCapNativeScope.body_cap annotation 0 right (.plain 0 rightPlain))
          have plain := ((zeroCall value middle called).2.2.1).annotated rfl
          have selected := SourceCurrentConstrainedCapNativeBinderReturn.zero annotation depth _ value middle.heap middleContext.semantic
            returned.1 plain middleContext.guards (sourceWeight annotation source) (by simpa only [zero] using classified)
            fresh result heap outcome
          simpa only [zero] using selected
        · exact SourceCurrentConstrainedCapNativeBinderReturn.positive annotation depth _ value middle.heap middleContext.semantic
            returned.1 returned.2.1 middleContext.guards (sourceWeight annotation source) _ (by omega) oldWeight classified fresh result heap outcome
      have finalContext : Context annotation source {middle with heap := heap} :=
        ⟨⟨selected.2.2.2.2.2.1.1.normal.facts, middleContext.valid.2⟩, selected.2.2.2.2.2.1,
          selected.2.2.1, grows_trans middleContext.growth selected.2.2.2.2.2.2.1,
          extends_trans middleContext.history selected.2.2.2.2.2.2.2.1⟩
      have scope := SourceRecursiveIntersectionResultScope.optionalBinder domain.key.seen (pair firstId secondId)
        value middle.heap middleContext.semantic.1 returned.1 bodyScope result heap outcome
      exact ⟨finalContext, selected.2.2.2.2.1, selected.1, selected.2.1, scope⟩

end MicroCFTA.SourceCurrentConstrainedCapKernelJoint
