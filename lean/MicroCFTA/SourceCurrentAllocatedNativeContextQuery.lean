import MicroCFTA.SourceCurrentAllocatedNativeContextExecution
import MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts
import MicroCFTA.SourceCurrentAllocatedQueryMemo

/-!
# Contextual meaning of actual completed checked queries

Actual call readback selects a ready cell or the original started handle.
The contextual cache supplies its law for that literal result request.
Initial contextual validity and local executed finish laws derive the
returned invariant. No final native-validity premise is needed.
General query completion and recursive finish-law construction remain open.
For a started query, its finish plan includes the root result law itself.
These endpoints transfer that law. The body induction must derive it.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeContextQuery
open Language InternedConstructorTemplates
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceCurrentAllocatedNativeContextCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

variable (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
  (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)

/-- Actual completed call readback recovers its exact request law from the retained cells. -/
theorem call_law [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (before after : Checked width) (result : Value Symbol Guard) (steps : Nat)
    (call : SourceEqualityNativeDemandNodeReadback.Call request before result after steps)
    (physical : SourceEqualityNativeDemandProvenance.Valid holds before.native)
    (initial : Contextual view model ranked holds before.native)
    (ready : NodeReady before.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (final : Contextual view model ranked holds after.native) :
    NodeLaw view model ranked holds request result := by
  cases call with
  | direct fuel after value unresolved body =>
      obtain ⟨key, actual⟩ := SourceCurrentAllocatedQueryMemo.key_exists request safe
      rw [unresolved] at actual
      cases actual
  | ready key handle original value requested published returned =>
      exact (node_ready_contextual view model ranked holds before.native physical initial request original ready
        key ⟨requested, safe⟩ handle published result returned).2.2
  | started fuel handle chosen running actual middle value selected demanded suspended evaluating machine body =>
      have same := SourceEqualityNativeDemandRequestExact.node_started holds request actual before.native chosen running
        handle physical ready safe selected demanded
      subst actual
      have chosenShape := SourceRecursiveIntersectionNative.lookupNode_shape request before.native physical.shape
      simp only [selected] at chosenShape
      have runningShape := SourceRecursiveIntersectionNative.demandNode_shape handle chosen chosenShape
      simp only [demanded] at runningShape
      have retained := SourceEqualityNativeDemandRunning.trace_retains fuel (.code (compileNode request))
        (⟨running, before.operations⟩ : Checked width) middle result body
        (SourceRecursiveIntersectionCode.compileNode_bodyCode request) runningShape
      have present := retained.2.1 handle request evaluating
      have returned : (finishNode handle result middle.native).nodes.cells handle = some ⟨request, .returned result⟩ := by
        simp only [finishNode, FlatMemoThunk.finish, present, FlatMemoThunk.setStatus, Cache.put, ↓reduceIte]
      exact final.nodes handle request result returned

/-- A completed query transfers its reached finish laws, including its own root completion law. -/
theorem query_law_of_finish_laws [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (before after : Checked width) (result : Value Symbol Guard) (fuel : Nat)
    (physical : SourceEqualityNativeDemandProvenance.Valid holds before.native)
    (initial : Contextual view model ranked holds before.native)
    (ready : NodeReady before.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (localLaws : SourceCurrentAllocatedNativeContextExecution.FinishThrough view model ranked holds fuel
      (.code (requestNode request.domain request.left request.right)) before)
    (done : execute fuel (.code (requestNode request.domain request.left request.right)) before = .done result after) :
    NodeLaw view model ranked holds request result ∧ Contextual view model ranked holds after.native := by
  have final := SourceCurrentAllocatedNativeContextExecution.done_contextual view model ranked holds fuel _ before after result
    initial localLaws done
  obtain ⟨steps, _, call⟩ := SourceEqualityNativeDemandNodeReadback.of_done fuel request before after result done
  exact ⟨call_law view model ranked holds request before after result steps call physical initial ready safe final, final⟩

/-- Rank erasure gives empty-domain exactness after the root finish law has been established. -/
theorem query_exact_of_finish_laws [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (before after : Checked width) (result : Value Symbol Guard) (fuel : Nat)
    (physical : SourceEqualityNativeDemandProvenance.Valid holds before.native)
    (initial : Contextual view model ranked holds before.native)
    (ready : NodeReady before.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (localLaws : SourceCurrentAllocatedNativeContextExecution.FinishThrough view model ranked holds fuel
      (.code (requestNode request.domain request.left request.right)) before)
    (done : execute fuel (.code (requestNode request.domain request.left request.right)) before = .done result after)
    (inputs : NodeInputs view model request)
    (finite : ∀ name term, model.languages name term ↔ ∃ rank, ranked.languages name rank term)
    (domain : request.domain = IntersectionEmptyDomain.emptyDomain)
    (output : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    InternedGuardedLanguage.meaning holds output result term ↔
      IntersectSchedule.inputLanguage model.languages (SourceRecursiveIntersectionInputView.inputOf request.left) term ∧
      IntersectSchedule.inputLanguage model.languages (SourceRecursiveIntersectionInputView.inputOf request.right) term := by
  have law := (query_law_of_finish_laws view model ranked holds request before after result fuel physical initial ready safe localLaws done).1
  exact SourceCurrentAllocatedNativeClosedReceipts.node_closed_exact view model ranked holds finite request result inputs law
    domain output term

end MicroCFTA.SourceCurrentAllocatedNativeContextQuery
