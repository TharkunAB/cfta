import MicroCFTA.SourceNativeGlobalUnfold
import MicroCFTA.SourceQueryUnfoldMemo
import MicroCFTA.SourceEqualityNativeScoped

/-!
# Global tables through completed scoped native requests

Actual native instructions derive the constructor trace and its absence of
global unfolding calls. Actual heap growth then retains coherence of all
three gate tables. The native node and edge tables remain separate.
The proof does not describe delayed Haskell operand producers.
-/
namespace MicroCFTA.SourceNativeGlobalMemos
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityNativeScoped SourceEqualityRequiredSemanticCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- A completed scoped request derives its actual silent constructor trace. -/
theorem scoped_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {target input result : Value Symbol Guard} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : SourceEqualityNativeScoped.Step emptyGuard conjoin target input before result after)
    (memos : EndpointMemoGateTrace.Memos) :
    ∃ events, SourceGlobalUnfold.Runs ⟨before.machine.heap, memos.unfolding⟩
      ⟨after.machine.heap, memos.unfolding⟩ events ∧ SourceGlobalUnfold.NoGlobal events := by
  cases trace with
  | done fuel ranges actual =>
      simpa only [actual, SourceRecursiveIntersectionNative.Outcome.state] using
        SourceNativeGlobalUnfold.execute_receipt emptyGuard conjoin fuel
          (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) before memos.unfolding

/-- Actual scoped execution and its heap effects derive all three coherent final tables. -/
theorem scoped_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {target input result : Value Symbol Guard} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : SourceEqualityNativeScoped.Step emptyGuard conjoin target input before result after)
    (ready : IdleReady emptyGuard conjoin before)
    (targetAvailable : Available before.machine.heap target) (inputAvailable : Available before.machine.heap input)
    (targetClosed : target.free = []) (inputClosed : input.free = [])
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (memos : EndpointMemoGateTrace.Memos) (valid : EndpointMemoGateTrace.Valid before.machine.heap memos) :
    ∃ events, SourceGlobalUnfold.Runs ⟨before.machine.heap, memos.unfolding⟩
      ⟨after.machine.heap, memos.unfolding⟩ events ∧ SourceGlobalUnfold.NoGlobal events ∧
      EndpointMemoGateTrace.Valid after.machine.heap memos := by
  obtain ⟨events, actual, silent⟩ := scoped_receipt trace memos
  have effects := trace.verified ready targetAvailable inputAvailable targetClosed inputClosed holds conjoined
  exact ⟨events, actual, silent, SourceQueryUnfoldMemo.valid_grows before.machine.heap after.machine.heap
    ready.semantic effects.2.1 memos valid⟩

end MicroCFTA.SourceNativeGlobalMemos
