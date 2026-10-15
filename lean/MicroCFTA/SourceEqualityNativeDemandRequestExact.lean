import MicroCFTA.SourceEqualityNativeDemandCellValidity
import MicroCFTA.SourceRecursiveIntersectionNativeObservations
import MicroCFTA.SourceRecursiveIntersectionNativeShape

/-!
# Original requests at actual checked native starts

Current checked tables retain original available inputs and actual key
bounds. These facts identify the complete request selected for evaluation.
The proof derives lookup validity from the current state. It assumes no
future validity, body result, or completed-call receipt.
-/
namespace MicroCFTA.SourceEqualityNativeDemandRequestExact
open InternedConstructorTemplates SourceRecursiveIntersectionThunks SourceRecursiveIntersectionKernel
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State

/-- An actual started node request equals the current candidate under checked original keys and inputs. -/
theorem node_started [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (request actual : NodeRequest Symbol Guard)
    (before chosen running : Native width Symbol Guard) (handle : Nat)
    (valid : SourceEqualityNativeDemandProvenance.Valid holds before) (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.evaluate actual, running)) : actual = request := by
  have chosenValid := SourceEqualityNativeDemandProvenance.lookupNode_valid before valid request ready safe
  simp only [selected] at chosenValid
  obtain ⟨key, requested, published, sameMachine⟩ :=
    SourceRecursiveIntersectionNative.lookupNode_memoized request before chosen handle selected
  have chosenReady : NodeReady chosen.machine request := by rw [sameMachine]; exact ready
  have suspended := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running actual demanded).1
  exact SourceEqualityNativeDemandProvenance.node_request_exact chosen chosenValid request chosenReady key
    ⟨requested, safe⟩ handle published ⟨actual, .suspended⟩ suspended

/-- An actual started edge request equals the complete current ordered row pair under checked keys and inputs. -/
theorem edge_started [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (request actual : EdgeRequest Symbol Guard)
    (before chosen running : Native width Symbol Guard) (handle : Nat)
    (valid : SourceEqualityNativeDemandProvenance.Valid holds before) (ready : EdgeReady before.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before = (handle, chosen))
    (demanded : demandEdge handle chosen = (.evaluate actual, running)) : actual = request := by
  have chosenValid := SourceEqualityNativeDemandProvenance.lookupEdge_valid before valid request ready safe
  simp only [selected] at chosenValid
  obtain ⟨published, sameMachine⟩ :=
    SourceRecursiveIntersectionNative.lookupEdge_selected request before chosen handle selected
  have chosenReady : EdgeReady chosen.machine request := by rw [sameMachine]; exact ready
  have suspended := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running actual demanded).1
  exact SourceEqualityNativeDemandProvenance.edge_request_exact chosen chosenValid request chosenReady _
    ⟨rfl, safe⟩ handle published ⟨actual, .suspended⟩ suspended

end MicroCFTA.SourceEqualityNativeDemandRequestExact
