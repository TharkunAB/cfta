import MicroCFTA.SourceEqualityNativeDemandAcceptedReceipt
import MicroCFTA.SourceEqualityNativeDemandNodeCalls

/-!
# Accepted checked edges with a fresh self child call

Singleton original child lists determine one actual native request. Source
self tests and fresh publication derive its complete child receipt. The
accepted prefix and final constructor then derive the parent body receipt.
No recursive child receipt or future validity is supplied as a premise.
-/
namespace MicroCFTA.SourceEqualityNativeDemandAcceptedSelfChild
open Language Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode SourceRecursiveIntersectionControl
open SourceEqualityNativeDemand SourceEqualityNativeDemandProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Actual source self-child calls discharge the accepted parent's child receipt and give exact finite body completion. -/
theorem body_produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (first second combined : Allocated) (leftChild rightChild : Value Symbol Guard)
    (nativeValid : SourceEqualityNativeDemandProvenance.Valid (SourceEqualityPCSGuard.holds formulas solver) state.native)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (heapReady : SourceEqualityRequiredCache.Ready state.native.machine.heap) (inputs : EdgeReady state.native.machine request)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (leftChildren : request.left.children = [leftChild]) (rightChildren : request.right.children = [rightChild])
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (accepted : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok (.ready combined))
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain leftChild rightChild)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain leftChild rightChild = some key)
    (missing : state.native.nodes.table key = none)
    (nonempty : hasEmpty leftChild rightChild = false) (noReset : reset request.domain.key leftChild rightChild = false)
    (same : closedSelf leftChild rightChild = true) :
    ∃ result final, execute 5 (.edgeBody request .pure) state = .done result final ∧
      EdgeProduced (width := width) (SourceEqualityPCSGuard.holds formulas solver) final.native.machine request result ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap final.native.machine.heap ∧
      EdgeResident final.native.machine.heap result ∧ result.children = [leftChild] ∧
      final.operations = (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
        request.left.children.length request.right.children.length state.operations).2 := by
  let checked := SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
    request.left.children.length request.right.children.length state.operations
  let childState : SourceEqualityNativeDemand.State width := {state with operations := checked.2}
  let childRequest : NodeRequest Symbol Guard := ⟨request.domain, leftChild, rightChild⟩
  have arity : request.left.children.length = request.right.children.length := by simp only [leftChildren, rightChildren, List.length_singleton]
  have leftAvailable : Available state.native.machine.heap leftChild :=
    nativeValid.machine.1.cached.edges request.left.entry.key request.left inputs.2.1 leftChild (by rw [leftChildren]; simp)
  have rightAvailable : Available state.native.machine.heap rightChild :=
    nativeValid.machine.1.cached.edges request.right.entry.key request.right inputs.2.2 rightChild (by rw [rightChildren]; simp)
  have childReady : NodeReady childState.native.machine childRequest := ⟨inputs.1, leftAvailable, rightAvailable⟩
  obtain ⟨after, singleton, _, _, operations⟩ := SourceEqualityNativeDemandNodeCalls.self_miss_walk
    (SourceEqualityPCSGuard.holds formulas solver) childRequest childState nativeValid childReady heapReady safe key requested missing nonempty noReset same
  have walked : SourceEqualityNativeDemandChildWalk.Walk (SourceEqualityPCSGuard.holds formulas solver) request.domain
      (request.left.children.zip request.right.children) childState [leftChild] after 2 := by
    simpa only [leftChildren, rightChildren, List.zip_cons_cons, List.zip_nil_left] using singleton
  have parent := SourceEqualityNativeDemandAcceptedReceipt.body_produced formulas solver request state after first second combined
    [leftChild] 2 operationsValid heapReady inputs leftCached rightCached arity symbols left right accepted walked
  exact ⟨_, _, parent.1, parent.2.1, parent.2.2.1, parent.2.2.2.1, parent.2.2.2.2.1, operations⟩

end MicroCFTA.SourceEqualityNativeDemandAcceptedSelfChild
