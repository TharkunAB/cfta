import MicroCFTA.SourceCurrentAllocatedNativeAuthenticBodyFirstInnerHistories
import MicroCFTA.SourceCurrentAllocatedNativeAuthenticCoherentInnerHistory

namespace MicroCFTA.SourceCurrentAllocatedNativePastEntryInnerPayloadTransport
open Cache InternedConstructorTemplates
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity pair)
open SourceRecursiveIntersectionDomain (extend)
open SourceEqualityNativeDemand
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeGeneralCMHistory (AuthenticEntry)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/-- An actual old producer supplies inner payload laws for every handle with the same key. -/
theorem inner_payloads_of_past_authentic_entry_at_equal_key
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (oldRoot : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel wholeCount : Nat) (readerControl : Control (Value Symbol Guard)) (reader : Checked width)
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width) readerControl reader)
    (fullPattern : Value Symbol Guard) (patternId : Nat)
    (oldDomain newDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntry (width := width) oldRoot machine operations wholeCount
      entry body depth ordinary fullPattern patternId oldDomain)
    (sameKey : newDomain.key = oldDomain.key)
    (inputs : InputsThrough fuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (fields : FieldsThrough fuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (prefixCount : Nat) (prefixControl : Control (Value Symbol Guard)) (current : Checked width)
    (prefixBound : prefixCount ≤ wholeCount)
    (prefixActual : Trace prefixCount (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width) prefixControl current) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let bodyFirst := extend newDomain.key [entry.identity] (pair bodyId entry.identity)
    let diagonalFirst := extend newDomain.key [entry.identity] (pair entry.identity entry.identity)
    let diagonalTerminal := extend diagonalFirst [entry.identity] (pair bodyId entry.identity)
    Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
      entry.identity bodyId bodyFirst body universeValue) current.native.nodes ∧
    Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
      entry.identity bodyId bodyFirst universeValue) current.native.edges ∧
    Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
      entry.identity entry.identity entry.identity diagonalTerminal diagonalFirst body universeValue)
      current.native.nodes ∧
    Returned SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult current.native.edges := by
  have bodyFirst :=
    SourceCurrentAllocatedNativeAuthenticBodyFirstInnerHistories.body_first_inner_histories_at_authentic_prefix
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      bodyId bodyIdentity oldRoot machine machineValid sourceGrowth operations operationsValid
      fuel wholeCount readerControl reader wholeBound wholeActual fullPattern patternId oldDomain authentic
      inputs fields prefixCount prefixControl current prefixBound prefixActual
  have diagonal :=
    SourceCurrentAllocatedNativeAuthenticCoherentInnerHistory.authentic_coherent_inner_returned_at_actual_root_prefix
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      bodyId bodyIdentity oldRoot machine machineValid sourceGrowth operations operationsValid
      fuel wholeCount prefixCount readerControl prefixControl reader current wholeBound wholeActual
      fullPattern patternId oldDomain authentic prefixBound prefixActual inputs fields
  dsimp only
  rw [sameKey]
  exact ⟨bodyFirst.1, bodyFirst.2, diagonal.1, diagonal.2⟩

end MicroCFTA.SourceCurrentAllocatedNativePastEntryInnerPayloadTransport

#print axioms MicroCFTA.SourceCurrentAllocatedNativePastEntryInnerPayloadTransport.inner_payloads_of_past_authentic_entry_at_equal_key
