import MicroCFTA.SourceCurrentAllocatedNativeActualPrefixReturnedInduction
import MicroCFTA.SourceCurrentAllocatedNativeSamePrefixKeyedChildResult
import MicroCFTA.SourceCurrentAllocatedNativeSamePrefixEdgeChildResult
import MicroCFTA.SourceCurrentAllocatedNativeClosedResetProfile
import MicroCFTA.SourceSynthesisCurrentUniverseBodyChildClassification
import MicroCFTA.SourceCurrentAllocatedNativeNodeQueryDispatchOrigin
import MicroCFTA.SourceCurrentAllocatedNativeBodyFirstOuterQueryGlobalLaws
import MicroCFTA.SourceCurrentAllocatedNativeDiagonalOuterQueryGlobalLaws

/-!
# General closed and original mixed laws on one actual native history

The entry witness retains the actual operand order. The witness retains
both components of the canonical allocation. Each mixed request keeps its
full original pattern and its original height bound.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistory
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniversePrefixHeight (height)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- Closed requests use the empty domain or a domain that resets closed inputs. -/
def ClosedQualified (sourceName : Nat) (request : NodeRequest Symbol Guard) : Prop :=
  Profile sourceName request.left ∧ Profile sourceName request.right ∧
    (request.domain = IntersectionEmptyDomain.emptyDomain ∨ request.domain.key.free.isEmpty = false)

/-- One checked entry belongs to the fixed initial-query history. -/
def AuthenticEntry
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (pattern : Value Symbol Guard) (patternId : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) : Prop :=
  pattern.free = [] ∧ SourceRecursiveIntersectionControl.identity pattern = some patternId ∧
    (SourceRecursiveIntersectionControl.tag pattern = 1 ∨ SourceRecursiveIntersectionControl.tag pattern = 3) ∧
    ∃ (universeFirst : Bool) (used : Nat) (before : Checked width)
      (next : Interned IntersectionFlatMemoKeyDomain.DomainKey → Code Symbol Guard (Value Symbol Guard)),
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let left := if universeFirst then universeValue else pattern
      let right := if universeFirst then pattern else universeValue
      let first := if universeFirst then entry.identity else patternId
      let second := if universeFirst then patternId else entry.identity
      let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
        IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
      let started : Checked width :=
        {before with native := advance before.native {before.native.machine with domains := entered.2}}
      used + 1 ≤ wholeCount ∧
        Trace used (.code (.node rootRequest .pure))
          (⟨initial width machine, operations⟩ : Checked width)
          (.code (.enter IntersectionEmptyDomain.emptyDomain left right first second next)) before ∧
        SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
          IntersectionEmptyDomain.emptyKey left right first second = entered ∧
        Trace 1 (.code (.enter IntersectionEmptyDomain.emptyDomain left right first second next)) before
          (.code (next entered.1)) started ∧ domain = entered.1

/-- Mixed requests retain the full original pattern, both orders, and original height. -/
def MixedQualified
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (request : NodeRequest Symbol Guard) : Prop :=
  ∃ (pattern : Value Symbol Guard) (patternId : Nat) (openAlias operand : Value Symbol Guard),
    AuthenticEntry (width := width) rootRequest machine operations wholeCount entry body depth ordinary
      pattern patternId request.domain ∧
    (openAlias = body ∨ openAlias = .reference (.interned entry.identity)) ∧
    Profile entry.identity operand ∧ height operand ≤ height pattern ∧
    (openAlias = .reference (.interned entry.identity) → height operand < height pattern) ∧
    ((request.left = openAlias ∧ request.right = operand) ∨
      (request.left = operand ∧ request.right = openAlias))

/-- A child pair has either the closed qualification or the original mixed qualification. -/
def Qualified
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (request : NodeRequest Symbol Guard) : Prop :=
  ClosedQualified entry.identity request ∨
    MixedQualified (width := width) rootRequest machine operations wholeCount entry body depth ordinary request

/-- The two result clauses retain the original closed and mixed scopes. -/
def NodeResult
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) : Prop :=
  (ClosedQualified entry.identity request → Profile entry.identity value) ∧
    (MixedQualified (width := width) rootRequest machine operations wholeCount entry body depth ordinary request →
      Profile entry.identity value)

/-- Row results use qualifications of the original ordered zipped children. -/
def EdgeResult
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard) : Prop :=
  (∀ pair ∈ request.left.children.zip request.right.children,
    Qualified (width := width) rootRequest machine operations wholeCount entry body depth ordinary
      ⟨request.domain, pair.1, pair.2⟩) →
    ∀ child ∈ row.children, Profile entry.identity child

/-- The internal node law retains pure results and both actual auxiliary evaluation orders. -/
private def AuxiliaryNodeResult
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (bodyId : Nat)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) : Prop :=
  SourceCurrentAllocatedNativePureQueryGlobalLaws.NodeResult request value ∧
    ∀ (pattern : Value Symbol Guard) (patternId : Nat)
      (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
      AuthenticEntry (width := width) rootRequest machine operations wholeCount entry body depth ordinary
        pattern patternId domain →
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let bodyFirst := SourceRecursiveIntersectionDomain.extend domain.key [entry.identity]
        (SourceRecursiveIntersectionControl.pair bodyId entry.identity)
      let diagonalFirst := SourceRecursiveIntersectionDomain.extend domain.key [entry.identity]
        (SourceRecursiveIntersectionControl.pair entry.identity entry.identity)
      let diagonalTerminal := SourceRecursiveIntersectionDomain.extend diagonalFirst [entry.identity]
        (SourceRecursiveIntersectionControl.pair bodyId entry.identity)
      SourceCurrentAllocatedNativeBodyFirstOuterQueryGlobalLaws.NodeResult
        entry.identity bodyId bodyFirst domain.key body universeValue request value ∧
      SourceCurrentAllocatedNativeDiagonalOuterQueryGlobalLaws.NodeResult
        entry.identity diagonalTerminal diagonalFirst domain.key body universeValue request value

/-- The internal row law retains mismatch, top, and body-first reference-row results. -/
private def AuxiliaryEdgeResult
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (bodyId : Nat)
    (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard) : Prop :=
  SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult request row ∧
    ∀ (pattern : Value Symbol Guard) (patternId : Nat)
      (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
      AuthenticEntry (width := width) rootRequest machine operations wholeCount entry body depth ordinary
        pattern patternId domain →
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let bodyFirst := SourceRecursiveIntersectionDomain.extend domain.key [entry.identity]
        (SourceRecursiveIntersectionControl.pair bodyId entry.identity)
      SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
        entry.identity bodyId bodyFirst universeValue request row

private def HistoryNodeResult
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (bodyId : Nat)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) : Prop :=
  NodeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary request value ∧
    AuxiliaryNodeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary bodyId request value

private def HistoryEdgeResult
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (bodyId : Nat)
    (request : EdgeRequest Symbol Guard) (value : EdgeValue Symbol Guard) : Prop :=
  EdgeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary request value ∧
    AuxiliaryEdgeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary bodyId request value

section PrivateSupport

private theorem profile_empty (sourceName : Nat) : Profile sourceName (.empty : Value Symbol Guard) := by
  refine ⟨rfl, ?_⟩
  intro atom member
  simp only [InternedBoundaryAtoms.atoms, List.not_mem_nil] at member

private theorem closed_codec (value : Value Symbol Guard) (closed : value.free = []) :
    ∃ input, IntersectionFlatMemoKey.input value.referenceOf = some input := by
  cases value <;> simp_all [Value.free, Value.referenceOf, IntersectionFlatMemoKey.input]

private theorem key_of_codecs {width : Nat} (request : NodeRequest Symbol Guard)
    (left : ∃ input, IntersectionFlatMemoKey.input request.left.referenceOf = some input)
    (right : ∃ input, IntersectionFlatMemoKey.input request.right.referenceOf = some input) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key := by
  obtain ⟨first, firstInput⟩ := left
  obtain ⟨second, secondInput⟩ := right
  exact ⟨_, IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain _ _
    first second firstInput secondInput⟩

theorem qualified_key
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input)
    (request : NodeRequest Symbol Guard)
    (qualified : Qualified (width := width) rootRequest machine operations wholeCount entry body depth ordinary request) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key := by
  rcases qualified with closed | mixed
  · exact key_of_codecs (width := width) request (closed_codec _ closed.1.1) (closed_codec _ closed.2.1.1)
  · obtain ⟨pattern, patternId, openAlias, operand, _authentic, alias, operandProfile,
      _height, _strict, ordered⟩ := mixed
    have aliasCodec : ∃ input, IntersectionFlatMemoKey.input openAlias.referenceOf = some input := by
      rcases alias with rfl | rfl
      · exact bodyCodec
      · exact ⟨.ref entry.identity, rfl⟩
    have operandCodec := closed_codec _ operandProfile.1
    rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
    · exact key_of_codecs (width := width) request (by rw [left]; exact aliasCodec) (by rw [right]; exact operandCodec)
    · exact key_of_codecs (width := width) request (by rw [left]; exact operandCodec) (by rw [right]; exact aliasCodec)

private theorem empty_result
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (request : NodeRequest Symbol Guard) :
    NodeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary request .empty := by
  exact ⟨fun _ => profile_empty _, fun _ => profile_empty _⟩

private theorem self_result
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (bodyOpen : body.free ≠ []) (request : NodeRequest Symbol Guard)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .self) :
    NodeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary request request.left := by
  constructor
  · intro qualified
    exact qualified.1
  · intro qualified
    have leftClosed := SourceRecursiveIntersectionResultScope.self_closed
      request.domain.key request.left request.right selected
    obtain ⟨pattern, patternId, openAlias, operand, _authentic, alias, operandProfile,
      _height, _strict, ordered⟩ := qualified
    rcases ordered with ⟨left, _right⟩ | ⟨left, _right⟩
    · have aliasClosed : openAlias.free = [] := by rw [← left]; exact leftClosed
      rcases alias with rfl | rfl
      · exact (bodyOpen aliasClosed).elim
      · simp only [Value.free, List.cons_ne_self] at aliasClosed
    · rw [left]
      exact operandProfile

private theorem closed_no_repeated
    (sourceName : Nat) (request : NodeRequest Symbol Guard)
    (qualified : ClosedQualified sourceName request) (key : Nat × Nat)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .repeated key) :
    False := by
  rcases qualified.2.2 with domain | active
  · have seen := SourceRecursiveIntersectionResultScope.repeated_seen
      request.domain.key request.left request.right key selected
    simp only [domain, IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey,
      List.not_mem_nil] at seen
  · have restart : SourceRecursiveIntersectionControl.reset request.domain.key request.left request.right = true := by
      simp only [SourceRecursiveIntersectionControl.reset, qualified.1.1, qualified.2.1.1,
        List.isEmpty_nil, active, Bool.not_false, Bool.and_self]
    cases emptyTest : SourceRecursiveIntersectionControl.hasEmpty request.left request.right with
    | false =>
      simp only [SourceRecursiveIntersectionControl.decision, emptyTest, restart,
        Bool.false_eq_true, ite_false, ite_true] at selected
      cases selected
    | true =>
      simp only [SourceRecursiveIntersectionControl.decision, emptyTest, ite_true] at selected
      cases selected

private theorem failed_body_impossible
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (bodyCount : Nat) (failure : SourceRecursiveIntersectionKernel.Failure)
    (before after : Checked width) (value : Value Symbol Guard)
    (actual : Steps bodyCount (.code (.fail failure)) before (.code (.pure value)) after) : False := by
  cases actual with
  | cons _ _ _ _ _ _ _ one _ => cases one

private theorem closed_forward_at_node_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount fuel finishUsed dispatchUsed bodyCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (beforeBody beforeFinish : Checked width) (resume : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (within : finishUsed ≤ fuel) (total : dispatchUsed + bodyCount = finishUsed)
    (whole : Trace finishUsed (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code (.finishNode handle value (resume value))) beforeFinish)
    (origin : Steps dispatchUsed (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code ((compileNode request).bind (fun result => .finishNode handle result (resume result)))) beforeBody)
    (actual : Steps bodyCount (.code (compileNode request)) beforeBody (.code (.pure value)) beforeFinish)
    (past : Returned (NodeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
      beforeFinish.native.nodes ∧
      Returned (EdgeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
        beforeFinish.native.edges)
    (child : NodeRequest Symbol Guard) (childQualified : ClosedQualified entry.identity child)
    (compiled : compileNode request = requestNode child.domain child.left child.right) :
    Profile entry.identity value := by
  obtain ⟨key, keyed⟩ := key_of_codecs (width := width) child (closed_codec _ childQualified.1.1)
    (closed_codec _ childQualified.2.1.1)
  have childOrigin : Steps dispatchUsed (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code ((requestNode child.domain child.left child.right).bind
        (fun result => .finishNode handle result (resume result)))) beforeBody := by
    simpa only [compiled] using origin
  have childActual : Steps bodyCount (.code (requestNode child.domain child.left child.right))
      beforeBody (.code (.pure value)) beforeFinish := by simpa only [compiled] using actual
  have childLaw := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_node_finish
    (NodeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
    (EdgeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
    rootRequest machine machineValid operations fuel finishUsed dispatchUsed bodyCount handle value
    (resume value) beforeFinish within whole past child key keyed
    (fun result => .finishNode handle result (resume result)) beforeBody beforeFinish value
    (by omega) childOrigin childActual
  exact childLaw.1.1 childQualified

end PrivateSupport

end MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistory
