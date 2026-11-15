import MicroCFTA.SourceCurrentAllocatedNativeActualPrefixReturnedInduction
import MicroCFTA.SourceCurrentAllocatedNativeSamePrefixKeyedChildResult
import MicroCFTA.SourceCurrentAllocatedNativeSamePrefixEdgeChildResult
import MicroCFTA.SourceCurrentAllocatedNativeClosedResetProfile
import MicroCFTA.SourceSynthesisCurrentUniverseGeneratedTypeClosure

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
    AuthenticEntry rootRequest machine operations wholeCount entry body depth ordinary
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
    MixedQualified rootRequest machine operations wholeCount entry body depth ordinary request

/-- The two result clauses retain the original closed and mixed scopes. -/
def NodeResult
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) : Prop :=
  (ClosedQualified entry.identity request → Profile entry.identity value) ∧
    (MixedQualified rootRequest machine operations wholeCount entry body depth ordinary request →
      Profile entry.identity value)

/-- Row results use qualifications of the original ordered zipped children. -/
def EdgeResult
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard) : Prop :=
  (∀ pair ∈ request.left.children.zip request.right.children,
    Qualified rootRequest machine operations wholeCount entry body depth ordinary
      ⟨request.domain, pair.1, pair.2⟩) →
    ∀ child ∈ row.children, Profile entry.identity child

end MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistory
