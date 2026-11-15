import MicroCFTA.SourceCurrentNativeEnterCommonOperand
import MicroCFTA.SourceSynthesisUniverseClosedResetSteps

/-!
# Full original operands at either real native Mu entry order

The actual ordered event allocates the same canonical domain tuple.
The receipt retains the real event and its actual continuation.
The same suffix supplies full operands at its observed reader.
No canonical Code event replaces a reverse event.
-/
namespace MicroCFTA.SourceCurrentNativeOrderedOriginalEntry
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity tag)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceSynthesisUniversePrefixHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey

set_option autoImplicit false

/-- Either real original entry order retains full operands and its canonical allocation at the same reader. -/
theorem ordered_original_entry_common_operands
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} {Output : Type}
    (entry : Interned NodeKey) (body depth ordinary : Node)
    (pattern : Node) (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId)
    (patternKind : tag pattern = 1 ∨ tag pattern = 3) (universeFirst : Bool)
    (next : Interned DomainKey → Code Symbol Guard Output)
    (fuel : Nat) (before reader : Checked width) (rest : Control Output)
    (physical : Physical before.native) :
    let universeValue : Node := .mu entry body depth ordinary
    let left := if universeFirst then universeValue else pattern
    let right := if universeFirst then pattern else universeValue
    let first := if universeFirst then entry.identity else patternId
    let second := if universeFirst then patternId else entry.identity
    let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
      IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
    let started : Checked width :=
      {before with native := advance before.native {before.native.machine with domains := entered.2}}
    Trace (fuel + 1) (.code (.enter IntersectionEmptyDomain.emptyDomain left right first second next))
      before rest reader →
    SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
      IntersectionEmptyDomain.emptyKey left right first second = entered ∧
    SourceEqualityNativeDemand.step
      (.code (.enter IntersectionEmptyDomain.emptyDomain left right first second next)) before =
      .yielded (.code (next entered.1)) started ∧
    Trace 1 (.code (.enter IntersectionEmptyDomain.emptyDomain left right first second next))
      before (.code (next entered.1)) started ∧
    Trace fuel (.code (next entered.1)) started rest reader ∧
    started.native.machine.heap = before.native.machine.heap ∧
    started.native.machine.domains = entered.2 ∧ started.operations = before.operations ∧
    Available before.native.machine.heap universeValue ∧ Available before.native.machine.heap pattern ∧
    Available reader.native.machine.heap universeValue ∧ Available reader.native.machine.heap pattern ∧
    Domain started.native.machine entered.1 ∧ Domain reader.native.machine entered.1 ∧
    entered.1.key = SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey
      [entry.identity] (SourceRecursiveIntersectionControl.pair entry.identity patternId) ∧
    entered.1.key.free.isEmpty = false ∧ Physical reader.native ∧
    Extension before.native.machine reader.native.machine ∧
    (∀ candidate : Node, Available reader.native.machine.heap candidate → candidate.free = [] →
      identity candidate = some patternId → candidate = pattern ∧ height candidate = height pattern) := by
  let universeValue : Node := .mu entry body depth ordinary
  let left := if universeFirst then universeValue else pattern
  let right := if universeFirst then pattern else universeValue
  let first := if universeFirst then entry.identity else patternId
  let second := if universeFirst then patternId else entry.identity
  let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  let started : Checked width :=
    {before with native := advance before.native {before.native.machine with domains := entered.2}}
  dsimp only
  intro actual
  have patternBinder : SourceRecursiveIntersectionEnvironment.binder pattern = [] := by
    cases pattern <;> try rfl
    simp [tag] at patternKind
  have pairReverse : SourceRecursiveIntersectionControl.pair patternId entry.identity =
      SourceRecursiveIntersectionControl.pair entry.identity patternId := by
    simp only [SourceRecursiveIntersectionControl.pair, Nat.min_comm, Nat.max_comm]
  have reverseAllocation : SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
      IntersectionEmptyDomain.emptyKey pattern universeValue patternId entry.identity = entered := by
    change IntersectionEmptyDomain.make before.native.machine.domains
      (SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey
        ((SourceRecursiveIntersectionEnvironment.binder pattern ++
          SourceRecursiveIntersectionEnvironment.binder universeValue).map Prod.fst)
        (SourceRecursiveIntersectionControl.pair patternId entry.identity)) =
      IntersectionEmptyDomain.make before.native.machine.domains
        (SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey
          ((SourceRecursiveIntersectionEnvironment.binder universeValue ++
            SourceRecursiveIntersectionEnvironment.binder pattern).map Prod.fst)
          (SourceRecursiveIntersectionControl.pair entry.identity patternId))
    rw [patternBinder]
    simp only [List.nil_append, List.append_nil, pairReverse]
  have allocatedEq : SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
      IntersectionEmptyDomain.emptyKey left right first second = entered := by
    cases universeFirst with
    | false => exact reverseAllocation
    | true => rfl
  have receipt := SourceCurrentNativeEnterCommonOperand.enter_prefix_common_operands
    IntersectionEmptyDomain.emptyDomain left right first second next fuel before reader rest physical actual
  dsimp only at receipt
  rw [allocatedEq] at receipt
  obtain ⟨one, tail, heapSame, domainsSame, operationsSame, _oldDomain,
    leftBefore, rightBefore, leftReader, rightReader, startedDomain, readerDomain,
    _rawKey, extension, sameClosed⟩ := receipt
  have event : Trace 1 (.code (.enter IntersectionEmptyDomain.emptyDomain left right first second next))
      before (.code (next entered.1)) started := by
    cases actual with
    | cons control state resume current final result count inputs chosen remaining =>
        exact .cons _ _ _ _ _ _ 0 inputs one (.refl _ _)
  have universeBefore : Available before.native.machine.heap universeValue := by
    cases universeFirst with
    | false => exact rightBefore
    | true => exact leftBefore
  have patternBefore : Available before.native.machine.heap pattern := by
    cases universeFirst with
    | false => exact leftBefore
    | true => exact rightBefore
  have universeReader : Available reader.native.machine.heap universeValue := by
    cases universeFirst with
    | false => exact rightReader
    | true => exact leftReader
  have patternReader : Available reader.native.machine.heap pattern := by
    cases universeFirst with
    | false => exact leftReader
    | true => exact rightReader
  have canonicalKey : entered.1.key = SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey
      [entry.identity] (SourceRecursiveIntersectionControl.pair entry.identity patternId) := by
    have originalKey := SourceRecursiveIntersectionSchedule.entered_key before.native.machine.domains
      physical.machine.2 IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
    change entered.1.key = SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey
      ((SourceRecursiveIntersectionEnvironment.binder universeValue ++
        SourceRecursiveIntersectionEnvironment.binder pattern).map Prod.fst)
      (SourceRecursiveIntersectionControl.pair entry.identity patternId) at originalKey
    rw [patternBinder] at originalKey
    simpa only [universeValue, SourceRecursiveIntersectionEnvironment.binder,
      List.append_nil, List.map_cons, List.map_nil] using originalKey
  have nonempty : entered.1.key.free.isEmpty = false :=
    SourceSynthesisUniverseClosedResetSteps.mixed_entry_nonempty_free_map
      before.native.machine.domains physical.machine.2 entry body depth ordinary pattern patternId
  have patternSide : pattern = left ∨ pattern = right := by
    cases universeFirst with
    | false => exact Or.inl rfl
    | true => exact Or.inr rfl
  have readerPhysical := (SourceCurrentNativeEnterCommonOperand.checked_trace_extension actual physical).1
  exact ⟨allocatedEq, one, event, tail, heapSame, domainsSame, operationsSame,
    universeBefore, patternBefore, universeReader, patternReader, startedDomain, readerDomain,
    canonicalKey, nonempty, readerPhysical, extension,
    sameClosed pattern patternSide patternClosed patternId patternIdentity⟩

end MicroCFTA.SourceCurrentNativeOrderedOriginalEntry
