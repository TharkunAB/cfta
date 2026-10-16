import MicroCFTA.SourceCurrentAllocatedNativeDomainTrace

namespace MicroCFTA.DomainTraceIndependentKernels

open Cache InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionKernel IntersectionFlatMemoKeyDomain SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private def key : DomainKey := SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey []
  (SourceRecursiveIntersectionControl.pair 0 1)

private def entered (before : Checked width) : Checked width :=
  {before with native := advance before.native {before.native.machine with domains :=
    (IntersectionEmptyDomain.make before.native.machine.domains key).2}}

private def worked (job : Work Symbol Guard Unit) (before : Checked width) : Checked width :=
  {before with native := advance before.native {before.native.machine with heap :=
    (InternedConstructorTemplates.run job before.native.machine.heap).2}}

private def workCode (job : Work Symbol Guard Unit) : Code Symbol Guard Unit := .work job .pure
private def readCode (job : Work Symbol Guard Unit) : Code Symbol Guard Unit := .read 0 (fun _ => workCode job)
private def secondCode (job : Work Symbol Guard Unit) : Code Symbol Guard Unit :=
  .enter IntersectionEmptyDomain.emptyDomain .empty .empty 0 1 (fun _ => readCode job)
private def program (job : Work Symbol Guard Unit) : Code Symbol Guard Unit :=
  .enter IntersectionEmptyDomain.emptyDomain .empty .empty 0 1 (fun _ => secondCode job)

private theorem make_again (state : Cache.State DomainKey) (valid : Cache.Valid state) :
    IntersectionEmptyDomain.make (IntersectionEmptyDomain.make state key).2 key =
      IntersectionEmptyDomain.make state key := by
  by_cases empty : key = IntersectionEmptyDomain.emptyKey
  · simp [IntersectionEmptyDomain.make, empty]
  · simp only [IntersectionEmptyDomain.make, empty, ↓reduceIte]
    rw [Cache.intern_idempotent state key valid]

private theorem entered_again (before : Checked width) (valid : Cache.Valid before.native.machine.domains) :
    entered (entered before) = entered before := by
  simp only [entered, advance]
  rw [make_again _ valid]

private theorem prefix_cons {inventory : List DomainKey} {control next : Control Unit}
    {before after : Checked width} (current : SourceCurrentAllocatedNativeDomainTrace.Entered inventory control)
    (one : SourceEqualityNativeDemand.step control before = .yielded next after)
    (tail : SourceCurrentAllocatedNativeDomainTrace.Prefixes inventory next after) : SourceCurrentAllocatedNativeDomainTrace.Prefixes inventory control before := by
  intro fuel final result actual
  cases actual with
  | refl => exact current
  | cons control before middle state final result fuel first rest =>
    have same := Outcome.yielded.inj (first.symm.trans one)
    rcases same.1 with rfl
    rcases same.2 with rfl
    exact tail fuel final result rest

private theorem pure_prefix (inventory : List DomainKey) (before : Checked width) :
    SourceCurrentAllocatedNativeDomainTrace.Prefixes inventory (.code (.pure ())) before := by
  intro fuel final result actual
  cases actual with
  | refl => trivial
  | cons control before middle state final result fuel first rest =>
    simp [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, lift] at first

/-- Two actual enters allocate one domain, then arbitrary constructor work leaves its cache unchanged. -/
theorem repeated_enter_read_work (before : Checked width) (job : Work Symbol Guard Unit)
    (valid : Cache.Valid before.native.machine.domains) :
    let after := worked job (entered before)
    Steps 4 (.code (program job)) before (.code (.pure ())) after ∧
      SourceCurrentAllocatedNativeDomainTrace.Prefixes [key] (.code (program job)) before ∧
      SourceRecursiveIntersectionDomainAllocation.Trace [key]
        before.native.machine.domains after.native.machine.domains ∧
      after.native.machine.domains = (entered before).native.machine.domains ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + 1 ∧
      after.operations = before.operations ∧ after.native.nodes = before.native.nodes ∧
      after.native.edges = before.native.edges := by
  dsimp only
  have first : SourceEqualityNativeDemand.step (.code (program job)) before =
      .yielded (.code (secondCode job)) (entered before) := rfl
  have second : SourceEqualityNativeDemand.step (.code (secondCode job)) (entered before) =
      .yielded (.code (readCode job)) (entered before) := by
    change Outcome.yielded (.code (readCode job)) (entered (entered before)) = _
    rw [entered_again before valid]
  have read : SourceEqualityNativeDemand.step (.code (readCode job)) (entered before) =
      .yielded (.code (workCode job)) (entered before) := rfl
  have work : SourceEqualityNativeDemand.step (.code (workCode job)) (entered before) =
      .yielded (.code (.pure ())) (worked job (entered before)) := rfl
  have actual : Steps 4 (.code (program job)) before (.code (.pure ())) (worked job (entered before)) :=
    .cons _ _ _ _ _ _ _ first (.cons _ _ _ _ _ _ _ second
      (.cons _ _ _ _ _ _ _ read (.cons _ _ _ _ _ _ _ work (.refl _ _))))
  have admitted : SourceCurrentAllocatedNativeDomainTrace.Prefixes [key] (.code (program job)) before :=
    prefix_cons (by simp [SourceCurrentAllocatedNativeDomainTrace.Entered, SourceCurrentAllocatedNativeDomainTrace.CodeEntered, program, key,
      SourceRecursiveIntersectionEnvironment.bindings, SourceRecursiveIntersectionEnvironment.binder,
      IntersectionEmptyDomain.emptyDomain]) first
      (prefix_cons (by simp [SourceCurrentAllocatedNativeDomainTrace.Entered, SourceCurrentAllocatedNativeDomainTrace.CodeEntered, secondCode, key,
        SourceRecursiveIntersectionEnvironment.bindings, SourceRecursiveIntersectionEnvironment.binder,
        IntersectionEmptyDomain.emptyDomain]) second
        (prefix_cons trivial read (prefix_cons trivial work (pure_prefix [key] _))))
  have history := SourceCurrentAllocatedNativeDomainTrace.trace [key] 4 _ _ _ _ actual admitted
  have bounded := SourceCurrentAllocatedNativeDomainTrace.next_le [key] 4 _ _ _ _ actual admitted
  exact ⟨actual, admitted, history, rfl, by simpa using bounded, rfl, rfl, rfl⟩

/-- The same raw prefix gives a strict shifted-domain bound, independently of constructor work size. -/
theorem repeated_enter_shifted_word (before : Checked width) (job : Work Symbol Guard Unit)
    (valid : Cache.Valid before.native.machine.domains) (limit : Nat)
    (room : before.native.machine.domains.next + 1 < limit) :
    (IntersectionEmptyDomain.make before.native.machine.domains key).1.identity < limit := by
  obtain ⟨actual, admitted, history, same, bounded, operations, nodes, edges⟩ :=
    repeated_enter_read_work before job valid
  have represented := (IntersectionEmptyDomain.make_correct before.native.machine.domains valid key).2
  have retained : IntersectionEmptyDomain.Represents
      (worked job (entered before)).native.machine.domains key
      (IntersectionEmptyDomain.make before.native.machine.domains key).1 := by
    simpa [worked, entered, advance] using represented
  exact SourceCurrentAllocatedNativeDomainTrace.identity_lt [key] 4 _ _ _ _ actual admitted valid key _ retained limit (by simpa using room)

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms repeated_enter_read_work
#check @repeated_enter_read_work
#print axioms repeated_enter_shifted_word
#check @repeated_enter_shifted_word

end MicroCFTA.DomainTraceIndependentKernels
