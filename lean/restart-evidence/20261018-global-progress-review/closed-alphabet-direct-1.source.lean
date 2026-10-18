import MicroCFTA.SourceCurrentNativeGuardTrace
import MicroCFTA.SourceEqualityConstraintInventory

/-!
# Fixed finite guard alphabets through actual native prefixes

A finite alphabet closed under source Top and conjunction does not grow
with the trace length. Original normalized literals construct such an
alphabet by retaining the derivable entries of their finite inventory.
These are bounds on own fields. They do not bound inherited payloads,
fresh physical nodes, recursive requests, or the length of execution.
-/
namespace MicroCFTA.SourceCurrentNativeClosedGuardAlphabet
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityNativeDemand
open SourceCurrentNativeGuardStep (Fields)
open SourceEqualityConstraintOrigins (Derived)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Good" => SourceCurrentAllocatedNativePhysicalCompletion.Good
local notation "Allocated" => SourceCurrentAllocatedNativeFieldClosure.Fields
local notation "Trace" => SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace

/-- The alphabet contains every guard emitted from its own members. -/
def Closed (alphabet : List Guard) : Prop :=
  top ∈ alphabet ∧ ∀ first ∈ alphabet, ∀ second ∈ alphabet, conjoin first second ∈ alphabet

/-- One extension of a closed alphabet introduces no new guard. -/
theorem step_subset (alphabet : List Guard) (closed : Closed alphabet) :
    SourceCurrentNativeGuardAlphabet.step alphabet ⊆ alphabet := by
  intro guard member
  rcases List.mem_append.mp member with earlier | combined
  · rcases List.mem_append.mp earlier with initial | singleton
    · exact initial
    · exact (List.mem_singleton.mp singleton) ▸ closed.1
  · obtain ⟨first,firstMember,mapped⟩ := List.mem_flatMap.mp combined
    obtain ⟨second,secondMember,rfl⟩ := List.mem_map.mp mapped
    exact closed.2 first firstMember second secondMember

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A checked physical prefix retains the same closed alphabet at every reached control. -/
theorem retained (alphabet : List Guard) (closed : Closed alphabet)
    {A : Type} {width fuel : Nat} {control rest : Control A}
    {before after : SourceEqualityNativeDemand.State width}
    (trace : Trace fuel control before rest after) (good : Good before)
    (allocated : Allocated control before)
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap)
    (fields : Fields alphabet control) :
    Heap (fun guard => guard ∈ alphabet) after.native.machine.heap ∧ Fields alphabet rest := by
  induction trace with
  | refl => exact ⟨known,fields⟩
  | cons control before middle current rest after count inputs one tail ih =>
      have effects := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control before good inputs allocated
      have currentGood : Good current := by simpa only [one,Outcome.state] using effects.1
      have currentAllocated : Allocated middle current := by
        simpa only [one,SourceCurrentAllocatedNativeFieldClosure.OutcomeFields] using effects.2.2.2.2.2
      have currentKnown : Heap (fun guard => guard ∈ alphabet) current.native.machine.heap := by
        simpa only [one,Outcome.state] using SourceCurrentNativeGuardStep.step_heap alphabet control before good inputs known fields
      have currentFields := SourceCurrentNativeGuardStep.fields_mono (step_subset alphabet closed) middle
        (SourceCurrentNativeGuardStep.yielded_fields alphabet control middle before current good inputs allocated known fields one)
      exact ih currentGood currentAllocated currentKnown currentFields

/-- Retain exactly the derivable entries of the finite original inventory. -/
noncomputable def originalAlphabet (literals : List Guard) : List Guard := by
  classical
  exact (SourceEqualityConstraintInventory.inventory literals).filter
    (fun guard => decide (Derived literals top conjoin guard))

/-- Normalized literals make original alphabet membership equivalent to causal guard derivability. -/
theorem mem_originalAlphabet (literals : List Guard)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (guard : Guard) : guard ∈ originalAlphabet literals ↔ Derived literals top conjoin guard := by
  classical
  simp only [originalAlphabet,List.mem_filter,decide_eq_true_eq]
  exact ⟨And.right,fun derived =>
    ⟨SourceEqualityConstraintInventory.derived_mem_inventory literals normalized guard derived,derived⟩⟩

/-- Initial normalized literals construct a fixed finite alphabet closed under every native conjunction. -/
theorem original_closed (literals : List Guard)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities) :
    Closed (originalAlphabet literals) := by
  refine ⟨(mem_originalAlphabet literals normalized top).mpr .top,?_⟩
  intro first firstMember second secondMember
  exact (mem_originalAlphabet literals normalized _).mpr (.conjunction
    ((mem_originalAlphabet literals normalized first).mp firstMember)
    ((mem_originalAlphabet literals normalized second).mp secondMember))

/-- Original causal annotations supply the actual entry heap in the fixed alphabet. -/
theorem original_heap (literals : List Guard)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (heap : InternedConstructorTemplates.State Symbol Guard)
    (origins : Heap (Derived literals top conjoin) heap) :
    Heap (fun guard => guard ∈ originalAlphabet literals) heap :=
  fun key edge present => (mem_originalAlphabet literals normalized key.constraint).mpr (origins key edge present)

/-- Actual current native prefixes retain a finite original carrier without an instruction-count ceiling. -/
theorem original_retained (literals : List Guard)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    {A : Type} {width fuel : Nat} {control rest : Control A}
    {before after : SourceEqualityNativeDemand.State width}
    (trace : Trace fuel control before rest after) (good : Good before)
    (allocated : Allocated control before)
    (origins : Heap (Derived literals top conjoin) before.native.machine.heap)
    (fields : Fields (originalAlphabet literals) control) :
    Heap (fun guard => guard ∈ originalAlphabet literals) after.native.machine.heap ∧
      Fields (originalAlphabet literals) rest :=
  retained _ (original_closed literals normalized) trace good allocated
    (original_heap literals normalized _ origins) fields

end MicroCFTA.SourceCurrentNativeClosedGuardAlphabet
