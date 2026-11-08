import MicroCFTA.SourceSynthesisOriginalGuardAlphabet
import MicroCFTA.SourceCurrentNativeGuardTrace

/-!
# Original synthesis guards through actual checked native prefixes

The original mapped build supplies every initial physical guard check.
Actual checked traces derive their own finite guard extension. Every guard
in that extension has an original-literal, Top, or conjunction origin.
The trace, physical checks, and initial heap identity remain explicit.
The result does not bound trace length or make the original alphabet closed.
-/
namespace MicroCFTA.SourceSynthesisNativeGuardOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceEqualityConstraintOrigins (Derived)
open SourceEqualityAnnotationHeap (Heap)
open SourceSynthesisOriginalGuardAlphabet (alphabet)
open SourceCurrentNativeGuardAlphabet (advance step advance_step)
open SourceEqualityNativeDemand (Control)
open SourceRecursiveIntersectionCode (requestNode)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Trace" => SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace
local notation "Good" => SourceCurrentAllocatedNativePhysicalCompletion.Good
local notation "Allocated" => SourceCurrentAllocatedNativeFieldClosure.Fields
local notation "Fields" => SourceCurrentNativeGuardStep.Fields
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

/-- Reuse the actual source conjunction origin relation with the original library alphabet. -/
abbrev Origin (lib : Library) : Guard → Prop := Derived (alphabet lib) top conjoin

private theorem step_derived (lib : Library) (current : List Guard)
    (known : ∀ guard ∈ current, Origin lib guard) (guard : Guard)
    (member : guard ∈ step current) : Origin lib guard := by
  rcases List.mem_append.mp member with earlier | paired
  · rcases List.mem_append.mp earlier with original | unit
    · exact known guard original
    · have same : guard = top := List.mem_singleton.mp unit
      subst guard
      exact Derived.top
  · obtain ⟨first, firstIn, secondMap⟩ := List.mem_flatMap.mp paired
    obtain ⟨second, secondIn, same⟩ := List.mem_map.mp secondMap
    cases same
    exact Derived.conjunction (known first firstIn) (known second secondIn)

/-- Each guard in the actual finite extension has an origin in the original source alphabet. -/
theorem advance_derived (lib : Library) (count : Nat) {guard : Guard}
    (member : guard ∈ advance (alphabet lib) count) : Origin lib guard := by
  induction count generalizing guard with
  | zero => exact Derived.literal member
  | succ count ih =>
      rw [advance_step] at member
      exact step_derived lib _ (fun _ present => ih present) guard member

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual original Label build derives its complete literal guard heap. -/
theorem initial_heap (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Node) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap) :
    Heap (fun guard => guard ∈ alphabet lib) heap := by
  let literal := SourceSynthesisLabelProgramBuildRoles.literal
  have allowed := SourceEqualityConstraintOrigins.allowed (fun guard => guard ∈ alphabet lib)
    (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal expression)
    (SourceSynthesisOriginalGuardAlphabet.mapped_guards literal lib query signed expression accepted)
  have mappedBuilt : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal expression) [] empty = .done value heap := by
    simpa only [literal, SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built
  simpa only [mappedBuilt, InternedNestedConstruction.Outcome.state] using
    SourceEqualityAnnotationConstruction.build (fun guard => guard ∈ alphabet lib)
      (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal expression) allowed [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)

variable [DecidableEq Symbol] {width fuel : Nat}

/-- Every actual checked prefix derives its final guard heap from the original build. -/
theorem trace_heap (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Node) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap)
    {A : Type} {control rest : Control A} {before after : Checked width}
    (initialHeap : before.native.machine.heap = heap)
    (actual : Trace fuel control before rest after) (good : Good before)
    (allocated : Allocated control before) (fields : Fields (alphabet lib) control) :
    Heap (Origin lib) after.native.machine.heap := by
  have known : Heap (fun guard => guard ∈ alphabet lib) before.native.machine.heap := by
    rw [initialHeap]
    exact initial_heap lib query signed expression accepted value heap built
  have final := (SourceCurrentNativeGuardTrace.retained (alphabet lib) actual good allocated known fields).1
  intro key edge stored
  exact advance_derived lib fuel (final key edge stored)

/-- Actual node-query prefixes derive original guard origins with no supplied guard heap. -/
theorem request_heap (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Node) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap)
    {domain : Interned IntersectionFlatMemoKeyDomain.DomainKey} {left right result : Node} {before after : Checked width}
    (initialHeap : before.native.machine.heap = heap)
    (actual : Trace fuel (.code (requestNode domain left right)) before (.code (.pure result)) after)
    (good : Good before) : Heap (Origin lib) after.native.machine.heap :=
  trace_heap lib query signed expression accepted value heap built initialHeap actual good
    (fun _ => True.intro) (fun _ => True.intro)

end MicroCFTA.SourceSynthesisNativeGuardOrigins
