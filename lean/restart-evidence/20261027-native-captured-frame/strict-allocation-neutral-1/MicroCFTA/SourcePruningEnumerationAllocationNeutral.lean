import MicroCFTA.SourcePruningEnumerationShallowChildLanguage
import MicroCFTA.SourcePruningEnumerationSelectedEdgeFinishLanguage
import MicroCFTA.EnumerationFrame

/-!
# Fresh slots and residuals with a neutral captured payload

Fresh allocation does not inspect an older captured payload.
Its semantic restriction remains exact after neutralization.
The selected residual write retains the same filled-fragment predicate.
-/
namespace MicroCFTA.SourcePruningEnumerationShallowChild
open Language Fragments EnumerationState EnumerationCorrectness EnumerationFrame
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard : Type}

/-- Fresh native allocation adds its domain while retaining the neutral captured payload. -/
theorem allocation_neutral_semantics
    (held : Nat) (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (before : State Symbol EnumGuard) (node : Option Nat)
    (inside : held < before.values.length) (aligned : before.counter = before.values.length) :
    Satisfies language meaning assignment (neutralize held (allocated node before)) ↔
      Satisfies language meaning assignment (neutralize held before) ∧
        permits (node.map language) (assignment before.counter) := by
  rw [neutralize_allocated held node before inside]
  exact allocation_semantics language meaning assignment node (neutralize held before)
    (by simpa only [neutralize, List.length_set] using aligned)

/-- A fresh stored bucket retains exactly its domain and inherited constraints after neutralization. -/
theorem allocation_bucket_neutral_semantics
    (held : Nat) (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (before : State Symbol EnumGuard)
    (handle : Nat) (scs : List Suspended)
    (inside : held < before.values.length) (aligned : before.counter = before.values.length) :
    Satisfies language meaning assignment (neutralize held
      {allocated (some handle) before with values :=
        (allocated (some handle) before).values.set before.counter (.unenumerated (some handle) scs)}) ↔
      Satisfies language meaning assignment (neutralize held before) ∧
        language handle (assignment before.counter) ∧
        ∀ sc ∈ scs, Suspended.Holds assignment (assignment before.counter) sc := by
  have different : before.counter ≠ held := by omega
  rw [neutralize_set held before.counter (allocated (some handle) before) _ different,
    neutralize_allocated held (some handle) before inside]
  exact allocation_bucket_semantics language meaning assignment (neutralize held before) handle scs
    (by simpa only [neutralize, List.length_set] using aligned)

/-- Fresh own-class suspension adds no assignment restriction even with a neutral captured payload. -/
theorem suspension_neutral_semantics
    (held count : Nat) (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (before : State Symbol EnumGuard)
    (inside : held < before.values.length) (aligned : before.counter = before.values.length) :
    Satisfies language meaning assignment (neutralize held (suspendedState count before)) ↔
      Satisfies language meaning assignment (neutralize held before) := by
  rw [neutralize_suspended held count before inside]
  exact suspendMany_semantics language meaning assignment count (neutralize held before)
    (by simpa only [neutralize, List.length_set] using aligned)

end MicroCFTA.SourcePruningEnumerationShallowChild

namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open Language EnumerationState EnumerationCorrectness EnumerationFrame
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol

/-- The actual residual write adds its complete predicate with the captured payload neutralized. -/
theorem finish_neutral_semantics
    (held : Nat) (residual : Option Constraint) (fragment : Fragment) (before : Cached)
    (language : NodeLanguage Symbol) (meaning : Constraint → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) :
    Satisfies language meaning assignment (neutralize held (finish residual fragment before).core) ↔
      Satisfies language meaning assignment (neutralize held before.core) ∧
        ResidualHolds meaning residual (Fragments.fill assignment fragment) := by
  have same : neutralize held (finish residual fragment before).core =
      (finish residual fragment (EnumerationExpandableIndex.frame (neutralize held before.core) before)).core := by
    cases residual <;> rfl
  rw [same]
  exact finish_semantics residual fragment
    (EnumerationExpandableIndex.frame (neutralize held before.core) before) language meaning assignment

end MicroCFTA.SourcePruningEnumerationSelectedEdge
