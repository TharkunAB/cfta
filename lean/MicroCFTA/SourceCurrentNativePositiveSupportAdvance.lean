import MicroCFTA.SourceCurrentNativePositiveSupportRebase
import MicroCFTA.SourceCurrentConstrainedCapCurrentNative

/-!
# Positional support through unchanged native cells

The actual machine extension retains the entry source records.
The same complete native tables retain their captured requests and laws.
-/
namespace MicroCFTA.SourceCurrentNativePositiveSupportAdvance
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentNativeRequestPositivePositions (Support)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
variable {width : Nat}

/-- Unchanged native cells retain their positive laws at the actual later heap. -/
theorem advance (before after : Checked width)
    (current : SourceCurrentConstrainedCapCurrentNative.At Plain before)
    (supported : Support before.native.machine.heap before.native)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good after)
    (extension : SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine)
    (nodes : after.native.nodes = before.native.nodes)
    (edges : after.native.edges = before.native.edges) :
    Support after.native.machine.heap after.native := by
  have retained : Support before.native.machine.heap after.native :=
    ⟨by simpa only [nodes] using supported.1, by simpa only [edges] using supported.2⟩
  have origins : SourceCurrentConstrainedCapCheckedJointOrigins.Stored before.native.machine.heap after.native :=
    ⟨by simpa only [nodes] using current.2.2.nodes, by simpa only [edges] using current.2.2.edges⟩
  exact SourceCurrentNativePositiveSupportRebase.rebase before.native.machine.heap after.native.machine.heap
    after.native current.1.valid.1 good.native.machine.1 extension.heap extension.history origins retained

end MicroCFTA.SourceCurrentNativePositiveSupportAdvance
