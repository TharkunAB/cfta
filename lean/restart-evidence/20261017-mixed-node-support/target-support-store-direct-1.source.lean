import MicroCFTA.SourceCurrentHereditaryNativeTransition
import MicroCFTA.SourceCurrentHereditaryNativeControl

/-!
# Causal local laws across query source heaps

Empty native tables satisfy the conditional laws for each source heap.
A fresh finish installs its actual annotated result for each source heap.
The invariant does not restrict unrelated guards in the constructor heap.
-/
namespace MicroCFTA.SourceCurrentHereditaryNativeUniversalStore
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

/-- Returned native laws remain usable when a later query chooses its own source heap. -/
structure Stored (annotation : Guard → Prop) (state : Checked width) : Prop where
  constructors : SourceCurrentHereditaryConstruction.MuStored annotation state.native.machine.heap
  native : ∀ source, SourceCurrentHereditaryNativeCache.Stored annotation source state.native

variable (annotation : Guard → Prop)

/-- Fresh native tables have no returned-cell annotation obligation. -/
theorem initial (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (constructors : SourceCurrentHereditaryConstruction.MuStored annotation machine.heap) :
    Stored annotation ⟨SourceRecursiveIntersectionThunks.initial width machine, operations⟩ :=
  ⟨constructors, fun source => SourceCurrentHereditaryNativeCache.initial_stored annotation source width machine⟩

/-- An actual machine change retains every unchanged native return law. -/
theorem advance (before : Checked width) (machine : Machine Symbol Guard)
    (stored : Stored annotation before)
    (constructors : SourceCurrentHereditaryConstruction.MuStored annotation machine.heap) :
    Stored annotation {before with native := SourceRecursiveIntersectionThunks.advance before.native machine} :=
  ⟨constructors, fun source => SourceCurrentHereditaryNativeCache.advance_stored annotation source before.native machine (stored.native source)⟩

/-- A completed node installs its derived annotation at the exact evaluating owner. -/
theorem finishNode (before : Checked width) (handle : Nat) (request : NodeRequest Symbol Guard)
    (result : Value Symbol Guard) (stored : Stored annotation before)
    (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (annotated : Annotated annotation result) :
    Stored annotation {before with native := SourceRecursiveIntersectionThunks.finishNode handle result before.native} :=
  ⟨stored.constructors, fun source => SourceCurrentHereditaryNativeCache.finishNode_stored annotation source before.native
    handle request result (stored.native source) running
    (SourceCurrentHereditaryNativeControl.node_law annotation source request result annotated)⟩

/-- A completed row installs its full derived guard and child annotation. -/
theorem finishEdge (before : Checked width) (handle : Nat) (request : EdgeRequest Symbol Guard)
    (result : EdgeValue Symbol Guard) (stored : Stored annotation before)
    (running : before.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (annotated : SourceCurrentHereditaryConstructors.Edge annotation result) :
    Stored annotation {before with native := SourceRecursiveIntersectionThunks.finishEdge handle result before.native} :=
  ⟨stored.constructors, fun source => SourceCurrentHereditaryNativeCache.finishEdge_stored annotation source before.native
    handle request result (stored.native source) running
    (SourceCurrentHereditaryNativeControl.edge_law annotation source request result annotated)⟩

/-- Node demand preserves all source-indexed laws at its literal returned state. -/
theorem node_yielded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (request : NodeRequest Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard A) (before after : Checked width) (control : SourceEqualityNativeDemand.Control A)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native) (stored : Stored annotation before)
    (ready : NodeReady before.native.machine request)
    (words : SourceCurrentAllocatedNativeRequestBounds.Words width (.code (.node request next)))
    (actual : SourceEqualityNativeDemand.step (.code (.node request next)) before = .yielded control after) :
    Stored annotation after := by
  have first := SourceCurrentHereditaryNativeTransition.node_yielded annotation source request next before control after
    valid (stored.native source) ready words actual
  exact ⟨by rw [first.1]; exact stored.constructors, fun other =>
    (SourceCurrentHereditaryNativeTransition.node_yielded annotation other request next before control after
      valid (stored.native other) ready words actual).2.2.1⟩

/-- Edge demand preserves all source-indexed laws at its literal returned state. -/
theorem edge_yielded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A) (before after : Checked width) (control : SourceEqualityNativeDemand.Control A)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native) (stored : Stored annotation before)
    (ready : EdgeReady before.native.machine request)
    (words : SourceCurrentAllocatedNativeRequestBounds.Words width (.code (.edge request next)))
    (actual : SourceEqualityNativeDemand.step (.code (.edge request next)) before = .yielded control after) :
    Stored annotation after := by
  have first := SourceCurrentHereditaryNativeTransition.edge_yielded annotation source request next before control after
    valid (stored.native source) ready words actual
  exact ⟨by rw [first.1]; exact stored.constructors, fun other =>
    (SourceCurrentHereditaryNativeTransition.edge_yielded annotation other request next before control after
      valid (stored.native other) ready words actual).2.2.1⟩

end MicroCFTA.SourceCurrentHereditaryNativeUniversalStore
