import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNarrow
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored
import MicroCFTA.SourceCurrentAllocatedMkEdge

/-!
# Finite ordinary bounds for actual checked parent constructors

The exact constructor receipt selects narrowed children or singleton Empty.
Both choices bound the returned edge by the original parent. A raw rejection
needs no original child domain or availability. Native tables keep their
conditional structural certificates through the same physical constructor.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMkEdge
open Language InternedConstructorTemplates
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
variable {width : Nat}

/-- Physical constructor receipts retain the exact native result tables. -/
theorem native_stored
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {before after : SourceEqualityNativeDemand.State width} {result : EdgeValue Symbol Guard}
    (receipt : SourceCurrentAllocatedMkEdge.PhysicalReceipt formulas solver inventory before result after)
    (stored : NativeStored before.native) : NativeStored after.native := by
  constructor
  · simpa only [receipt.nodes] using stored.nodes
  · simpa only [receipt.edges] using stored.edges

/-- A singleton Empty sentinel bounds every original row, without an arity condition. -/
theorem sentinel (original result : EdgeValue Symbol Guard) (children : result.children = [.empty]) :
    EdgeNarrow original result := by
  constructor
  · change SourceCurrentAllocatedFiniteOrdinaryDomain.Children result.children
    rw [children]
    exact .cons .empty .nil
  · rw [SourceCurrentAllocatedFiniteOrdinaryDomain.edgeHeight_children, children]
    exact Nat.zero_le _

/-- The actual checked constructor retains the original parent bound after narrowed children. -/
theorem narrowed [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {symbol : Symbol} {constraint : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {before after : SourceEqualityNativeDemand.State width}
    {result : EdgeValue Symbol Guard}
    (receipt : SourceCurrentAllocatedMkEdge.Receipt formulas solver inventory symbol constraint values before result after)
    (original : EdgeValue Symbol Guard) (related : All₂ NodeNarrow original.children values) :
    EdgeNarrow original result := by
  by_cases accepted : SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback constraint) values.length
  · have children : result.children = values := by simpa only [accepted, ↓reduceIte] using receipt.children
    exact SourceCurrentAllocatedFiniteOrdinaryNarrow.edge_children (children ▸ related)
  · have children : result.children = [.empty] := by simpa only [accepted, Bool.false_eq_true, ↓reduceIte] using receipt.children
    exact sentinel original result children

/-- A completed raw rejection gives the same structural bound without child inputs. -/
theorem rejected [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory} {symbol : Symbol}
    {before after : SourceEqualityNativeDemand.State width} {result : EdgeValue Symbol Guard}
    (receipt : SourceCurrentAllocatedMkEdge.RejectReceipt formulas solver inventory symbol before result after)
    (original : EdgeValue Symbol Guard) : EdgeNarrow original result :=
  sentinel original result receipt.children

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMkEdge
