import MicroCFTA.SourceCurrentConjunctionTuplePullAdmission
import MicroCFTA.SourceCurrentConjunctionTuplePullTotal

/-!
# Physical operand reads skipped by an outer symbol mismatch

The source fold reads the first and last ordinary operands before the middle
operand. Different outer symbols end this stream without reading the middle
operand. The old eager exposure list still reads that operand.
The zero read allowance below is a modeled observation limit. It is not a
native Haskell fault or a claim about a reachable allocator failure.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullDemand
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- An outer mismatch completes in six transitions without demanding the middle operand. -/
theorem mismatch_skips_middle (h budget : Nat) (before : Physical Symbol Formula)
    (leftEntry rightEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (left right : Edge) (leftDepth rightDepth : Nat)
    (leftFree rightFree : List InternedBinderProtocol.Reference) (middle : Node)
    (different : right.entry.key.symbol ≠ left.entry.key.symbol) :
    SourceCurrentConjunctionTuplePullAdmission.sample 6 h budget
      [.node leftEntry [left] leftDepth leftFree, middle,
        .node rightEntry [right] rightDepth rightFree] before =
      .done (.fit []) before := by
  simp [SourceCurrentConjunctionTuplePullAdmission.sample,
    SourceCurrentConjunctionTuplePullAdmission.drive,
    SourceCurrentConjunctionTuplePullAdmission.advance,
    SourceCurrentConjunctionTuplePull.start, SourceCurrentConjunctionTuplePull.step,
    SourceCurrentConjunctionTuplePull.expose, SourceCurrentConjunctionRowsWorker.exposures,
    MergedFreshOrdinaryExposure.nodeEdges, Outcome.bind, different]

/-- Total sampling derives the same skipped read without a transition allowance. -/
theorem total_mismatch_skips_middle (h budget : Nat) (before : Physical Symbol Formula)
    (leftEntry rightEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (left right : Edge) (leftDepth rightDepth : Nat)
    (leftFree rightFree : List InternedBinderProtocol.Reference) (middle : Node)
    (different : right.entry.key.symbol ≠ left.entry.key.symbol) :
    SourceCurrentConjunctionTuplePullTotal.sample h budget
      [.node leftEntry [left] leftDepth leftFree, middle,
        .node rightEntry [right] rightDepth rightFree] before =
      .done (.fit []) before := by
  apply SourceCurrentConjunctionTuplePullTotal.run_of_observation 6
  exact mismatch_skips_middle h budget before leftEntry rightEntry left right
    leftDepth rightDepth leftFree rightFree middle different

omit [DecidableEq Symbol] in
/-- Eager exposure propagates the middle read fault even when the outer rows mismatch. -/
theorem eager_middle_fault (h : Nat) (before after : Physical Symbol Formula)
    (leftEntry rightEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (left right : Edge) (leftDepth rightDepth : Nat)
    (leftFree rightFree : List InternedBinderProtocol.Reference) (middle : Node)
    (fault : SourceCurrentConjunctionRowsWorker.Fault)
    (failed : SourceCurrentConjunctionRowsWorker.exposures h [middle] before = .failed fault after) :
    SourceCurrentConjunctionRowsWorker.exposures h
      [.node leftEntry [left] leftDepth leftFree, middle,
        .node rightEntry [right] rightDepth rightFree] before = .failed fault after := by
  cases read : MergedFreshOrdinaryExposure.nodeEdges h middle before.heap <;>
    simp_all [SourceCurrentConjunctionRowsWorker.exposures,
      MergedFreshOrdinaryExposure.nodeEdges, Outcome.bind]

omit [DecidableEq Symbol] in
/-- A union requires observation fuel even when the lazy tuple stream never demands it. -/
theorem unread_union_exhausted (before : Physical Symbol Formula)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (members : List Node)
    (depth : Nat) (free : List InternedBinderProtocol.Reference) :
    SourceCurrentConjunctionRowsWorker.exposures 0 [.union entry members depth free] before =
      .failed (.exhausted .head) before := by
  rfl

end MicroCFTA.SourceCurrentConjunctionTuplePullDemand
