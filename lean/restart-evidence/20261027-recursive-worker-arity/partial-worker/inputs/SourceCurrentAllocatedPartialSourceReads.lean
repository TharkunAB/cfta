import MicroCFTA.SourceCurrentAllocatedPartialReads
import MicroCFTA.SourceCurrentAllocatedParentEdgeActual

/-!
# Source-aligned global query schedules for current outer traces

Each read graph is indexed by the same completed raw caller trace. Parent
edge reads use its actual checked local reduction and anchored primary calls. Rows and child walks
thread the returned global bundle in source order. Caller memo hits skip
the body reads. Pure constructors and equality operations do not call the
three global query families in this schedule. No semantic, readiness, or
future-completion law is a field. These schedules do not prove physical
heap coherence, runtime forcing, or an operational Runs adapter for the
general Mu reconstruction callback.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialSourceReads
open InternedConstructorTemplates
open SourceCurrentAllocatedPartialGraph
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "NodeReq" => SourceCurrentAllocatedPartialState.NodeRequest
local notation "EdgeReq" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

mutual
/-- A returned node hit skips body reads; evaluation uses exactly its selected body. -/
inductive NodeCallReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {request : NodeReq} → {before : Caller width} → {result : Value Symbol Guard} → {after : Caller width} →
    NodeCall budget request before result after → Memos → Memos → Prop where
  | hit : NodeCallReads formulas solver (.hit started) memos memos
  | evaluate (reads : NodeBodyReads formulas solver body memos saved) :
      NodeCallReads formulas solver (.evaluate started body) memos saved

/-- Ordinary bodies follow rows; the other source node branches make no global query. -/
inductive NodeBodyReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {request : NodeReq} → {before : Caller width} → {result : Value Symbol Guard} → {after : Caller width} →
    NodeBody budget request before result after → Memos → Memos → Prop where
  | empty : NodeBodyReads formulas solver .empty memos memos
  | union : NodeBodyReads formulas solver .union memos memos
  | binder : NodeBodyReads formulas solver (.binder actual) memos memos
  | ordinary (reads : RowsReads formulas solver rows memos saved) :
      NodeBodyReads formulas solver (.ordinary rows) memos saved

/-- Edge result hits skip the checked parent body; evaluation retains its literal reads. -/
inductive EdgeCallReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {request : EdgeReq} → {before : Caller width} → {result : EdgeValue Symbol Guard} → {after : Caller width} →
    EdgeCall budget request before result after → Memos → Memos → Prop where
  | hit : EdgeCallReads formulas solver (.hit started) memos memos
  | evaluate (reads : EdgeBodyReads formulas solver body memos saved) :
      EdgeCallReads formulas solver (.evaluate started body) memos saved

/-- The parent leaf contains the same actual current checked read graph. -/
inductive EdgeBodyReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {request : EdgeReq} → {before : Caller width} → {result : EdgeValue Symbol Guard} → {after : Caller width} →
    EdgeBody budget request before result after → Memos → Memos → Prop where
  | parent (reads : SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos saved) :
      EdgeBodyReads formulas solver (.parent field actual) memos saved

/-- Each source row reads its parent call, then descendants, and then the row suffix. -/
inductive RowsReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {inherited : EqValue} → {values : List (EdgeValue Symbol Guard)} → {before : Caller width} →
    {results : List (EdgeValue Symbol Guard)} → {after : Caller width} →
    Rows budget inherited values before results after → Memos → Memos → Prop where
  | nil : RowsReads formulas solver .nil memos memos
  | cons (edge : EdgeCallReads formulas solver first memos middle)
      (children : DescendantsReads formulas solver child middle later)
      (rest : RowsReads formulas solver tail later saved) :
      RowsReads formulas solver (.cons first child tail) memos saved

/-- The inherited prefix and raw rebuild surround the actual child-query reads. -/
inductive DescendantsReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {inherited : EqValue} → {value : EdgeValue Symbol Guard} → {before : Caller width} →
    {result : EdgeValue Symbol Guard} → {after : Caller width} →
    Descendants budget inherited value before result after → Memos → Memos → Prop where
  | run (reads : ChildrenReads formulas solver children memos saved) :
      DescendantsReads formulas solver (.run combined children) memos saved

/-- Contradiction has no child call; a live inherited value follows its indexed walk. -/
inductive ChildrenReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {inherited : EqValue} → {values : List (Value Symbol Guard)} → {before : Caller width} →
    {results : List (Value Symbol Guard)} → {after : Caller width} →
    Children budget inherited values before results after → Memos → Memos → Prop where
  | contradiction : ChildrenReads formulas solver .contradiction memos memos
  | live (reads : WalkReads formulas solver actual memos saved) :
      ChildrenReads formulas solver (.live actual) memos saved

/-- Actual descended requests thread global reads from the head through the remaining slots. -/
inductive WalkReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {combined : EqValue} → {index : Nat} → {values : List (Value Symbol Guard)} → {before : Caller width} →
    {results : List (Value Symbol Guard)} → {after : Caller width} →
    Walk budget combined index values before results after → Memos → Memos → Prop where
  | nil : WalkReads formulas solver .nil memos memos
  | cons (head : NodeCallReads formulas solver first memos middle)
      (rest : WalkReads formulas solver tail middle saved) :
      WalkReads formulas solver (.cons first tail) memos saved
end

/-- A node result hit cannot change the global bundle in this actual read schedule. -/
theorem node_hit {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {budget : Nat} {request : NodeReq}
    {before running : Caller width} {handle : Nat} {result : Value Symbol Guard} {memos saved : Memos}
    (started : SourceCurrentAllocatedPartialState.beginNode request before = (handle, (.ready result, running)))
    (reads : NodeCallReads formulas solver (NodeCall.hit (budget := budget) started) memos saved) : saved = memos := by
  cases reads <;> simp_all

/-- An edge result hit skips the body and leaves every global query table unchanged. -/
theorem edge_hit {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {budget : Nat} {request : EdgeReq}
    {before running : Caller width} {handle : Nat} {result : EdgeValue Symbol Guard} {memos saved : Memos}
    (started : SourceCurrentAllocatedPartialState.beginEdge request before = (handle, (.ready result, running)))
    (reads : EdgeCallReads formulas solver (EdgeCall.hit (budget := budget) started) memos saved) : saved = memos := by
  cases reads <;> simp_all

/-- The contradiction branch has no child call and retains the literal incoming global bundle. -/
theorem children_contradiction {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {budget : Nat} {values : List (Value Symbol Guard)}
    {before : Caller width} {memos saved : Memos}
    (reads : ChildrenReads formulas solver (Children.contradiction (budget := budget) (values := values) (before := before)) memos saved) :
    saved = memos := by
  cases reads
  rfl


-- Erasure keeps the eight actual source graphs and every returned bundle.
local macro "erase_induction" recursor:ident reads:ident formulas:ident solver:ident : tactic => `(tactic|
  (apply $recursor
     (motive_1 := fun {_i0_0 _i0_1 _i0_2 _i0_3 _i0_4} trace memos final _ =>
       SourceCurrentAllocatedPartialReads.NodeCallReads $formulas $solver trace memos final)
     (motive_2 := fun {_i1_0 _i1_1 _i1_2 _i1_3 _i1_4} trace memos final _ =>
       SourceCurrentAllocatedPartialReads.NodeBodyReads $formulas $solver trace memos final)
     (motive_3 := fun {_i2_0 _i2_1 _i2_2 _i2_3 _i2_4} trace memos final _ =>
       SourceCurrentAllocatedPartialReads.EdgeCallReads $formulas $solver trace memos final)
     (motive_4 := fun {_i3_0 _i3_1 _i3_2 _i3_3 _i3_4} trace memos final _ =>
       SourceCurrentAllocatedPartialReads.EdgeBodyReads $formulas $solver trace memos final)
     (motive_5 := fun {_i4_0 _i4_1 _i4_2 _i4_3 _i4_4 _i4_5} trace memos final _ =>
       SourceCurrentAllocatedPartialReads.RowsReads $formulas $solver trace memos final)
     (motive_6 := fun {_i5_0 _i5_1 _i5_2 _i5_3 _i5_4 _i5_5} trace memos final _ =>
       SourceCurrentAllocatedPartialReads.DescendantsReads $formulas $solver trace memos final)
     (motive_7 := fun {_i6_0 _i6_1 _i6_2 _i6_3 _i6_4 _i6_5} trace memos final _ =>
       SourceCurrentAllocatedPartialReads.ChildrenReads $formulas $solver trace memos final)
     (motive_8 := fun {_i7_0 _i7_1 _i7_2 _i7_3 _i7_4 _i7_5 _i7_6} trace memos final _ =>
       SourceCurrentAllocatedPartialReads.WalkReads $formulas $solver trace memos final)
     (t := $reads)
   all_goals intros
   all_goals first
     | exact .hit (started := by assumption)
     | exact .evaluate (started := by assumption) (by assumption)
     | exact .empty
     | exact .union
     | exact .binder (actual := by assumption)
     | exact .ordinary (by assumption)
     | exact SourceCurrentAllocatedPartialReads.EdgeBodyReads.parent (field := by assumption)
         (SourceCurrentAllocatedParentEdgeActual.Reads.erase (by assumption))
     | exact .nil
     | exact .cons (by assumption) (by assumption) (by assumption)
     | exact .run (combined := by assumption) (by assumption)
     | exact .contradiction
     | exact .live (by assumption)
     | exact .cons (by assumption) (by assumption)))

/-- Source-aligned node call reads retain the historical graph and both global bundles. -/
theorem node_call_erase
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {budget : Nat} {request : NodeReq} {before after : Caller width} {result : Value Symbol Guard}
    {actual : NodeCall budget request before result after} {memos final : Memos}
    (reads : NodeCallReads formulas solver actual memos final) :
    SourceCurrentAllocatedPartialReads.NodeCallReads formulas solver actual memos final := by
  erase_induction NodeCallReads.rec reads formulas solver

/-- Source-aligned node body reads retain the historical graph and both global bundles. -/
theorem node_body_erase
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {budget : Nat} {request : NodeReq} {before after : Caller width} {result : Value Symbol Guard}
    {actual : NodeBody budget request before result after} {memos final : Memos}
    (reads : NodeBodyReads formulas solver actual memos final) :
    SourceCurrentAllocatedPartialReads.NodeBodyReads formulas solver actual memos final := by
  erase_induction NodeBodyReads.rec reads formulas solver

/-- Source-aligned edge call reads retain the historical graph and both global bundles. -/
theorem edge_call_erase
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {budget : Nat} {request : EdgeReq} {before after : Caller width} {result : EdgeValue Symbol Guard}
    {actual : EdgeCall budget request before result after} {memos final : Memos}
    (reads : EdgeCallReads formulas solver actual memos final) :
    SourceCurrentAllocatedPartialReads.EdgeCallReads formulas solver actual memos final := by
  erase_induction EdgeCallReads.rec reads formulas solver

/-- Source-aligned edge body reads retain the historical graph and both global bundles. -/
theorem edge_body_erase
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {budget : Nat} {request : EdgeReq} {before after : Caller width} {result : EdgeValue Symbol Guard}
    {actual : EdgeBody budget request before result after} {memos final : Memos}
    (reads : EdgeBodyReads formulas solver actual memos final) :
    SourceCurrentAllocatedPartialReads.EdgeBodyReads formulas solver actual memos final := by
  erase_induction EdgeBodyReads.rec reads formulas solver

/-- Source-aligned rows reads retain the historical graph and both global bundles. -/
theorem rows_erase
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {budget : Nat} {inherited : EqValue} {values results : List (EdgeValue Symbol Guard)} {before after : Caller width}
    {actual : Rows budget inherited values before results after} {memos final : Memos}
    (reads : RowsReads formulas solver actual memos final) :
    SourceCurrentAllocatedPartialReads.RowsReads formulas solver actual memos final := by
  erase_induction RowsReads.rec reads formulas solver

/-- Source-aligned descendants reads retain the historical graph and both global bundles. -/
theorem descendants_erase
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {budget : Nat} {inherited : EqValue} {value result : EdgeValue Symbol Guard} {before after : Caller width}
    {actual : Descendants budget inherited value before result after} {memos final : Memos}
    (reads : DescendantsReads formulas solver actual memos final) :
    SourceCurrentAllocatedPartialReads.DescendantsReads formulas solver actual memos final := by
  erase_induction DescendantsReads.rec reads formulas solver

/-- Source-aligned children reads retain the historical graph and both global bundles. -/
theorem children_erase
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {budget : Nat} {inherited : EqValue} {values results : List (Value Symbol Guard)} {before after : Caller width}
    {actual : Children budget inherited values before results after} {memos final : Memos}
    (reads : ChildrenReads formulas solver actual memos final) :
    SourceCurrentAllocatedPartialReads.ChildrenReads formulas solver actual memos final := by
  erase_induction ChildrenReads.rec reads formulas solver

/-- Source-aligned walk reads retain the historical graph and both global bundles. -/
theorem walk_erase
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {budget index : Nat} {combined : EqValue} {values results : List (Value Symbol Guard)} {before after : Caller width}
    {actual : Walk budget combined index values before results after} {memos final : Memos}
    (reads : WalkReads formulas solver actual memos final) :
    SourceCurrentAllocatedPartialReads.WalkReads formulas solver actual memos final := by
  erase_induction WalkReads.rec reads formulas solver

end MicroCFTA.SourceCurrentAllocatedPartialSourceReads
