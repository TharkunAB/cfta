import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardProfiles

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.GuardFoundationChecks
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits Bounds effectiveBudget)
open SourceCurrentAllocatedFiniteOrdinaryGuardLimits
open SourceCurrentAllocatedFiniteOrdinaryGuardProfiles
variable {Symbol Formula : Type}
local notation "Constraint" => SourceSymbolicIndex.Constraint Formula

/-- Initial stored fields and syntax alone supply the effective envelope of a conjunction. -/
theorem computed_conjoin [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool) (first second : Constraint) :
    let common := step (join (of_constraint first) (of_constraint second))
    SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.OptionBounds
      (effectiveBudget common).1 (effectiveBudget common).2
      (SourceCompactGuards.sourceEqualities (SourceEqualityConstraintConstructors.conjoin le first second)) := by
  apply SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.effective
  exact conjoin_step le first second _
    (bounds_mono _ (of_constraint_bounds first) (le_join_left _ _))
    (bounds_mono _ (of_constraint_bounds second) (le_join_right _ _))

/-- A retained initial vector stays below a joined native step and its effective budget. -/
theorem effective_order (first second : Limits) :
    Le first (step (join first second)) ∧
    (effectiveBudget first).1 ≤ (effectiveBudget (step (join first second))).1 ∧
    (effectiveBudget first).2 ≤ (effectiveBudget (step (join first second))).2 := by
  have enough := le_trans (le_join_left first second) (step_ge (join first second))
  exact ⟨enough, effective_mono enough⟩

/-- Two ordinary levels of readback use the original forest's computed guard envelope. -/
theorem nested_initial (values : List (Value Symbol Constraint))
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children values)
    (root : Value Symbol Constraint) (rootMember : root ∈ values)
    (outer : EdgeValue Symbol Constraint) (outerMember : outer ∈ InternedEdgeResidency.nodeEdges root)
    (child : Value Symbol Constraint) (childMember : child ∈ outer.children)
    (inner : EdgeValue Symbol Constraint) (innerMember : inner ∈ InternedEdgeResidency.nodeEdges child) :
    Bounds (childrenLimits values) inner.entry.key.constraint := by
  have rootProfile := node_of_root values domain root rootMember
  have childProfile := Node.child root rootProfile outer outerMember child childMember
  exact Edge.guard inner (Rows.member _ (Node.nodeEdges child childProfile) inner innerMember)

/-- A literal conjunction edge retains every child under the common native step. -/
theorem native_literal_edge [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (first second : EdgeValue Symbol Constraint) (common : Limits)
    (firstProfile : Edge common first) (secondProfile : Edge common second) (identity : Nat) :
    let key : EdgeKey Symbol Constraint := ⟨first.entry.key.symbol, first.children.map Value.referenceOf,
      SourceEqualityConstraintConstructors.conjoin le first.entry.key.constraint second.entry.key.constraint⟩
    Edge (step common) (.mk ⟨identity, key⟩ first.children) := by
  refine ⟨conjoin_step le _ _ common (Edge.guard first firstProfile) (Edge.guard second secondProfile), ?_⟩
  exact Children.mono _ (Edge.children first firstProfile) (step_ge common)

/-- The literal Top sentinel fits every original hereditary envelope. -/
theorem top_sentinel (symbol : Symbol) (identity : Nat) (common : Limits) :
    let key : EdgeKey Symbol Constraint := ⟨symbol, [.empty], SourceEqualityConstraintConstructors.top⟩
    Edge common (.mk ⟨identity, key⟩ [.empty]) := by
  exact ⟨top_bounds common, ⟨Node.empty common, trivial⟩⟩

private def completeGuard : SourceSymbolicIndex.Constraint Unit :=
  ⟨some [[[1000000], [1000001, 2]]],
    .and [.same [1000000] [1000001, 2], .or [.not (.same [7, 8, 9] [10]), .top]]⟩

private def literalEdge : EdgeValue Unit (SourceSymbolicIndex.Constraint Unit) :=
  .mk ⟨3, ⟨(), [.empty], completeGuard⟩⟩ [.empty]

private def literalNode : Value Unit (SourceSymbolicIndex.Constraint Unit) :=
  .node ⟨4, .node [3]⟩ [literalEdge] 0 []

/-- Stored equalities, Same, Or, and Not coexist in a directly computed original profile. -/
theorem concrete_full_guard : Node (limits literalNode) literalNode ∧
    Bounds (limits literalNode) completeGuard := by
  have domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node literalNode :=
    .ordinary (.cons (.cons .empty .nil) .nil)
  have bounded := node_self literalNode domain
  exact ⟨bounded, Edge.guard literalEdge (Rows.member _ (Node.nodeEdges literalNode bounded) literalEdge (by simp [literalNode]))⟩

end MicroCFTA.GuardFoundationChecks

#print axioms MicroCFTA.GuardFoundationChecks.computed_conjoin
#check @MicroCFTA.GuardFoundationChecks.computed_conjoin
#print axioms MicroCFTA.GuardFoundationChecks.effective_order
#check @MicroCFTA.GuardFoundationChecks.effective_order
#print axioms MicroCFTA.GuardFoundationChecks.nested_initial
#check @MicroCFTA.GuardFoundationChecks.nested_initial
#print axioms MicroCFTA.GuardFoundationChecks.native_literal_edge
#check @MicroCFTA.GuardFoundationChecks.native_literal_edge
#print axioms MicroCFTA.GuardFoundationChecks.top_sentinel
#check @MicroCFTA.GuardFoundationChecks.top_sentinel
#print axioms MicroCFTA.GuardFoundationChecks.concrete_full_guard
#check @MicroCFTA.GuardFoundationChecks.concrete_full_guard
