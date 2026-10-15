import MicroCFTA.SourceEqualityPartialMemoFrame
import MicroCFTA.SourceEqualityPartialResultMemoSource

/-!
# Actual completed memo execution with one shared source leaf

Closed source construction interns the two leaf occurrences as one value.
The cold worker returns successfully and allocates only the root and leaf
result cells. Both cells are returned. The second leaf request reuses its
published result. These are finite execution facts for this fixture.
-/
namespace MicroCFTA.SourceEqualityPartialMemoCompletedExample
open InternedConstructorTemplates InternedNestedConstruction
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph
open SourceEqualityPartialMemoWorker SourceEqualityPartialMemoFrame
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 200000000

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)

private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

/-- The source leaf has an empty child list and the full Top constraint. -/
def leaf : Syntax Symbol Guard := .node [.mk ("a", .top) top []]

/-- The binary root contains the same literal source leaf in both positions. -/
def expression : Syntax Symbol Guard := .node [.mk ("p", .top) top [leaf, leaf]]

/-- The input syntax is closed and every complete physical annotation is normalized. -/
theorem source_valid : Scoped 0 expression ∧
    SourceEqualityAnnotationConstruction.Allowed SourceEqualityNormalizedEntry.ValidGuard expression := by
  constructor
  · simp [expression, leaf, Scoped, ManyScoped, EdgesScoped]
  · simp only [expression, leaf, SourceEqualityAnnotationConstruction.Allowed,
      SourceEqualityAnnotationConstruction.ManyAllowed, SourceEqualityAnnotationConstruction.EdgesAllowed]
    simp only [SourceEqualityNormalizedEntry.ValidGuard, SourceEqualityConstraintConstructors.top_cached, and_self]

/-- A completed observation retains the original construction and the full returned state. -/
structure Trace where
  root : Value Symbol Guard
  heap : InternedConstructorTemplates.State Symbol Guard
  result : Value Symbol Guard
  state : SourceEqualityPartialMemoWorker.State 8

/-- Execute the actual recursive memo worker from empty constraint and result tables. -/
noncomputable def observation : Option Trace :=
  match InternedFreshOrdinaryConstruction.build expression [] empty with
  | .pending .. => none
  | .done root heap =>
      match SourceEqualityPartialMemoWorker.run 2 2 2 2 2 8 2 (some []) root
          (initial (SourceEqualityNativeInitial.cold 8 heap)) with
      | .done (.ok result) state => some ⟨root, heap, result, state⟩
      | _ => none

/-- Successful observation supplies the actual source construction and complete run receipts. -/
theorem observation_receipts (observed : Trace) (found : observation = some observed) :
    InternedFreshOrdinaryConstruction.build expression [] empty = .done observed.root observed.heap ∧
      SourceEqualityPartialMemoWorker.run 2 2 2 2 2 8 2 (some []) observed.root
        (initial (SourceEqualityNativeInitial.cold 8 observed.heap)) = .done (.ok observed.result) observed.state := by
  unfold observation at found
  split at found <;> try contradiction
  split at found <;> try contradiction
  cases found
  exact ⟨by assumption, by assumption⟩

/-- Read child references only from the fixture's one-row ordinary head. -/
def childReferences : Value Symbol Guard → List InternedBinderProtocol.NodeRef
  | .node _ [edge] _ _ => edge.children.map Value.referenceOf
  | _ => []

/-- Check both completed cells, sharing, physical root preservation, and published keys. -/
noncomputable def certificate : Bool :=
  match observation with
  | none => false
  | some observed =>
      match observed.state.memo.cells 0, observed.state.memo.cells 1 with
      | some ⟨root, .returned rootResult⟩, some ⟨leaf, .returned leafResult⟩ =>
          decide (observed.state.memo.next = 2 ∧
            childReferences observed.root = [leaf.value.referenceOf, leaf.value.referenceOf] ∧
            root.value.referenceOf = observed.root.referenceOf ∧
            rootResult.referenceOf = observed.result.referenceOf ∧
            leafResult.referenceOf = leaf.value.referenceOf ∧
            observed.result.referenceOf = observed.root.referenceOf ∧
            leaf.value.referenceOf ≠ root.value.referenceOf ∧
            observed.state.memo.table (some 0, observed.root.referenceOf) = some 0 ∧
            observed.state.memo.table (some 0, leaf.value.referenceOf) = some 1) &&
          SourceEqualityPrecheck.isEmpty root.inherited && SourceEqualityPrecheck.isEmpty leaf.inherited
      | _, _ => false

/-- Kernel reduction checks actual cold completion and the shared leaf's returned memo cell. -/
theorem actual : certificate = true := by cbv

/-- The concrete cold check plan contains only reached native and recursive checks. -/
def constructionChecked : Prop :=
  match InternedFreshOrdinaryConstruction.build expression [] empty with
  | .pending .. => False
  | .done root heap => SourceEqualityPartialResultMemoProofs.Checked 2 2 2 2 2 8 2 (some []) root
      (initial (SourceEqualityNativeInitial.cold 8 heap))

/-- Kernel reduction and actual receipt equalities discharge the complete cold check plan. -/
theorem actual_checked : constructionChecked := by
  cbv
  constructor
  · intro payload actual
    cbv at actual
    cases actual
    cbv
  · constructor
    · intro narrowed middle receipt own physical payload combined
      cbv at receipt
      cases receipt
      cbv at physical
      cases physical
      cbv at combined
      cases combined
      cbv
      constructor
      · constructor
        · intro payload actual
          cbv at actual
          cases actual
          cbv
        · constructor
          · intro narrowed middle receipt own physical payload combined
            cbv at receipt
            cases receipt
            cbv at physical
            cases physical
            cbv at combined
            cases combined
            cbv
          · intro result middle receipt
            cbv at receipt
            cases receipt
            cbv
      · intro result middle receipt
        cbv at receipt
        cases receipt
        cbv
        intros
        trivial
    · intro result middle receipt
      cbv at receipt
      cases receipt
      cbv

/-- Every successful observation has the proved actual cold check plan. -/
theorem observed_checked (observed : Trace) (found : observation = some observed) :
    SourceEqualityPartialResultMemoProofs.Checked 2 2 2 2 2 8 2 (some []) observed.root
      (initial (SourceEqualityNativeInitial.cold 8 observed.heap)) := by
  have checked := actual_checked
  unfold constructionChecked at checked
  rw [(observation_receipts observed found).1] at checked
  exact checked

/-- The concrete successful cold run instantiates the actual public semantic theorem. -/
theorem observed_exact (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (observed : Trace) (found : observation = some observed) :
    SourceEqualityPartialMemoSound.Sound (acceptsConstraint formulas solver) ambient observed.state ∧
      SourceEqualityPartialScope.Scope observed.state.native ∧
      SourceEqualityRequiredCache.Keeps observed.heap observed.state.native.machine.heap ∧
      InternedProbeProvenance.Available observed.state.native.machine.heap observed.result ∧ observed.result.free = [] ∧
      ∀ term, InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient observed.result term ↔
        InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient observed.root term := by
  have receipts := observation_receipts observed found
  exact SourceEqualityPartialResultMemoSource.public_exact 8 expression source_valid.2 observed.root observed.heap receipts.1
    formulas solver ambient 2 2 2 2 2 8 2 observed.result observed.state (observed_checked observed found) receipts.2

/-- Actual completion retains the two distinct returned requests and their physical source keys. -/
theorem actual_completed : ∃ observed root rootResult leaf leafResult,
    observation = some observed ∧
    observed.state.memo.cells 0 = some ⟨root, .returned rootResult⟩ ∧
    observed.state.memo.cells 1 = some ⟨leaf, .returned leafResult⟩ ∧
    (observed.state.memo.next = 2 ∧
      childReferences observed.root = [leaf.value.referenceOf, leaf.value.referenceOf] ∧
      root.value.referenceOf = observed.root.referenceOf ∧
      rootResult.referenceOf = observed.result.referenceOf ∧
      leafResult.referenceOf = leaf.value.referenceOf ∧
      observed.result.referenceOf = observed.root.referenceOf ∧
      leaf.value.referenceOf ≠ root.value.referenceOf ∧
      observed.state.memo.table (some 0, observed.root.referenceOf) = some 0 ∧
      observed.state.memo.table (some 0, leaf.value.referenceOf) = some 1) ∧
    SourceEqualityPrecheck.isEmpty root.inherited = true ∧ SourceEqualityPrecheck.isEmpty leaf.inherited = true := by
  have checked := actual
  unfold certificate at checked
  split at checked <;> try contradiction
  split at checked <;> try contradiction
  simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨_, _, _, _, _, by assumption, by assumption, by assumption, checked.1.1, checked.1.2, checked.2⟩

/-- The complete actual receipt derives valid key-linked tables without computing their equality. -/
theorem observed_valid (observed : Trace) (found : observation = some observed) : Valid (stateTables observed.state) := by
  have receipts := observation_receipts observed found
  have frame := run_frame 2 2 2 2 2 8 2 (some []) observed.root
    (initial (SourceEqualityNativeInitial.cold 8 observed.heap)) (initial_valid _)
  rw [receipts.2] at frame
  exact frame.valid

/-- The cold completed run has exactly two allocated cells, both returned. -/
theorem actual_only_two : ∃ observed root rootResult leaf leafResult,
    observation = some observed ∧ Valid (stateTables observed.state) ∧
    observed.state.memo.cells 0 = some ⟨root, .returned rootResult⟩ ∧
    observed.state.memo.cells 1 = some ⟨leaf, .returned leafResult⟩ ∧
    observed.result.referenceOf = observed.root.referenceOf ∧
    (∀ handle, 2 ≤ handle → observed.state.memo.cells handle = none) := by
  obtain ⟨observed, root, rootResult, leaf, leafResult, found, first, second, facts, _, _⟩ := actual_completed
  have valid := observed_valid observed found
  refine ⟨observed, root, rootResult, leaf, leafResult, found, valid, first, second, facts.2.2.2.2.2.1, ?_⟩
  intro handle later
  cases stored : observed.state.memo.cells handle with
  | none => rfl
  | some cell =>
      have bound := valid.2.bounded handle cell stored
      change handle < observed.state.memo.next at bound
      rw [facts.1] at bound
      omega

end MicroCFTA.SourceEqualityPartialMemoCompletedExample
