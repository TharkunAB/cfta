import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformMonotone

/-!
# Uniform constructor budgets for the actual parent prefix

The initial own guard vector bounds the actual class list and its paths.
Every class uses one common final row envelope for its possible tail.
The budget counts constructor requests, including cache hits.
It does not count instructions or constrain inherited payload size.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets
open SourceEqualityClassOrder (Record)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits Bounds)
open SourceCurrentAllocatedFiniteOrdinaryGuardLimits (Le)
open SourceCurrentAllocatedFiniteOrdinaryGuardOwn (classBudget pathDepth)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers (parentRows)
namespace Counts
export SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds (nodeCount edgeCount)
end Counts
namespace Target
export SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers (targetRows nodeBudget edgeBudget)
end Target
local notation "Native" => SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.nodeBudget
local notation "ClassN" => SourceCurrentAllocatedFiniteOrdinaryClassResources.nodeBudget
local notation "ClassE" => SourceCurrentAllocatedFiniteOrdinaryClassResources.edgeBudget
local notation "PassN" => SourceCurrentAllocatedFiniteOrdinaryPassResources.nodeBudget
local notation "PassE" => SourceCurrentAllocatedFiniteOrdinaryPassResources.edgeBudget

/-- One position permits a complete target and the following native query. -/
def leafNodes (paths rows arity count depth bound : Nat) : Nat :=
  Target.nodeBudget rows arity count depth bound paths +
    Native (max (Target.targetRows rows count depth bound paths) rows) (max arity 1) bound

/-- Edge requests use the same conservative native Work budget. -/
def leafEdges (paths rows arity count depth bound : Nat) : Nat :=
  Target.edgeBudget rows arity count depth bound paths +
    Native (max (Target.targetRows rows count depth bound paths) rows) (max arity 1) bound

/-- Every original forest position permits a leaf and every ordinary node permits rebuilding. -/
def classNodes (paths rows arity count depth bound : Nat) : Nat :=
  count * (1 + arity * Counts.edgeCount rows arity bound) * leafNodes paths rows arity count depth bound +
    count * Counts.nodeCount rows arity bound

/-- Every original row occurrence permits edge rebuilding. -/
def classEdges (paths rows arity count depth bound : Nat) : Nat :=
  count * (1 + arity * Counts.edgeCount rows arity bound) * leafEdges paths rows arity count depth bound +
    count * Counts.edgeCount rows arity bound

/-- Required precedes at most the original own class count, each at the common final profile. -/
def nodeBudget (limits : Limits) (rows arity bound : Nat) : Nat :=
  arity * Counts.nodeCount rows arity bound +
    classBudget limits * classNodes (classBudget limits) (parentRows limits rows arity bound)
      (max arity 1) arity (pathDepth limits) bound

/-- The checked parent constructor adds one edge request after the local prefix. -/
def edgeBudget (limits : Limits) (rows arity bound : Nat) : Nat :=
  arity * Counts.edgeCount rows arity bound +
    classBudget limits * classEdges (classBudget limits) (parentRows limits rows arity bound)
      (max arity 1) arity (pathDepth limits) bound + 1

private theorem max_mono {a b c d : Nat} (one : a ≤ c) (two : b ≤ d) : max a b ≤ max c d :=
  Nat.max_le.mpr ⟨Nat.le_trans one (Nat.le_max_left _ _), Nat.le_trans two (Nat.le_max_right _ _)⟩

private theorem native_mono {rows largerRows arity largerArity bound largerBound : Nat}
    (rowBound : rows ≤ largerRows) (arityBound : arity ≤ largerArity) (heightBound : bound ≤ largerBound) :
    Native rows arity bound ≤ Native largerRows largerArity largerBound := by
  have parameters : Native rows arity bound ≤ Native largerRows largerArity bound := by
    clear heightBound largerBound
    induction bound with
    | zero => exact Nat.le_refl _
    | succ bound ih =>
        exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul rowBound rowBound)
          (Nat.add_le_add_left (Nat.mul_le_mul arityBound ih) 1)) 1
  exact Nat.le_trans parameters (SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.node_mono _ _ heightBound)

/-- Wider rows, arity, and height retain both original occurrence counts. -/
theorem counts_mono {rows largerRows arity largerArity bound largerBound : Nat}
    (rowBound : rows ≤ largerRows) (arityBound : arity ≤ largerArity) (heightBound : bound ≤ largerBound) :
    Counts.nodeCount rows arity bound ≤ Counts.nodeCount largerRows largerArity largerBound ∧
      Counts.edgeCount rows arity bound ≤ Counts.edgeCount largerRows largerArity largerBound := by
  have parameters : Counts.nodeCount rows arity bound ≤ Counts.nodeCount largerRows largerArity bound ∧
      Counts.edgeCount rows arity bound ≤ Counts.edgeCount largerRows largerArity bound := by
    clear heightBound largerBound
    induction bound with
    | zero => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    | succ bound ih =>
        exact ⟨Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul rowBound arityBound) ih.1) 1,
          Nat.mul_le_mul rowBound (Nat.add_le_add_left (Nat.mul_le_mul arityBound ih.2) 1)⟩
  exact ⟨Nat.le_trans parameters.1 (SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.nodeCount_mono _ _ heightBound),
    Nat.le_trans parameters.2 (SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.edgeCount_mono _ _ heightBound)⟩

/-- Increasing any common class input bound retains both permitted leaf costs. -/
theorem leaf_mono {paths largerPaths rows largerRows arity largerArity count largerCount depth largerDepth bound largerBound : Nat}
    (pathBound : paths ≤ largerPaths) (rowBound : rows ≤ largerRows) (arityBound : arity ≤ largerArity)
    (countBound : count ≤ largerCount) (depthBound : depth ≤ largerDepth) (heightBound : bound ≤ largerBound) :
    leafNodes paths rows arity count depth bound ≤ leafNodes largerPaths largerRows largerArity largerCount largerDepth largerBound ∧
      leafEdges paths rows arity count depth bound ≤ leafEdges largerPaths largerRows largerArity largerCount largerDepth largerBound := by
  have targetN := Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers.node_parameters_mono paths
    rowBound arityBound countBound depthBound heightBound)
    (SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers.node_mono _ _ _ _ _ pathBound)
  have targetE := Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers.edge_parameters_mono paths
    rowBound arityBound countBound depthBound heightBound)
    (SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers.edge_mono _ _ _ _ _ pathBound)
  have targetR := Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers.targetRows_parameters_mono paths
    rowBound countBound depthBound heightBound)
    (SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers.targetRows_mono _ _ _ _ pathBound)
  have query := native_mono (max_mono targetR rowBound) (max_mono arityBound (Nat.le_refl 1)) heightBound
  exact ⟨Nat.add_le_add targetN query, Nat.add_le_add targetE query⟩

/-- Increasing any common class input bound retains both whole-class constructor costs. -/
theorem class_mono {paths largerPaths rows largerRows arity largerArity count largerCount depth largerDepth bound largerBound : Nat}
    (pathBound : paths ≤ largerPaths) (rowBound : rows ≤ largerRows) (arityBound : arity ≤ largerArity)
    (countBound : count ≤ largerCount) (depthBound : depth ≤ largerDepth) (heightBound : bound ≤ largerBound) :
    classNodes paths rows arity count depth bound ≤ classNodes largerPaths largerRows largerArity largerCount largerDepth largerBound ∧
      classEdges paths rows arity count depth bound ≤ classEdges largerPaths largerRows largerArity largerCount largerDepth largerBound := by
  have counts := counts_mono rowBound arityBound heightBound
  have leaves := leaf_mono pathBound rowBound arityBound countBound depthBound heightBound
  have positions := Nat.mul_le_mul countBound (Nat.add_le_add_left (Nat.mul_le_mul arityBound counts.2) 1)
  exact ⟨Nat.add_le_add (Nat.mul_le_mul positions leaves.1) (Nat.mul_le_mul countBound counts.1),
    Nat.add_le_add (Nat.mul_le_mul positions leaves.2) (Nat.mul_le_mul countBound counts.2)⟩

/-- The initial raw vector and larger ordinary bounds retain both parent budgets. -/
theorem parameters_mono {first last : Limits} {rows largerRows arity largerArity bound largerBound : Nat}
    (guards : Le first last) (rowBound : rows ≤ largerRows) (arityBound : arity ≤ largerArity)
    (heightBound : bound ≤ largerBound) :
    nodeBudget first rows arity bound ≤ nodeBudget last largerRows largerArity largerBound ∧
      edgeBudget first rows arity bound ≤ edgeBudget last largerRows largerArity largerBound := by
  have effective := SourceCurrentAllocatedFiniteOrdinaryGuardLimits.effective_mono guards
  have counts := counts_mono rowBound arityBound heightBound
  have classes := class_mono effective.1
    (SourceCurrentAllocatedFiniteOrdinaryParentUniformMonotone.parentRows_mono guards rowBound arityBound heightBound)
    (max_mono arityBound (Nat.le_refl 1)) arityBound effective.2 heightBound
  exact ⟨Nat.add_le_add (Nat.mul_le_mul arityBound counts.1) (Nat.mul_le_mul effective.1 classes.1),
    Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul arityBound counts.2) (Nat.mul_le_mul effective.1 classes.2)) 1⟩

/-- Every parent budget includes the raw-rejection sentinel request. -/
theorem edgeBudget_pos (limits : Limits) (rows arity bound : Nat) : 1 ≤ edgeBudget limits rows arity bound := by
  unfold edgeBudget
  omega

private theorem target_cost_bound (record : Record) (paths rows arity count depth bound : Nat)
    (pathBound : record.paths.length ≤ paths) :
    SourceCurrentAllocatedFiniteOrdinaryTargetResources.nodeBudget rows arity count depth bound (record.paths.length - 1) ≤
        Target.nodeBudget rows arity count depth bound paths ∧
    SourceCurrentAllocatedFiniteOrdinaryTargetResources.edgeBudget rows arity count depth bound (record.paths.length - 1) ≤
        Target.edgeBudget rows arity count depth bound paths ∧
    SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows record rows count depth bound ≤
        Target.targetRows rows count depth bound paths := by
  cases countPaths : record.paths.length - 1 with
  | zero => simp only [SourceCurrentAllocatedFiniteOrdinaryTargetResources.nodeBudget,
      SourceCurrentAllocatedFiniteOrdinaryTargetResources.edgeBudget,
      SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows, countPaths,
      SourceCurrentAllocatedFiniteOrdinaryTargetResources.outputRows]; exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
  | succ remaining =>
      have enough : remaining ≤ paths := by omega
      exact ⟨by simpa only [countPaths, SourceCurrentAllocatedFiniteOrdinaryTargetResources.nodeBudget] using
          SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers.node_mono rows arity count depth bound enough,
        by simpa only [countPaths, SourceCurrentAllocatedFiniteOrdinaryTargetResources.edgeBudget] using
          SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers.edge_mono rows arity count depth bound enough,
        by simpa only [SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows, countPaths,
          SourceCurrentAllocatedFiniteOrdinaryTargetResources.outputRows] using
          SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers.targetRows_mono rows count depth bound enough⟩

/-- Each literal class fits the common path-count envelope at its own input parameters. -/
theorem class_budget (record : Record) (paths rows arity count depth bound : Nat)
    (pathBound : record.paths.length ≤ paths) :
    ClassN record rows arity count depth bound ≤ classNodes paths rows arity count depth bound ∧
      ClassE record rows arity count depth bound ≤ classEdges paths rows arity count depth bound := by
  have target := target_cost_bound record paths rows arity count depth bound pathBound
  have query : SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.queryBudget record rows arity count depth bound rows arity bound ≤
      Native (max (Target.targetRows rows count depth bound paths) rows) (max arity 1) bound := by
    unfold SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.queryBudget
    have arities : max (max arity 1) arity = max arity 1 := Nat.max_eq_left (Nat.le_max_left _ _)
    simpa only [arities, Nat.max_self] using native_mono (max_mono target.2.2 (Nat.le_refl rows))
      (Nat.le_refl (max arity 1)) (Nat.le_refl bound)
  have nodes := Nat.add_le_add target.1 query
  have edges := Nat.add_le_add target.2.1 query
  exact ⟨Nat.add_le_add_right (Nat.mul_le_mul_left _ nodes) _, Nat.add_le_add_right (Nat.mul_le_mul_left _ edges) _⟩

/-- All tail-first class costs fit one final-profile budget per original record. -/
theorem pass_budget (records : List Record) (limits : Limits) (rows arity count bound : Nat)
    (paths : ∀ record ∈ records, record.paths.length ≤ classBudget limits)
    (classes : records.length ≤ classBudget limits) (countBound : count ≤ arity) :
    PassN records rows arity count (pathDepth limits) bound ≤
        records.length * classNodes (classBudget limits) (parentRows limits rows arity bound) (max arity 1) arity (pathDepth limits) bound ∧
    PassE records rows arity count (pathDepth limits) bound ≤
        records.length * classEdges (classBudget limits) (parentRows limits rows arity bound) (max arity 1) arity (pathDepth limits) bound := by
  induction records with
  | nil => simp only [SourceCurrentAllocatedFiniteOrdinaryPassResources.nodeBudget,
      SourceCurrentAllocatedFiniteOrdinaryPassResources.edgeBudget, List.length_nil, Nat.zero_mul, Nat.le_refl, and_self]
  | cons record rest ih =>
      have tailPaths := fun value member => paths value (List.mem_cons_of_mem record member)
      have tailClasses : rest.length ≤ classBudget limits := by simp only [List.length_cons] at classes; omega
      have tail := ih tailPaths tailClasses
      have tailRows := SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.pass_rows rest
        (classBudget limits) (classBudget limits) rows count (pathDepth limits) bound tailPaths tailClasses
      have wholeRows := SourceCurrentAllocatedFiniteOrdinaryParentUniformMonotone.passRows_mono (classBudget limits)
        (Nat.le_refl (classBudget limits)) (Nat.le_refl rows) countBound
        (Nat.le_refl (pathDepth limits)) (Nat.le_refl bound)
      have head := class_budget record (classBudget limits)
        (SourceCurrentAllocatedFiniteOrdinaryPassResources.outputRows rest rows count (pathDepth limits) bound)
        (SourceCurrentAllocatedFiniteOrdinaryPassResources.outputArity rest arity) count (pathDepth limits) bound
        (paths record List.mem_cons_self)
      have wider := class_mono (Nat.le_refl (classBudget limits)) (Nat.le_trans tailRows wholeRows)
        (SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.pass_arity rest arity) countBound
        (Nat.le_refl (pathDepth limits)) (Nat.le_refl bound)
      have nodes := Nat.add_le_add tail.1 (Nat.le_trans head.1 wider.1)
      have edges := Nat.add_le_add tail.2 (Nat.le_trans head.2 wider.2)
      simpa only [SourceCurrentAllocatedFiniteOrdinaryPassResources.nodeBudget,
        SourceCurrentAllocatedFiniteOrdinaryPassResources.edgeBudget, List.length_cons, Nat.add_mul, Nat.one_mul, parentRows] using And.intro nodes edges

/-- The same initial precheck derives the literal parent budgets from the original raw vector. -/
theorem receipt_budget
    [DecidableEq (SourceObservations.Label FullSyntax.Formula)]
    [DecidableEq (InternedConstructorTemplates.EdgeKey (SourceObservations.Label FullSyntax.Formula)
      (SourceSymbolicIndex.Constraint FullSyntax.Formula))]
    {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {original : SourceSymbolicIndex.Constraint FullSyntax.Formula}
    {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {inherited own : SourceEqualityConstraintAllocation.Value} {before : SourceEqualityNativeDemand.State width}
    {branch : SourceEqualityPrecheck.Branch}
    (actual : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory original loaded inherited before own branch)
    (limits : Limits) (profile : Bounds limits original) (rows arity count bound : Nat) (countBound : count ≤ arity) :
    SourceCurrentAllocatedFiniteOrdinaryParentResources.nodeBudget original loaded inherited before.operations
        rows arity count (pathDepth limits) bound ≤ nodeBudget limits rows arity bound ∧
    SourceCurrentAllocatedFiniteOrdinaryParentResources.edgeBudget original loaded inherited before.operations
        rows arity count (pathDepth limits) bound ≤ edgeBudget limits rows arity bound := by
  have stage : ∀ records, branch = .classes records →
      SourceCurrentAllocatedFiniteOrdinaryStageResources.nodeBudget records rows arity count (pathDepth limits) bound ≤
        nodeBudget limits rows arity bound ∧
      SourceCurrentAllocatedFiniteOrdinaryStageResources.edgeBudget records rows arity count (pathDepth limits) bound + 1 ≤
        edgeBudget limits rows arity bound := by
    intro records same
    subst branch
    have classes := SourceCurrentAllocatedFiniteOrdinaryGuardOwn.receipt actual limits profile
    have pass := pass_budget records limits rows arity count bound classes.2.2.1 classes.2.1 countBound
    have counts : count * Counts.nodeCount rows arity bound ≤ arity * Counts.nodeCount rows arity bound ∧
        count * Counts.edgeCount rows arity bound ≤ arity * Counts.edgeCount rows arity bound :=
      ⟨Nat.mul_le_mul_right _ countBound, Nat.mul_le_mul_right _ countBound⟩
    have passNodes := Nat.mul_le_mul_right
      (classNodes (classBudget limits) (parentRows limits rows arity bound) (max arity 1) arity (pathDepth limits) bound) classes.2.1
    have passEdges := Nat.mul_le_mul_right
      (classEdges (classBudget limits) (parentRows limits rows arity bound) (max arity 1) arity (pathDepth limits) bound) classes.2.1
    exact ⟨Nat.add_le_add counts.1 (Nat.le_trans pass.1 passNodes),
      Nat.add_le_add_right (Nat.add_le_add counts.2 (Nat.le_trans pass.2 passEdges)) 1⟩
  unfold SourceCurrentAllocatedFiniteOrdinaryParentResources.nodeBudget SourceCurrentAllocatedFiniteOrdinaryParentResources.edgeBudget
  split
  · exact ⟨Nat.zero_le _, edgeBudget_pos limits rows arity bound⟩
  · cases branch with
    | unchanged | emptyChildren =>
        simp only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.nodeBudget,
          SourceCurrentAllocatedFiniteOrdinaryLocalResources.edgeBudget, actual.actual]
        exact ⟨Nat.zero_le _, edgeBudget_pos limits rows arity bound⟩
    | classes records =>
        simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.nodeBudget,
          SourceCurrentAllocatedFiniteOrdinaryLocalResources.edgeBudget, actual.actual] using stage records rfl

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets
