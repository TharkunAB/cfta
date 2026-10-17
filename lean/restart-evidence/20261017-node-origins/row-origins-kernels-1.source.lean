import MicroCFTA.SourceCurrentRequiredRowOrigins
import MicroCFTA.SourceEqualityRequiredWorkerSound
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.RequiredRowOriginKernels
open Cache InternedConstructorTemplates InternedNestedConstruction InternedProbeProvenance InternedEdgeResidency
open SourceEqualityNeeded SourceCurrentRequiredRowOrigins
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def plain : Guard := ⟨some [], .top⟩
private def constrained : Guard := ⟨some [[[0],[1]]], .top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf", .top) plain []]
private def finite : Syntax Symbol Guard := .node [.mk ("pair", .top) constrained [leaf,leaf]]
private def productive : Syntax Symbol Guard := .binder false (.node [
  .mk ("leaf", .top) plain [], .mk ("step", .top) plain [.var 0]])
private def unselected : Syntax Symbol Guard := .binder false (.node [.mk ("bad", .top) constrained [.var 0,.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("root", .top) plain [finite,productive,unselected]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def input : Node := match built with | .done value _ => value | .pending .. => .empty
private def initial : Heap := built.state
private theorem built_done : built = .done input initial := by cbv
private def entries : List (Int × Needed) := [(0,.node [(0,.node [])]), (1,.node [(0,.node [])])]
private def needed : Needed := .node entries
private def run := SourceEqualityRequiredWorker.require 8 16 needed input initial
private def output : Node := match run with | .done value _ => value | _ => .empty
private def final : Heap := match run with | .done _ state | .pending _ state | .unresolved _ state | .exhausted _ state => state
private theorem run_done : run = .done output final := by cbv
private def rootRow : Edge := (nodeEdges input).head!
private def finiteValue : Node := rootRow.children[0]!
private def productiveValue : Node := rootRow.children[1]!
private def untouchedValue : Node := rootRow.children[2]!
private def returnedRoot : Edge := (nodeEdges output).head!
private def returnedFinite : Node := returnedRoot.children[0]!
private def returnedRow : Edge := (nodeEdges returnedFinite).head!

private theorem shallow_safe (entry) (rows : List Edge) (level free) :
    ExposureSafe (.node [(0,.node [])]) (.node entry rows level free) := by
  apply ExposureSafe.ordinary
  intro row member index childNeeded found child selected
  have present := SourceEqualityNeededMap.lookup_mem _ _ _ found
  simp only [List.mem_singleton, Prod.mk.injEq] at present
  obtain ⟨_, rfl⟩ := present
  exact .identity child

private theorem input_safe : ExposureSafe needed input := by
  have shape : ∃ entry rows level free, input = .node entry rows level free := by cbv; exact ⟨_,_,_,_,rfl⟩
  obtain ⟨entry, rows, level, free, shape⟩ := shape
  rw [shape]
  apply ExposureSafe.ordinary
  intro row member index childNeeded found child selected
  have present := SourceEqualityNeededMap.lookup_mem _ _ _ found
  simp only [entries, List.mem_cons, List.mem_singleton, Prod.mk.injEq] at present
  rcases present with ⟨indexEq,rfl⟩ | ⟨indexEq,rfl⟩
  · have idx : index = 0 := by omega
    subst index
    have childEq : child = finiteValue := by
      have rowsEq : rows = nodeEdges input := by rw [shape]; rfl
      rw [rowsEq] at member
      have rowEq : row = rootRow := by simpa only [input, built, expression, finite, productive, unselected, leaf, plain, constrained] using member
      subst row
      exact (Option.some.inj (selected.symm.trans (by cbv))).symm
    subst child
    have finiteShape : ∃ e r d f, finiteValue = .node e r d f := by cbv; exact ⟨_,_,_,_,rfl⟩
    obtain ⟨e,r,d,f,eq⟩ := finiteShape
    rw [eq]
    exact shallow_safe e r d f
  · have idx : index = 1 := by omega
    subst index
    have rowsEq : rows = nodeEdges input := by rw [shape]; rfl
    rw [rowsEq] at member
    have rowEq : row = rootRow := by simpa only [input, built, expression, finite, productive, unselected, leaf, plain, constrained] using member
    subst row
    have childEq : child = productiveValue := (Option.some.inj (selected.symm.trans (by cbv))).symm
    subst child
    exact .accepted _ _ (by cbv)

private theorem constructed_proof :
    ∃ (program : Syntax Symbol Guard) (before after : Heap) (original result : Node) (request : Needed) (row : Edge),
      InternedFreshOrdinaryConstruction.build program [] empty = .done original before ∧
      SourceEqualityRequiredWorker.require 8 16 request original before = .done result after ∧
      SourceEqualityRequiredGraph.RequireNode request original before result after ∧
      Origin original result ∧ RowAt result [.child 0 0] 0 row ∧
      SourceMemoGate.plain row.entry.key.constraint = false ∧
      (∃ sourcePath sourceIndex sourceRow, RowAt original sourcePath sourceIndex sourceRow ∧
        SourceCurrentRequiredGuardOrigins.RowOrigin sourceRow row) ∧
      SourceMemoGate.unconstrained untouchedValue = false ∧
      returnedRoot.children[2]? = some untouchedValue := by
  have actual := SourceEqualityRequiredWorkerSound.require_graph 8 16 needed input initial output final run_done
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression input initial built_done
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result input initial built_done
  have costs : InternedFreshOrdinaryCostHeap.Heap initial := by
    simpa only [built_done, Outcome.state] using InternedFreshOrdinaryCosts.closed_heap expression
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain initial := by
    simpa only [built_done, Outcome.state] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
  have origin := SourceCurrentRequiredRowOrigins.node actual semantic costs available guards input_safe
  have occurrence : RowAt output [.child 0 0] 0 returnedRow :=
    .child 0 0 returnedRoot returnedFinite (by cbv) (by cbv) (.root (by cbv))
  have nonplain : SourceMemoGate.plain returnedRow.entry.key.constraint = false := by cbv
  exact ⟨expression, initial, final, input, output, needed, returnedRow, built_done, run_done, actual,
    origin, occurrence, nonplain, origin.nonplain occurrence nonplain, by cbv, by cbv⟩

/-- An actual recursive Required run retains a nested positive row and leaves an unselected constrained Mu unchanged. -/
theorem constructed :
    ∃ (program : Syntax Symbol Guard) (before after : Heap) (original result : Node) (request : Needed) (row : Edge),
      InternedFreshOrdinaryConstruction.build program [] empty = .done original before ∧
      SourceEqualityRequiredWorker.require 8 16 request original before = .done result after ∧
      SourceEqualityRequiredGraph.RequireNode request original before result after ∧
      Origin original result ∧ RowAt result [.child 0 0] 0 row ∧
      SourceMemoGate.plain row.entry.key.constraint = false ∧
      (∃ sourcePath sourceIndex sourceRow, RowAt original sourcePath sourceIndex sourceRow ∧
        SourceCurrentRequiredGuardOrigins.RowOrigin sourceRow row) ∧
      SourceMemoGate.unconstrained untouchedValue = false ∧
      returnedRoot.children[2]? = some untouchedValue := constructed_proof

end MicroCFTA.RequiredRowOriginKernels
#check @MicroCFTA.RequiredRowOriginKernels.constructed
#print MicroCFTA.RequiredRowOriginKernels.constructed
#print axioms MicroCFTA.RequiredRowOriginKernels.constructed
