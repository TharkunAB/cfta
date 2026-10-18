import MicroCFTA.SourceCurrentActualParentRowOrigins
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.ScheduleFootprintCheck
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
noncomputable section
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def top : Guard := ⟨some [],.top⟩
private def positive : Guard := ⟨some [[[0],[1]]],.top⟩
private def tau : Syntax Symbol Guard := .binder true (.node
  [.mk ("leaf",.top) top [],.mk ("loop",.top) top [.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("outer",.top) top
  [tau,.node [.mk ("pair",.top) positive [tau,tau]]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def nested : Node := (children root)[1]?.getD .empty
private def outerRow : EdgeValue Symbol Guard := (nodeEdges root)[0]?.getD
  (run (makeEdge ("outer",.top) top []) heap).1
private def nestedRow : EdgeValue Symbol Guard := (nodeEdges nested)[0]?.getD
  (run (makeEdge ("pair",.top) positive []) heap).1
private def record : SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩
private theorem built_done : built = .done root heap := by cbv
private theorem record_paths : record.paths = [[0],[1]] := by cbv
private theorem coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual,done,checked,_⟩ := SourceEqualityClassOrder.recordOf_complete [[0],[1]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp ⟨.branch [(0,.terminal),(1,.terminal)],by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans (by cbv))
  exact same ▸ checked
private theorem bad_footprint : ¬ SourceCurrentClassPositionalFootprints.Unselected record 1 1 := by
  intro footprint
  have member : [1] ∈ record.paths := by rw [record_paths]; simp
  exact (footprint [1] member).1 ⟨[1],rfl⟩
private theorem outer_own : SourceEqualityPhysicalPayload.own outerRow.entry.key.constraint = .ok (some []) := by cbv
private theorem outer_footprint : ∀ records : List SourceEqualityClassOrder.Record,
    SourceEqualityPhysicalPayload.own outerRow.entry.key.constraint = .ok (some records) →
      ∀ record ∈ records, SourceCurrentClassPositionalFootprints.Unselected record 1 1 := by
  intro records read
  have same : [] = records := Option.some.inj (Except.ok.inj (outer_own.symm.trans read))
  cases same
  intro record impossible
  cases impossible
private theorem nested_own : SourceEqualityPhysicalPayload.own nestedRow.entry.key.constraint = .ok (some [record]) := by cbv
private theorem witness :
    built = .done root heap ∧ InternedNestedFacts.Facts heap ∧ Available heap root ∧
    outerRow ∈ nodeEdges root ∧ outerRow.children[1]? = some nested ∧
    nestedRow ∈ nodeEdges nested ∧
    SourceEqualityPhysicalPayload.own outerRow.entry.key.constraint = .ok (some []) ∧
    (∀ records : List SourceEqualityClassOrder.Record,
      SourceEqualityPhysicalPayload.own outerRow.entry.key.constraint = .ok (some records) →
        ∀ record ∈ records, SourceCurrentClassPositionalFootprints.Unselected record 1 1) ∧
    SourceEqualityPhysicalPayload.own nestedRow.entry.key.constraint = .ok (some [record]) ∧
    record.paths = [[0],[1]] ∧ SourceEqualityClassOrder.Coherent record ∧
    ¬ SourceCurrentClassPositionalFootprints.Unselected record 1 1 := by
  have verified := InternedFreshOrdinaryFacts.closed_verified expression
  have facts : InternedNestedFacts.Facts heap := verified.facts
  have available : Available heap root := verified.result root heap built_done
  have outerMember : outerRow ∈ nodeEdges root := by cbv; exact List.mem_cons_self
  have child : outerRow.children[1]? = some nested := by cbv
  have nestedMember : nestedRow ∈ nodeEdges nested := by cbv; exact List.mem_cons_self
  exact ⟨built_done,facts,available,outerMember,child,nestedMember,outer_own,outer_footprint,
    nested_own,record_paths,coherent,bad_footprint⟩

/-- An actual Top parent can contain a coherent positive row that lacks its continuation footprint. -/
theorem footprint_not_hereditary :
    built = .done root heap ∧ InternedNestedFacts.Facts heap ∧ Available heap root ∧
    outerRow ∈ nodeEdges root ∧ outerRow.children[1]? = some nested ∧
    nestedRow ∈ nodeEdges nested ∧
    SourceEqualityPhysicalPayload.own outerRow.entry.key.constraint = .ok (some []) ∧
    (∀ records : List SourceEqualityClassOrder.Record,
      SourceEqualityPhysicalPayload.own outerRow.entry.key.constraint = .ok (some records) →
        ∀ record ∈ records, SourceCurrentClassPositionalFootprints.Unselected record 1 1) ∧
    SourceEqualityPhysicalPayload.own nestedRow.entry.key.constraint = .ok (some [record]) ∧
    record.paths = [[0],[1]] ∧ SourceEqualityClassOrder.Coherent record ∧
    ¬ SourceCurrentClassPositionalFootprints.Unselected record 1 1 := witness

end
end MicroCFTA.ScheduleFootprintCheck
