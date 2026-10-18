import MicroCFTA.SourceCurrentClassPositionalFootprints
import MicroCFTA.SourceEqualityPhysicalPayload
import MicroCFTA.SourceEqualityPCSNativeEdge
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.GlobalFootprintCheck
noncomputable section
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
private def first : Guard := ⟨some [[[0],[1]]],.same [] [0]⟩
private def second : Guard := ⟨some [],.or [.top]⟩
private def joined : Guard := SourceEqualityPCSNativeEdge.conjoin first second
private def record : SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩
private def Footprint (guard : Guard) : Prop := ∀ records : List SourceEqualityClassOrder.Record,
  SourceEqualityPhysicalPayload.own guard = .ok (some records) →
    ∀ record ∈ records, SourceCurrentClassPositionalFootprints.Unselected record 1 1
private theorem record_paths : record.paths = [[0],[1]] := by cbv
private theorem coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual,done,checked,_⟩ := SourceEqualityClassOrder.recordOf_complete [[0],[1]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp ⟨.branch [(0,.terminal),(1,.terminal)],by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans (by cbv))
  exact same ▸ checked
private theorem first_own : SourceEqualityPhysicalPayload.own first = .ok none := by cbv
private theorem second_own : SourceEqualityPhysicalPayload.own second = .ok (some []) := by cbv
private theorem joined_own : SourceEqualityPhysicalPayload.own joined = .ok (some [record]) := by cbv
private theorem first_footprint : Footprint first := by
  intro records found
  rw [first_own] at found
  cases found
private theorem second_footprint : Footprint second := by
  intro records found
  rw [second_own] at found
  cases Option.some.inj (Except.ok.inj found)
  intro record impossible
  cases impossible
private theorem not_joined : ¬ Footprint joined := by
  intro good
  have footprint := good [record] joined_own record List.mem_cons_self
  have member : [1] ∈ record.paths := by rw [record_paths]; simp
  exact (footprint [1] member).1 ⟨[1],rfl⟩
private theorem first_cached : SourceEqualityGuardReadback.Cached first.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] := by cbv
  intro classes found
  cases found
  exact SourceEqualityGuardReadback.normalized normal
private theorem witness :
    SourceEqualityGuardReadback.Cached first.equalities ∧
    SourceEqualityGuardReadback.Cached second.equalities ∧
    Footprint first ∧ Footprint second ∧ ¬ Footprint joined ∧
    SourceEqualityPhysicalPayload.own first = .ok none ∧
    SourceEqualityPhysicalPayload.own second = .ok (some []) ∧
    SourceEqualityPhysicalPayload.own joined = .ok (some [record]) ∧
    SourceEqualityClassOrder.Coherent record ∧ record.paths = [[0],[1]] :=
  ⟨first_cached,SourceEqualityGuardReadback.empty_cached,first_footprint,second_footprint,
    not_joined,first_own,second_own,joined_own,coherent,record_paths⟩
/-- Actual native guard conjunction can expose a stored class that both input accessors conceal. -/
theorem accessor_footprint_not_closed :
    SourceEqualityGuardReadback.Cached first.equalities ∧
    SourceEqualityGuardReadback.Cached second.equalities ∧
    Footprint first ∧ Footprint second ∧ ¬ Footprint joined ∧
    SourceEqualityPhysicalPayload.own first = .ok none ∧
    SourceEqualityPhysicalPayload.own second = .ok (some []) ∧
    SourceEqualityPhysicalPayload.own joined = .ok (some [record]) ∧
    SourceEqualityClassOrder.Coherent record ∧ record.paths = [[0],[1]] := witness
end
end MicroCFTA.GlobalFootprintCheck
