import MicroCFTA.SourceCurrentPrimaryRootSupport
import MicroCFTA.SourceCurrentAllocatedRecordScanWorker

/-!
# Root support of original values selected by actual record scans

Every retained record comes from an actual false primary observation.
The original forest does not change during scanning. Root support depends
only on the selected value, so no heap or memo invariant is required.
This theorem does not certify later edited values or prove completion.
-/
namespace MicroCFTA.SourceCurrentSelectedRootOrigins
open InternedConstructorTemplates SourceEqualityClassOrder
open SourceCurrentAllocatedRecordScanWorker (scan select)
open SourceCurrentAllocatedScanWorker (gate query decision)
open SourceCurrentActualRequiredRowOrigins (Root)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Outcome" => SourceCurrentAllocatedScanWorker.Outcome
variable {width : Nat}

private theorem bind_done {A B : Type} (first : Outcome A width)
    (next : A → Checked width → SourceCurrentEmptinessMemo.Memo → Outcome B width)
    {output : B} {after : Checked width} {saved : SourceCurrentEmptinessMemo.Memo}
    (actual : first.bind next = .done output after saved) :
    ∃ value middle memo, first = .done value middle memo ∧ next value middle memo = .done output after saved := by
  cases first with
  | done value middle memo => exact ⟨value,middle,memo,rfl,actual⟩
  | failed => cases actual

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem gate_false {g values paths memo current} {before middle : Checked width}
    (actual : gate true g values paths before memo = .done false middle current) :
    SourceCurrentAllocatedGateWorker.primary g values paths before = .done false middle := by
  cases observed : SourceCurrentAllocatedGateWorker.primary g values paths before with
  | failed => simp only [gate,ite_true,observed] at actual; cases actual
  | done answer after =>
    simp only [gate,ite_true,observed] at actual
    cases actual
    rfl

/-- A retained literal record has an actual false primary observation at its reached checked states. -/
theorem selected_primary {g s p h n budget values records memo outcome kept saved} {before after : Checked width}
    (actual : scan g s p h n budget values records before memo = .done (outcome,kept) after saved)
    {record : Record} (retained : record ∈ kept) :
    record ∈ records ∧ ∃ start finish : Checked width,
      SourceCurrentAllocatedGateWorker.primary g values record.paths start = .done false finish := by
  induction records generalizing before memo outcome kept after saved with
  | nil => cases actual; cases retained
  | cons first records ih =>
    obtain ⟨primary,middle,current,gateDone,later⟩ := bind_done _ _ (by simpa only [scan] using actual)
    cases primary with
    | false =>
      simp only [Bool.false_eq_true,ite_false] at later
      cases tailDone : scan g s p h n budget values records middle current with
      | failed => simp only [tailDone,select] at later; cases later
      | done result final completed =>
        cases result with
        | mk stopped selected =>
          simp only [tailDone,select] at later
          cases later
          rcases List.mem_cons.mp retained with rfl | retained
          · exact ⟨List.mem_cons_self,before,middle,gate_false gateDone⟩
          · obtain ⟨member,start,finish,called⟩ := ih tailDone retained
            exact ⟨List.mem_cons_of_mem _ member,start,finish,called⟩
    | true =>
      simp only [ite_true] at later
      obtain ⟨secondary,next,warm,gateDone,later⟩ := bind_done _ _ later
      cases secondary with
      | true =>
        simp only [ite_true] at later
        obtain ⟨member,start,finish,called⟩ := ih later retained
        exact ⟨List.mem_cons_of_mem _ member,start,finish,called⟩
      | false =>
        simp only [Bool.false_eq_true,ite_false] at later
        obtain ⟨value,queried,fourth,queryDone,later⟩ := bind_done _ _ later
        obtain ⟨answer,decided,final,decisionDone,later⟩ := bind_done _ _ later
        cases answer with
        | true => simp only [ite_true] at later; cases later; cases retained
        | false =>
          simp only [Bool.false_eq_true,ite_false] at later
          obtain ⟨member,start,finish,called⟩ := ih later retained
          exact ⟨List.mem_cons_of_mem _ member,start,finish,called⟩

/-- A present original slot selected by a retained record has supported root shape. -/
theorem selected_root {g s p h n budget values records memo outcome kept saved} {before after : Checked width}
    (actual : scan g s p h n budget values records before memo = .done (outcome,kept) after saved)
    {record : Record} (retained : record ∈ kept) {index : Nat} {suffix : EqualityNormalize.Path}
    (member : index :: suffix ∈ record.paths) {value : Node} (found : values[index]? = some value) : Root value := by
  obtain ⟨_,start,finish,primary⟩ := selected_primary (width := width) actual retained
  exact SourceCurrentPrimaryRootSupport.primary primary member found

end MicroCFTA.SourceCurrentSelectedRootOrigins
