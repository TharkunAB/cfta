import MicroCFTA.SourceCurrentParentOperationInvariants
import MicroCFTA.SourceCurrentAllocatedRecordScanWorker
import MicroCFTA.SourceCurrentRequiredPrimaryExposure

/-!
# False primary gates from literal selected records

A completed record scan supplies the actual false primary gate for each
selected record. Actual singleton prefixes supply physical facts for the
next stage. The gate replays at the final scan heap for the original forest.
No semantic read graph or future outer return is an input.
-/
namespace MicroCFTA.SourceCurrentSelectedPrimaryOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentLowerOperationInvariants (Effect)
open SourceCurrentAllocatedRecordScanWorker (scan select)
open SourceCurrentAllocatedScanWorker (Outcome gate query decision)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "ClassTrace" => EndpointStatefulGateTrace.ClassTrace source reaches
local notation "PathTrace" => EndpointStatefulGateTrace.PathTrace source reaches
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

private theorem bind_done {A B : Type}
    (first : Outcome A width) (next : A → Checked width → Fourth → Outcome B width)
    {result : B} {after : Checked width} {saved : Fourth}
    (actual : first.bind next = .done result after saved) :
    ∃ value middle current, first = .done value middle current ∧ next value middle current = .done result after saved := by
  cases first with
  | done value middle current => exact ⟨value,middle,current,rfl,actual⟩
  | failed => cases actual

private theorem effects {g s p h n budget values records before fourth result after saved}
    (actual : scan g s p h n budget values records before fourth = .done result after saved)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) : Effect before after := by
  have mapped := (SourceCurrentAllocatedRecordScanWorker.scan_mapPaths g s p h n budget values records before fourth).symm
  rw [actual] at mapped
  exact SourceCurrentParentOperationInvariants.scan mapped good available

private theorem primary_trace {g values paths before fourth after saved}
    (actual : gate true g values paths before fourth = .done false after saved) :
    ClassTrace values paths (before : Checked width).native.machine.heap false after.native.machine.heap := by
  cases returned : SourceCurrentAllocatedGateWorker.primary g values paths before with
  | failed => simp only [gate,ite_true,returned] at actual; cases actual
  | done answer current =>
    simp only [gate,ite_true,returned] at actual
    cases actual
    exact SourceCurrentAllocatedGateWorker.primary_graph returned

/-- Every selected record has its false primary class trace at the actual final scan heap. -/
theorem selected_class {g s p h n budget values records stopped kept before fourth after saved}
    (actual : scan g s p h n budget values records before fourth = .done (stopped,kept) after saved)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    ∀ record ∈ kept, ClassTrace values record.paths after.native.machine.heap false after.native.machine.heap := by
  induction records generalizing stopped kept before fourth after saved with
  | nil => cases actual; intro record impossible; cases impossible
  | cons record records ih =>
    obtain ⟨primary,middle,current,first,later⟩ := bind_done _ _ actual
    cases primary with
    | false =>
      have prefix : scan g s p h n budget values [record] before fourth = .done (none,[record]) middle current := by
        simp only [scan,first,Outcome.bind,Bool.false_eq_true,ite_false,select]
      have physical := effects prefix good available
      have known : Values middle.native.machine.heap values :=
        fun value member => physical.keeps.available value (available value member)
      simp only [Bool.false_eq_true,ite_false] at later
      cases returned : scan g s p h n budget values records middle current with
      | failed => simp only [returned,select] at later; cases later
      | done result checked completed =>
        cases result with
        | mk outcome selected =>
          simp only [returned,select] at later
          cases later
          have rest := ih returned physical.good known
          have growth := (effects returned physical.good known).keeps.growth
          have replay := SourceCurrentPrimaryReplay.class_replay source reaches values record.paths
            before.native.machine.heap false middle.native.machine.heap (primary_trace first) good.semantic available
          intro chosen member
          rcases List.mem_cons.mp member with rfl | tail
          · exact replay.2.2 checked.native.machine.heap growth
          · exact rest chosen tail
    | true =>
      simp only [ite_true] at later
      obtain ⟨secondary,last,completed,second,later⟩ := bind_done _ _ later
      cases secondary with
      | true =>
        have prefix : scan g s p h n budget values [record] before fourth = .done (none,[]) last completed := by
          simp only [scan,first,Outcome.bind,ite_true,second]
        have physical := effects prefix good available
        exact ih later physical.good (fun value member => physical.keeps.available value (available value member))
      | false =>
        simp only [Bool.false_eq_true,ite_false] at later
        obtain ⟨value,queried,next,queryDone,later⟩ := bind_done _ _ later
        obtain ⟨answer,decided,final,decisionDone,later⟩ := bind_done _ _ later
        have prefix : scan g s p h n budget values [record] before fourth =
            .done ((if answer then some record.paths else none),[]) decided final := by
          simp only [scan,first,Outcome.bind,ite_true,second,Bool.false_eq_true,ite_false,queryDone,decisionDone]
          cases answer <;> rfl
        have physical := effects prefix good available
        cases answer with
        | true => cases later; intro chosen impossible; cases impossible
        | false =>
          exact ih later physical.good (fun value member => physical.keeps.available value (available value member))

/-- Each selected path retains a false primary certificate for the original forest. -/
theorem selected_path {g s p h n budget values records stopped kept before fourth after saved}
    (actual : scan g s p h n budget values records before fourth = .done (stopped,kept) after saved)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values)
    {record : SourceEqualityClassOrder.Record} (selected : record ∈ kept)
    {path : EqualityNormalize.Path} (member : path ∈ record.paths) :
    PathTrace values path after.native.machine.heap false after.native.machine.heap := by
  have physical := effects actual good available
  exact SourceCurrentRequiredPrimaryExposure.false_class_paths values record.paths
    after.native.machine.heap after.native.machine.heap (selected_class actual good available record selected)
    physical.good.semantic (fun value member => physical.keeps.available value (available value member))
    after.native.machine.heap (grows_refl _) path member

end MicroCFTA.SourceCurrentSelectedPrimaryOrigins
