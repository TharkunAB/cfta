import MicroCFTA.SourceEqualityOnePassWorker

/-!
# Guarded native one-pass worker and graph agreement

Successful checked workers derive literal source graphs. Complete graphs
supply six finite stable bounds. Required paths and target projection share
one bound; their head reads share another. Every larger tuple retains the
same answer and full native state. Array normalization agrees eventually.
-/
namespace MicroCFTA.SourceEqualityOnePassWorkerProofs
open InternedConstructorTemplates SourceEqualityClassFoldGraph
open InternedNestedConstruction (Outcome)
open SourceEqualityOnePassGraph SourceEqualityOnePassWorker

/-- Six finite bounds give identical source answers and full native states at every larger tuple. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Result width Symbol Guard)
    (answer : Except String (List (Value Symbol Guard))) (after : NativeState width Symbol Guard) : Prop :=
  ∃ gate edit projection head comparison native, ∀ g e p h c n,
    gate ≤ g → edit ≤ e → projection ≤ p → head ≤ h → comparison ≤ c → native ≤ n → evaluation g e p h c n = .done answer after

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (unconstrained : Value Symbol Guard → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)

/-- Successful checked live execution contains the actual physical selection, required paths, and native fold. -/
theorem live_graph (g e p h c n : Nat) (records : List SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) (ranges : Ranges unconstrained emptyGuard conjoin clear top (.ok (.classes records)) values before)
    (answer : Except String (List (Value Symbol Guard))) (after : NativeState width Symbol Guard)
    (done : live unconstrained emptyGuard conjoin clear top g e p h c n records values before = .done answer after) :
    Graph unconstrained emptyGuard conjoin clear top (.ok (.classes records)) values before answer after := by
  cases selection : SourceEqualityRecordSelectionWorker.queries unconstrained g values records before.machine.heap with
  | pending => simp only [live, selection] at done; cases done
  | done output middle =>
      cases output with
      | none => simp only [live, selection] at done; cases done
      | some queries =>
          cases required : SourceEqualityRequiredExecution.requireAll p h (SourceEqualitySelectedRequired.paths (InternedSourceClassSelection.selected queries)) values middle with
          | pending | unresolved | exhausted => simp only [live, selection, required] at done; cases done
          | done current heap =>
              have stages : SourceEqualitySelectedRequired.Execution unconstrained values (records.map SourceEqualityClassOrder.Record.paths)
                  before.machine.heap queries middle current heap :=
                ⟨SourceEqualityRecordSelectionProofs.queries_graph unconstrained g values records before.machine.heap queries middle selection, p, h, required⟩
              cases folded : SourceEqualityClassFoldWorker.pass emptyGuard conjoin clear top e p h c n
                  (SourceEqualitySelectedRecords.keep records queries) current (SourceEqualityNativeScoped.advanceHeap before heap) with
              | incomplete => simp only [live, selection, required, folded, finish] at done; cases done
              | done results native =>
                  simp only [live, selection, required, folded, finish] at done
                  have parts := Result.done.inj done
                  cases parts.1; cases parts.2
                  exact .live rfl ⟨stages, SourceEqualityClassFoldWorkerProofs.pass_graph emptyGuard conjoin clear top e p h c n _ current _
                    (ranges queries middle current heap stages) results _ folded⟩

/-- Every successful checked one-pass worker derives its exact source branch and complete graph. -/
theorem checked_graph (g e p h c n : Nat) (checked : Except String SourceEqualityPrecheck.Branch) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) (ranges : Ranges unconstrained emptyGuard conjoin clear top checked values before)
    (answer : Except String (List (Value Symbol Guard))) (after : NativeState width Symbol Guard)
    (done : runChecked unconstrained emptyGuard conjoin clear top g e p h c n checked values before = .done answer after) :
    Graph unconstrained emptyGuard conjoin clear top checked values before answer after := by
  cases checked with
  | error message =>
      have parts := Result.done.inj done
      cases parts.1; cases parts.2; exact .error rfl
  | ok branch =>
      cases branch with
      | unchanged =>
          have parts := Result.done.inj done
          cases parts.1; cases parts.2; exact .unchanged rfl
      | emptyChildren =>
          have parts := Result.done.inj done
          cases parts.1; cases parts.2; exact .emptyChildren rfl
      | classes records => exact live_graph unconstrained emptyGuard conjoin clear top g e p h c n records values before ranges answer after done

omit [DecidableEq Symbol] in
/-- Actual completed required-path source receipts supply stable independent worker and head bounds. -/
theorem required_stable (paths : List SourceEqualityNeeded.Path) (values : List (Value Symbol Guard))
    (before : InternedConstructorTemplates.State Symbol Guard) (results : List (Value Symbol Guard)) (after : InternedConstructorTemplates.State Symbol Guard)
    (actual : ∃ fuel readFuel, SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after) :
    SourceEqualityRequiredWorkerComplete.StableRun (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before) results after := by
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr actual
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      have trace : SourceEqualityRequiredGraph.RequireChildren entries 0 values before results after := by simpa only [compiled] using graph
      simpa only [SourceEqualityRequiredExecution.requireAll, compiled] using SourceEqualityRequiredWorkerComplete.children_stable trace

/-- Every complete actual live graph has finite stable execution across all six independent stage bounds. -/
theorem live_stable {records values before queries middle required heap results after}
    (stages : SourceEqualitySelectedClassFold.Execution unconstrained emptyGuard conjoin clear top records values
      (before : NativeState width Symbol Guard) queries middle required heap results after) :
    StableRun (fun g e p h c n => live unconstrained emptyGuard conjoin clear top g e p h c n records values before) (.ok results) after := by
  obtain ⟨gateBound, gateStable⟩ := SourceEqualityRecordSelectionProofs.queries_stable unconstrained values records before.machine.heap queries middle stages.stages.selection
  obtain ⟨requiredBound, requiredHead, requiredStable⟩ := required_stable _ values middle required heap stages.stages.required
  obtain ⟨editBound, projectionBound, headBound, comparisonBound, nativeBound, foldStable⟩ :=
    SourceEqualityClassFoldWorkerProofs.pass_stable emptyGuard conjoin clear top stages.narrowed
  refine ⟨gateBound, editBound, max requiredBound projectionBound, max requiredHead headBound, comparisonBound, nativeBound, ?_⟩
  intro g e p h c n eg ee ep eh ec en
  have first := gateStable g eg
  have second := requiredStable p h (Nat.le_trans (Nat.le_max_left _ _) ep) (Nat.le_trans (Nat.le_max_left _ _) eh)
  have last := foldStable e p h c n ee (Nat.le_trans (Nat.le_max_right _ _) ep) (Nat.le_trans (Nat.le_max_right _ _) eh) ec en
  simp only [live, first, second, last, finish]

/-- Every complete checked graph supplies finite stable identical answers and complete native states. -/
theorem checked_stable {checked values before answer after}
    (trace : Graph unconstrained emptyGuard conjoin clear top checked values (before : NativeState width Symbol Guard) answer after) :
    StableRun (fun g e p h c n => runChecked unconstrained emptyGuard conjoin clear top g e p h c n checked values before) answer after := by
  cases trace with
  | error actual => exact ⟨0, 0, 0, 0, 0, 0, by intros; simp only [actual, runChecked]⟩
  | unchanged actual => exact ⟨0, 0, 0, 0, 0, 0, by intros; simp only [actual, runChecked]⟩
  | emptyChildren actual => exact ⟨0, 0, 0, 0, 0, 0, by intros; simp only [actual, runChecked]⟩
  | live actual stages =>
      simpa only [actual, runChecked] using live_stable unconstrained emptyGuard conjoin clear top stages

/-- All sufficiently large actual array bounds give the same complete one-pass worker at every stage tuple. -/
theorem array_eventual (own inherited : SourceEqualityPrecheck.Constraint) :
    ∃ bound, ∀ work, bound ≤ work → ∀ g e p h c n values (before : NativeState width Symbol Guard),
      runArray unconstrained emptyGuard conjoin clear top work g e p h c n own inherited values before =
        run unconstrained emptyGuard conjoin clear top g e p h c n own inherited values before := by
  obtain ⟨bound, agrees⟩ := SourceEqualityPrecheck.precheckArray_eventual own inherited
  exact ⟨bound, by intro work enough g e p h c n values before; simp only [runArray, SourceEqualityOnePassWorker.run, agrees work enough]⟩

end MicroCFTA.SourceEqualityOnePassWorkerProofs
