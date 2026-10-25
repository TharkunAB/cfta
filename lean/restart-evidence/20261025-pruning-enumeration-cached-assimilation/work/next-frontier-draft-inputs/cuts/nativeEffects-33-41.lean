theorem execute_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (fuel : Nat) (control : Control Output) (state : Checked width)
    (native : SourceEqualityNativeDemandProvenance.Valid holds state.native) (ready : Ready (physical state))
    (fields : SourceCurrentAllocatedNativeFieldClosure.Fields control state)
    (inputs : SourceEqualityNativeDemandFieldExecution.InputsThrough holds fuel control state) :
    Effects (physical state) (physical (execute fuel control state).state) ∧
      SourceEqualityNativeDemandProvenance.Valid holds (execute fuel control state).state.native ∧
      SourceRecursiveIntersectionKernel.Extension state.native.machine (execute fuel control state).state.native.machine ∧
      SourceCurrentAllocatedNativeFieldClosure.OutcomeFields (execute fuel control state) := by
