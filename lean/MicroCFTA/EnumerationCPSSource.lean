import MicroCFTA.EnumerationCPSRuns

/-!
# Recover the actual source protocol from checked execution

The source view omits model-error rows. The checked runner remains available
and records those rows. Recovery of the whole result list requires ErrorFree;
without it, the source view has only a successful-support theorem.
-/

namespace MicroCFTA.EnumerationCPSSource

variable {State Error α β : Type}

/-- Read the successful continuation of a checked action through the source type. -/
def sourceView (action : EnumerationCPSChecked.Computation State Error α) :
    EnumerationCPS.Computation State α :=
  fun state success later => action state success (fun _ rest => rest) later

/-- The source view of a finite checked computation keeps successes in their original order. -/
theorem sourceView_exact (action : EnumerationCPSChecked.Computation State Error α)
    (rows : EnumerationCPSChecked.Rows State Error α)
    (represented : EnumerationCPSChecked.Represents action rows) :
    EnumerationCPS.Represents (sourceView action)
      (fun state => EnumerationCPSChecked.successes (rows state)) := by
  rw [represented]
  unfold EnumerationCPS.Represents sourceView EnumerationCPSChecked.encode
    EnumerationCPS.encode EnumerationCPSChecked.successes
  funext Result state success later
  dsimp only
  induction rows state with
  | nil => rfl
  | cons first rest ih => cases first <;> simp [EnumerationCPSChecked.fold, ih]

/-- Source bind is the successful continuation of checked bind, with the same local state. -/
theorem sourceView_bind (action : EnumerationCPSChecked.Computation State Error α)
    (next : α → EnumerationCPSChecked.Computation State Error β) :
    @sourceView State Error β (EnumerationCPSChecked.bind action next) =
      @EnumerationCPS.bind State α β (sourceView action) (fun value => sourceView (next value)) := rfl

/-- Source choice retains the same original state for both alternatives. -/
theorem sourceView_choice (left right : EnumerationCPSChecked.Computation State Error α) :
    @sourceView State Error α (EnumerationCPSChecked.choice left right) =
      @EnumerationCPS.choice State α (sourceView left) (sourceView right) := rfl

/-- Source state unpacks the same completed state pair. -/
theorem sourceView_state (change : State → α × State) :
    @sourceView State Error α (EnumerationCPSChecked.state change) = @EnumerationCPS.state State α change := rfl

/-- Finite branch choice retains the same order and initial state. -/
theorem sourceView_branches (values : List α) :
    @sourceView State Error α (EnumerationCPSChecked.branches values) = @EnumerationCPS.branches State α values := rfl

/-- Source pure retains one unchanged-state branch. -/
theorem sourceView_pure (value : α) :
    @sourceView State Error α (EnumerationCPSChecked.pure value) = @EnumerationCPS.pure State α value := rfl

/-- The source ordinary failure keeps the later branches. -/
theorem sourceView_reject :
    @sourceView State Error α EnumerationCPSChecked.reject = @EnumerationCPS.failure State α := rfl

/-- The current source allBranches runner returns precisely the successful checked rows. -/
theorem allBranches_sourceView (action : EnumerationCPSChecked.Computation State Error α)
    (rows : EnumerationCPSChecked.Rows State Error α)
    (represented : EnumerationCPSChecked.Represents action rows) (state : State) :
    EnumerationCPS.allBranches (sourceView action) state = EnumerationCPSChecked.successes (rows state) :=
  EnumerationCPS.allBranches_exact _ _ (sourceView_exact action rows represented) state

/-- Error-free execution is exactly the condition needed for lossless source-runner recovery. -/
theorem error_free_recovery (action : EnumerationCPSChecked.Computation State Error α)
    (rows : EnumerationCPSChecked.Rows State Error α)
    (represented : EnumerationCPSChecked.Represents action rows) (state : State)
    (safe : EnumerationCPSChecked.ErrorFree (rows state)) :
    (EnumerationCPS.allBranches (sourceView action) state).map Except.ok = rows state := by
  rw [allBranches_sourceView action rows represented state]
  exact EnumerationCPSChecked.successes_recover _ safe

/-- The source-typed public action uses the checked algebraic worker translation. -/
def runs (graph : EnumerationState.Graph Symbol Guard) (marker : Symbol) (fuel root : Nat) :=
  EnumerationCPS.allBranches (sourceView (EnumerationCPSRuns.action graph marker fuel))
    (EnumerationState.initial root)

/-- Public source-protocol execution preserves each successful branch's order and state. -/
theorem runs_eq (graph : EnumerationState.Graph Symbol Guard) (marker : Symbol) (fuel root : Nat) :
    runs graph marker fuel root = EnumerationCPSRuns.successfulRuns graph marker fuel root := by
  rw [runs, allBranches_sourceView _ _ (EnumerationCPSRuns.action_exact graph marker fuel)]
  unfold EnumerationCPSRuns.successfulRuns
  rw [EnumerationCPSRuns.runs_eq]
  rfl

/-- The source-protocol runner inherits exact residual-checked accepted support. -/
theorem runs_exact (graph : EnumerationState.Graph Symbol Guard)
    (meaning : Guard → Language.Term Symbol → Prop) (complete : EnumerationSemantics.CompleteGraph graph)
    (correct : EnumerationCorrectness.IntersectionCorrect graph (EnumerationCorrectness.Accepted graph meaning))
    (marker : Symbol) (root : Nat) (term : Language.Term Symbol) :
    EnumerationCorrectness.Accepted graph meaning root term ↔
      ∃ fuel pending after, ((term, pending), after) ∈ runs graph marker fuel root ∧
        ∀ obligation ∈ pending, meaning obligation.1 obligation.2 := by
  simp only [runs_eq]
  exact EnumerationCPSRuns.successfulRuns_exact graph meaning complete correct marker root term

/-- A bound error is visible in checked execution even when its source view has no success. -/
theorem fuel_error_is_not_rejection (graph : EnumerationState.Graph Symbol Guard)
    (scs : List EnumerationState.Suspended) (node : Nat) (state : EnumerationState.State Symbol Guard) :
    EnumerationCPSChecked.allResults
      (EnumerationCPSState.lift (EnumerationState.enumerateNode graph 0 scs node)) state =
        [.error EnumerationState.Error.fuelExhausted] := by
  rw [EnumerationCPSChecked.allResults_exact _ _ (EnumerationCPSState.lift_exact _)]
  rfl

end MicroCFTA.EnumerationCPSSource
