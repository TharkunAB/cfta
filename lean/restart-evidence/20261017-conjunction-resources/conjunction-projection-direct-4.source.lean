import MicroCFTA.SourceCurrentConjunctionCompletionReads
import MicroCFTA.SourceCurrentProjectionNumeric

/-!
# Initial resource bounds for conjunction projection jobs

The original maximum path depth, forest length, and job count determine a
uniform scalar schedule. Every actual projection uses the same worker and
reader ceilings. Initial closed input forests construct their own graph.
-/
namespace MicroCFTA.SourceCurrentConjunctionProjectionResources
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph
open SourceEqualityProjectionPathDomain (NodeClosed ForestClosed)
open SourceCurrentConjunctionCompletionReads (Job Inputs Projections Effects)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentProjectionNumericControl (bound)
open SourceCurrentProjectionUnionResources (unionGrowth readFuel)
open SourceCurrentProjectionInitialResources (forestBound)
open HeightOrderControlled (iterate)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- Positive scalar resources make the path envelope monotone in depth. -/
theorem bound_depth_mono {first last : Nat} (increase : first ≤ last) {resource : Nat} (positive : 0 < resource) :
    bound first resource ≤ bound last resource := by
  induction increase with
  | refl => exact Nat.le_refl _
  | @step last increase ih => exact Nat.le_trans ih (SourceCurrentProjectionNumericControl.child_le_bound last positive)

/-- One job pays both the longest proper path and the largest root union. -/
def step (depth count resource : Nat) : Nat := unionGrowth count (bound depth (resource + 1))

/-- The next job retains its initial scalar and a positive unit. -/
theorem step_ge (depth count resource : Nat) : resource + 1 ≤ step depth count resource :=
  Nat.le_trans (SourceCurrentProjectionNumericControl.bound_ge depth (resource + 1)) (SourceCurrentProjectionUnionResources.unionGrowth_ge count _)

/-- Larger initial resources retain the complete one-job envelope. -/
theorem step_mono (depth count : Nat) {first last : Nat} (increase : first ≤ last) :
    step depth count first ≤ step depth count last :=
  SourceCurrentProjectionUnionResources.unionGrowth_mono (Nat.le_refl _)
    (SourceCurrentProjectionNumericControl.bound_mono depth (Nat.add_le_add_right increase 1))

/-- Larger static depth and forest limits retain the one-job envelope. -/
theorem step_limits_mono {firstDepth lastDepth firstCount lastCount : Nat}
    (depths : firstDepth ≤ lastDepth) (counts : firstCount ≤ lastCount) (resource : Nat) :
    step firstDepth firstCount resource ≤ step lastDepth lastCount resource :=
  SourceCurrentProjectionUnionResources.unionGrowth_mono counts (bound_depth_mono depths (by omega))

/-- Any original path and forest below the static limits fit one job step. -/
theorem forestBound_le_step (path : List Int) {depth count actualCount resource : Nat}
    (paths : path.length ≤ depth) (counts : actualCount ≤ count) :
    forestBound path actualCount resource ≤ step depth count resource := by
  cases path with
  | nil =>
      exact SourceCurrentProjectionUnionResources.unionGrowth_mono counts
        (Nat.le_trans (Nat.le_succ resource) (SourceCurrentProjectionNumericControl.bound_ge depth (resource + 1)))
  | cons index rest =>
      exact Nat.le_trans
        (Nat.le_trans (SourceCurrentProjectionNumericControl.bound_mono rest.length (Nat.le_succ resource))
          (bound_depth_mono (by simp only [List.length_cons] at paths; omega) (by omega)))
        (SourceCurrentProjectionUnionResources.unionGrowth_ge count _)

/-- Iterate the same one-job envelope for the initial job count. -/
def jobsBound (depth count jobs resource : Nat) : Nat := iterate (step depth count) jobs resource

/-- The complete job schedule retains its initial scalar. -/
theorem jobsBound_ge (depth count jobs resource : Nat) : resource ≤ jobsBound depth count jobs resource :=
  SourceCurrentMemoMergeNumericControl.iterate_ge _ (fun q => Nat.le_trans (Nat.le_succ q) (step_ge depth count q)) jobs resource

/-- Larger initial resources retain the same fixed job schedule. -/
theorem jobsBound_mono (depth count jobs : Nat) {first last : Nat} (increase : first ≤ last) :
    jobsBound depth count jobs first ≤ jobsBound depth count jobs last :=
  SourceCurrentMemoMergeNumericControl.iterate_mono _ (step_mono depth count) jobs increase

/-- Additional jobs retain every shorter schedule. -/
theorem jobsBound_count_mono (depth count : Nat) {first last : Nat} (increase : first ≤ last) (resource : Nat) :
    jobsBound depth count first resource ≤ jobsBound depth count last resource :=
  SourceCurrentMemoMergeNumericControl.iterate_count_mono _
    (fun q => Nat.le_trans (Nat.le_succ q) (step_ge depth count q)) increase resource

/-- Larger static path and forest limits retain the complete job schedule. -/
theorem jobsBound_limits_mono {firstDepth lastDepth firstCount lastCount : Nat}
    (depths : firstDepth ≤ lastDepth) (counts : firstCount ≤ lastCount) (jobs resource : Nat) :
    jobsBound firstDepth firstCount jobs resource ≤ jobsBound lastDepth lastCount jobs resource :=
  SourceCurrentMemoMergeNumericControl.iterate_compare _ _ (step_mono lastDepth lastCount)
    (step_limits_mono depths counts) jobs (Nat.le_refl _)

/-- A single worker ceiling covers every original path length. -/
def workerFuel (depth : Nat) : Nat := 2 * depth + 1

/-- The final pure scalar bounds every demanded recursive reader. -/
def readerFuel (depth count jobs resource : Nat) : Nat := readFuel (jobsBound depth count jobs resource)

/-- Closed resident values satisfy every finite selected-path closure domain. -/
theorem closed_node_domain (path : List Int) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) : NodeClosed path value := by
  induction path generalizing value with
  | nil => simpa only [NodeClosed] using closed
  | cons index path ih =>
      cases value with
      | empty => simp only [NodeClosed]
      | reference | union | mu => simpa only [NodeClosed] using closed
      | node entry edges depth free =>
          rw [NodeClosed]
          intro edge member child found
          have facts := semantic.ready.semantic.1.normal.facts
          have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
          exact ih child (facts.cached.edges edge.entry.key edge (resident edge member) child (select_member found))
            (MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed edge member child (select_member found))

/-- Closed original forests satisfy the existing selected-path domain for every signed path. -/
theorem closed_forest_domain (path : List Int) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) : ForestClosed path values := by
  cases path with
  | nil => simpa only [ForestClosed] using closed
  | cons index path =>
      rw [ForestClosed]
      intro value found
      exact closed_node_domain path value before semantic (available value (select_member found)) (closed value (select_member found))

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The certificate records each exact intermediate worker return at common numeric fuels. -/
inductive Replay (work reader : Nat) :
    {jobs : List (Job Symbol Guard)} → {before after : State Symbol Guard} → {values : List (Value Symbol Guard)} →
    Projections jobs before values after → Prop where
  /-- Empty jobs emit no worker call. -/
  | nil : Replay work reader (.nil (state := state))
  /-- Each original job uses its exact forest, path, result, and returned heap. -/
  | cons {forest : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
      {before middle after : State Symbol Guard} {value : Value Symbol Guard}
      {jobs : List (Job Symbol Guard)} {values : List (Value Symbol Guard)}
      {first : Forest (path.map Int.ofNat) forest before value middle} {rest : Projections jobs middle values after}
      (enough : SourceCurrentProjectionNumericReplay.workFuel (path.map Int.ofNat) ≤ work)
      (ready : SourceCurrentProjectionNumericReplay.ForestReady reader first)
      (tail : Replay work reader rest) : Replay work reader (.cons first rest)

/-- Independently larger common worker and reader fuels retain every exact intermediate return. -/
theorem Replay.mono {work reader largerWork largerReader : Nat}
    {jobs : List (Job Symbol Guard)} {before after : State Symbol Guard} {values : List (Value Symbol Guard)}
    {actual : Projections jobs before values after} (ready : Replay work reader actual)
    (works : work ≤ largerWork) (reads : reader ≤ largerReader) : Replay largerWork largerReader actual := by
  induction ready with
  | nil => exact .nil
  | @cons forest path before middle after value jobs values first rest enough firstReady tail ih =>
      exact .cons (Nat.le_trans enough works) (firstReady.mono reads) ih

/-- The first retained job executes at the common worker and reader ceilings. -/
theorem Replay.head {work reader : Nat} {forest : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
    {before middle after : State Symbol Guard} {value : Value Symbol Guard}
    {jobs : List (Job Symbol Guard)} {values : List (Value Symbol Guard)}
    {first : Forest (path.map Int.ofNat) forest before value middle} {rest : Projections jobs middle values after}
    (ready : Replay work reader (.cons first rest)) :
    SourceEqualityProjectionWorker.forest work reader (path.map Int.ofNat) forest before = .done value middle := by
  cases ready with
  | cons enough firstReady tail =>
      exact SourceCurrentProjectionNumericReplay.forest_replay firstReady work reader enough (Nat.le_refl _)

/-- The retained tail starts at the exact first job return with the same ceilings. -/
theorem Replay.tail {work reader : Nat} {forest : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
    {before middle after : State Symbol Guard} {value : Value Symbol Guard}
    {jobs : List (Job Symbol Guard)} {values : List (Value Symbol Guard)}
    {first : Forest (path.map Int.ofNat) forest before value middle} {rest : Projections jobs middle values after}
    (ready : Replay work reader (.cons first rest)) : Replay work reader rest := by
  cases ready with
  | cons enough firstReady tail => exact tail

private theorem bound_exact {jobs : List (Job Symbol Guard)} {before after : State Symbol Guard}
    {values : List (Value Symbol Guard)} (actual : Projections jobs before values after)
    (depth count resource : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : Inputs before jobs) (fits : Fits resource before)
    (depths : ∀ job ∈ jobs, job.2.length ≤ depth) (counts : ∀ job ∈ jobs, job.1.length ≤ count) :
    Fits (jobsBound depth count jobs.length resource) after ∧
      Replay (workerFuel depth) (readerFuel depth count jobs.length resource) actual := by
  induction actual generalizing resource with
  | nil => exact ⟨fits, .nil⟩
  | @cons forest path before value middle jobs values after first rest ih =>
      have available := (inputs _ List.mem_cons_self).1
      have domain := closed_forest_domain (path.map Int.ofNat) forest before semantic available (inputs _ List.mem_cons_self).2
      have firstBound := SourceCurrentProjectionInitialResources.forest_bound _ first resource semantic costs available domain fits
      have one := forestBound_le_step (resource := resource) (path.map Int.ofNat) (by simpa only [List.length_map] using depths _ List.mem_cons_self)
        (counts _ List.mem_cons_self)
      have physical := SourceEqualityProjectionCosts.forest_effects first semantic costs available
      have tail := ih (step depth count resource) physical.2.1 physical.2.2.1
        (Inputs.keeps (fun job member => inputs job (List.mem_cons_of_mem _ member)) physical.1)
        (firstBound.1.mono one) (fun job member => depths job (List.mem_cons_of_mem _ member))
        (fun job member => counts job (List.mem_cons_of_mem _ member))
      have widen := Nat.le_trans one (jobsBound_ge depth count jobs.length (step depth count resource))
      have ready := firstBound.2.mono (SourceCurrentProjectionUnionResources.readFuel_mono widen)
      have enough : SourceCurrentProjectionNumericReplay.workFuel (path.map Int.ofNat) ≤ workerFuel depth := by
        have length : path.length ≤ depth := depths (forest, path) List.mem_cons_self
        simp only [SourceCurrentProjectionNumericReplay.workFuel, List.length_map, workerFuel]
        omega
      exact ⟨tail.1, .cons enough ready tail.2⟩

/-- Initial static limits bound the exact complete projection graph and every worker call. -/
theorem Projections.bound {jobs : List (Job Symbol Guard)} {before after : State Symbol Guard}
    {values : List (Value Symbol Guard)} (actual : Projections jobs before values after)
    (depth count jobCount resource : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : Inputs before jobs) (fits : Fits resource before)
    (depths : ∀ job ∈ jobs, job.2.length ≤ depth) (counts : ∀ job ∈ jobs, job.1.length ≤ count)
    (length : jobs.length ≤ jobCount) :
    Fits (jobsBound depth count jobCount resource) after ∧ values.length = jobs.length ∧
      Replay (workerFuel depth) (readerFuel depth count jobCount resource) actual := by
  have checked := bound_exact actual depth count resource semantic costs inputs fits depths counts
  have increase := jobsBound_count_mono depth count length resource
  exact ⟨checked.1.mono increase, actual.length, checked.2.mono (Nat.le_refl _)
    (SourceCurrentProjectionUnionResources.readFuel_mono increase)⟩

/-- Initial closed available job forests construct their own graph at the computed scalar and fuels. -/
theorem complete (annotation : Guard → Prop) (jobs : List (Job Symbol Guard))
    (before : State Symbol Guard) (depth count jobCount resource : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before) (fields : SourceEqualityAnnotationHeap.Heap annotation before)
    (inputs : Inputs before jobs) (fits : Fits resource before)
    (depths : ∀ job ∈ jobs, job.2.length ≤ depth) (counts : ∀ job ∈ jobs, job.1.length ≤ count)
    (length : jobs.length ≤ jobCount) :
    ∃ values after, ∃ actual : Projections jobs before values after,
      Effects annotation before after ∧ Values after values ∧ ClosedValues values ∧
      Fits (jobsBound depth count jobCount resource) after ∧ values.length = jobs.length ∧
      Replay (workerFuel depth) (readerFuel depth count jobCount resource) actual := by
  obtain ⟨values, after, actual, effects, available, closed⟩ :=
    SourceCurrentConjunctionCompletionReads.projections_complete annotation jobs before semantic costs fields inputs
  have checked := Projections.bound actual depth count jobCount resource semantic costs inputs fits depths counts length
  exact ⟨values, after, actual, effects, available, closed, checked⟩

end MicroCFTA.SourceCurrentConjunctionProjectionResources
