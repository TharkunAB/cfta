import MicroCFTA.SourceCurrentConjunctionEmptinessRows
import MicroCFTA.SourceCurrentOpenExposureFields
import MicroCFTA.SourceEqualityProjectionCosts
import MicroCFTA.SourceEqualityAnnotationProjection
import MicroCFTA.SourceEqualityProjectionAPI

/-!
# Finite resident reads for current conjunction emptiness

Closed available operands have finite actual nodeEdges and getPath reads.
The graphs retain the returned constructor heap at every call. Projection
jobs use the source row-major order inside one equality requirement.

This component can complete a finite chosen sequence of reads. It does not
identify an eager sequence with Haskell lazy demand. Equality accessor and
combination interner events, dynamic exploration, and the current source
Decision and Scan adapter remain separate obligations.
-/
namespace MicroCFTA.SourceCurrentConjunctionCompletionReads
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionRead SourceEqualityProjectionGraph
open InternedGuardedLanguage (meaning)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "AnnotationHeap" => SourceEqualityAnnotationHeap.Heap

/-- Completed reads retain all four current constructor-heap invariants. -/
structure Effects (annotation : Guard → Prop) (before after : State Symbol Guard) : Prop where
  keeps : Keeps before after
  semantic : SemanticReady after
  costs : CostHeap after
  annotations : AnnotationHeap annotation after

/-- A read at its exact returned heap retains stored costs and annotations. -/
theorem read_effects [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {value : Value Symbol Guard}
    {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : Read value before edges after) (semantic : SemanticReady before)
    (costs : CostHeap before) (fields : AnnotationHeap annotation before)
    (available : Available before value) : Effects annotation before after := by
  have checked := SourceEqualityProjectionCosts.read_effects actual semantic costs available
  refine ⟨checked.1, checked.2.1, checked.2.2.1, ?_⟩
  cases actual with
  | done fuel completed =>
      simpa only [completed, MergedSourceExposure.Result.state] using
        SourceCurrentOpenExposureFields.nodeEdges_heap annotation fuel value before semantic fields available

/-- A finite selected operand sequence retains separate edge lists and their order. -/
inductive Exposures [DecidableEq (EdgeKey Symbol Guard)] :
    List (Value Symbol Guard) → State Symbol Guard →
      List (List (EdgeValue Symbol Guard)) → State Symbol Guard → Prop where
  | nil : Exposures [] state [] state
  | cons (first : Read value before edges middle)
      (rest : Exposures values middle more after) :
      Exposures (value :: values) before (edges :: more) after

/-- Every operand occurrence has one returned edge list; no occurrence is removed. -/
theorem Exposures.length [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {rows : List (List (EdgeValue Symbol Guard))} (actual : Exposures values before rows after) :
    rows.length = values.length := by
  induction actual with
  | nil => rfl
  | cons _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

/-- Every completed chosen exposure sequence derives its final resident closed rows. -/
theorem Exposures.verified [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {values : List (Value Symbol Guard)}
    {before after : State Symbol Guard} {rows : List (List (EdgeValue Symbol Guard))}
    (actual : Exposures values before rows after) (semantic : SemanticReady before)
    (costs : CostHeap before) (fields : AnnotationHeap annotation before)
    (available : Values before values) (closed : ClosedValues values) :
    Effects annotation before after ∧ ∀ edges ∈ rows, Edges after edges ∧ ClosedEdges edges := by
  induction actual with
  | nil =>
      exact ⟨⟨pure_keeps _ semantic.ready, semantic, costs, fields⟩, by simp⟩
  | @cons value before edges middle values more after first rest ih =>
      have own := read_effects annotation first semantic costs fields (available _ List.mem_cons_self)
      have rows := first.verified semantic (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
      have later := ih own.semantic own.costs own.annotations
        (fun child member => own.keeps.available child (available child (List.mem_cons_of_mem _ member)))
        (fun child member => closed child (List.mem_cons_of_mem _ member))
      refine ⟨⟨own.keeps.trans later.1.keeps, later.1.semantic, later.1.costs, later.1.annotations⟩, ?_⟩
      intro chosen member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨fun edge member => InternedEdgeResidency.edge_grows middle after later.1.keeps.growth edge
          (rows.2.2.1 edge member), rows.2.2.2⟩
      · exact later.2 chosen member

/-- Finite closed exposure is derived from actual reader completion, with no supplied bound. -/
theorem exposures_complete [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (fields : AnnotationHeap annotation before)
    (available : Values before values) (closed : ClosedValues values) :
    ∃ rows after, Exposures values before rows after ∧ Effects annotation before after ∧
      ∀ edges ∈ rows, Edges after edges ∧ ClosedEdges edges := by
  induction values generalizing before with
  | nil =>
      exact ⟨[], before, .nil, ⟨pure_keeps _ semantic.ready, semantic, costs, fields⟩, by simp⟩
  | cons value values ih =>
      obtain ⟨edges, middle, first, _, _, _, _⟩ :=
        SourceEqualityProjectionRead.complete value before semantic
          (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
      have own := read_effects annotation first semantic costs fields (available _ List.mem_cons_self)
      obtain ⟨rows, after, rest, _, _⟩ := ih middle own.semantic own.costs own.annotations
        (fun child member => own.keeps.available child (available child (List.mem_cons_of_mem _ member)))
        (fun child member => closed child (List.mem_cons_of_mem _ member))
      have actual := Exposures.cons first rest
      exact ⟨_, _, actual, actual.verified annotation semantic costs fields available closed⟩

/-- One source projection job retains its original forest and natural path. -/
abbrev Job (Symbol Guard : Type) := List (Value Symbol Guard) × EqualityNormalize.Path

/-- Every job has a closed available original forest at the current heap. -/
def Inputs (state : State Symbol Guard) (jobs : List (Job Symbol Guard)) : Prop :=
  ∀ job ∈ jobs, Values state job.1 ∧ ClosedValues job.1

/-- Original job inputs remain valid through actual constructor-heap effects. -/
theorem Inputs.keeps {jobs : List (Job Symbol Guard)} {before after : State Symbol Guard}
    (inputs : Inputs before jobs) (kept : Keeps before after) : Inputs after jobs := by
  intro job member
  exact ⟨fun value included => kept.available value ((inputs job member).1 value included), (inputs job member).2⟩

/-- The source list comprehension visits forests first, then paths in each forest. -/
def jobs (forests : List (List (Value Symbol Guard))) (paths : EqualityNormalize.Class) :
    List (Job Symbol Guard) :=
  forests.flatMap fun children => paths.map fun path => (children, path)

/-- Actual resident closed rows derive every job input, including repeated paths. -/
theorem jobs_inputs (state : State Symbol Guard)
    (forests : List (List (Value Symbol Guard))) (paths : EqualityNormalize.Class)
    (available : ∀ children ∈ forests, Values state children)
    (closed : ∀ children ∈ forests, ClosedValues children) : Inputs state (jobs forests paths) := by
  intro job member
  obtain ⟨children, present, selected⟩ := List.mem_flatMap.mp member
  obtain ⟨path, _, rfl⟩ := List.mem_map.mp selected
  exact ⟨available children present, closed children present⟩

/-- The number of source projection calls counts every row and path occurrence. -/
theorem jobs_length (forests : List (List (Value Symbol Guard))) (paths : EqualityNormalize.Class) :
    (jobs forests paths).length = forests.length * paths.length := by
  induction forests with
  | nil => simp [jobs]
  | cons children rest ih =>
      change ((paths.map fun path => (children, path)) ++ jobs rest paths).length = _
      rw [List.length_append, List.length_map, ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- Complete getPath calls execute in the chosen job order and retain exact snapshots. -/
inductive Projections [DecidableEq (EdgeKey Symbol Guard)] :
    List (Job Symbol Guard) → State Symbol Guard →
      List (Value Symbol Guard) → State Symbol Guard → Prop where
  | nil : Projections [] state [] state
  | cons {forest : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
      {before : State Symbol Guard} {value : Value Symbol Guard} {middle : State Symbol Guard}
      {remaining : List (Job Symbol Guard)} {values : List (Value Symbol Guard)} {after : State Symbol Guard}
      (first : Forest (path.map Int.ofNat) forest before value middle)
      (rest : Projections remaining middle values after) :
      Projections ((forest, path) :: remaining) before (value :: values) after

/-- Every source job contributes exactly one returned projection occurrence. -/
theorem Projections.length [DecidableEq (EdgeKey Symbol Guard)]
    {jobs : List (Job Symbol Guard)} {values : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (actual : Projections jobs before values after) :
    values.length = jobs.length := by
  induction actual with
  | nil => rfl
  | cons _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

/-- Actual projection effects derive closed available output and preserve annotations. -/
theorem Projections.verified [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {jobs : List (Job Symbol Guard)}
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : Projections jobs before values after) (semantic : SemanticReady before)
    (costs : CostHeap before) (fields : AnnotationHeap annotation before) (inputs : Inputs before jobs) :
    Effects annotation before after ∧ Values after values ∧ ClosedValues values := by
  induction actual with
  | nil => exact ⟨⟨pure_keeps _ semantic.ready, semantic, costs, fields⟩, by simp [Values], by simp [ClosedValues]⟩
  | @cons children path before value middle remaining values after first rest ih =>
      have ownInputs := inputs _ List.mem_cons_self
      have own := SourceEqualityProjectionCosts.forest_effects first semantic costs ownInputs.1
      have verified := SourceEqualityProjectionComplete.forest_complete (path.map Int.ofNat) children before
        semantic ownInputs.1 ownInputs.2
      obtain ⟨_, _, completed, _, _, _, resultClosed⟩ := verified
      obtain ⟨rfl, rfl⟩ := SourceEqualityProjectionAPI.forest_unique completed first
      have annotations := SourceEqualityAnnotationProjection.forest annotation first semantic ownInputs.1 ownInputs.2 fields
      have later := ih own.2.1 own.2.2.1 annotations
        (Inputs.keeps (fun job member => inputs job (List.mem_cons_of_mem _ member)) own.1)
      refine ⟨⟨own.1.trans later.1.keeps, later.1.semantic, later.1.costs, later.1.annotations⟩, ?_, ?_⟩
      · intro result member
        rcases List.mem_cons.mp member with rfl | member
        · exact later.1.keeps.available _ own.2.2.2
        · exact later.2.1 result member
      · intro result member
        rcases List.mem_cons.mp member with rfl | member
        · exact resultClosed
        · exact later.2.2 result member

/-- Every finite set of source row-major getPath jobs has a completed actual execution. -/
theorem projections_complete [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (jobs : List (Job Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (fields : AnnotationHeap annotation before) (inputs : Inputs before jobs) :
    ∃ values after, Projections jobs before values after ∧ Effects annotation before after ∧
      Values after values ∧ ClosedValues values := by
  induction jobs generalizing before with
  | nil =>
      exact ⟨[], before, .nil, ⟨pure_keeps _ semantic.ready, semantic, costs, fields⟩,
        by simp [Values], by simp [ClosedValues]⟩
  | cons job remaining ih =>
      obtain ⟨children, path⟩ := job
      have ownInputs := inputs _ List.mem_cons_self
      obtain ⟨value, middle, first, _, _, _, _⟩ :=
        SourceEqualityProjectionComplete.forest_complete (path.map Int.ofNat) children before
          semantic ownInputs.1 ownInputs.2
      have own := SourceEqualityProjectionCosts.forest_effects first semantic costs ownInputs.1
      have annotations := SourceEqualityAnnotationProjection.forest annotation first semantic ownInputs.1 ownInputs.2 fields
      obtain ⟨values, after, rest, _, _, _⟩ := ih middle own.2.1 own.2.2.1 annotations
        (Inputs.keeps (fun job member => inputs job (List.mem_cons_of_mem _ member)) own.1)
      have actual := Projections.cons first rest
      exact ⟨_, _, actual, actual.verified annotation semantic costs fields inputs⟩

/-- A source tuple of closed resident edges derives finite requirement projections. -/
theorem tuple_projections_complete [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (tuple : List (EdgeValue Symbol Guard)) (paths : EqualityNormalize.Class)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (fields : AnnotationHeap annotation before)
    (resident : Edges before tuple) (closed : ClosedEdges tuple) :
    ∃ values after, Projections (jobs (tuple.map EdgeValue.children) paths) before values after ∧
      Effects annotation before after ∧ Values after values ∧ ClosedValues values := by
  apply projections_complete annotation _ before semantic costs fields
  apply jobs_inputs
  · intro children member
    obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp member
    exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge edgeIn)
  · intro children member
    obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp member
    exact closed edge edgeIn

/-- A tuple drawn from actual exposed rows completes at that same returned heap. -/
theorem Exposures.tuple_projections_complete [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {nodes : List (Value Symbol Guard)}
    {before middle : State Symbol Guard} {rows : List (List (EdgeValue Symbol Guard))}
    (actual : Exposures nodes before rows middle) (semantic : SemanticReady before)
    (costs : CostHeap before) (fields : AnnotationHeap annotation before)
    (available : Values before nodes) (closed : ClosedValues nodes)
    (tuple : List (EdgeValue Symbol Guard)) (paths : EqualityNormalize.Class)
    (selected : ∀ edge ∈ tuple, edge ∈ rows.flatten) :
    ∃ values after, Projections (jobs (tuple.map EdgeValue.children) paths) middle values after ∧
      Effects annotation before after ∧ Values after values ∧ ClosedValues values := by
  have observed := actual.verified annotation semantic costs fields available closed
  have inputs : Edges middle tuple ∧ ClosedEdges tuple := by
    constructor
    · intro edge member
      obtain ⟨edges, rowIn, edgeIn⟩ := List.mem_flatten.mp (selected edge member)
      exact (observed.2 edges rowIn).1 edge edgeIn
    · intro edge member
      obtain ⟨edges, rowIn, edgeIn⟩ := List.mem_flatten.mp (selected edge member)
      exact (observed.2 edges rowIn).2 edge edgeIn
  obtain ⟨values, after, completed, effects, valuesAvailable, valuesClosed⟩ :=
    SourceCurrentConjunctionCompletionReads.tuple_projections_complete
      annotation tuple paths middle observed.1.semantic observed.1.costs observed.1.annotations
      inputs.1 inputs.2
  exact ⟨values, after, completed,
    ⟨observed.1.keeps.trans effects.keeps, effects.semantic, effects.costs, effects.annotations⟩,
    valuesAvailable, valuesClosed⟩

/-- An actual proper projection retains the common subtree used by a class requirement. -/
theorem projection_included [DecidableEq (EdgeKey Symbol Guard)]
    {children : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
    {before after : State Symbol Guard} {result : Value Symbol Guard}
    (actual : Forest (path.map Int.ofNat) children before result after)
    (semantic : SemanticReady before) (available : Values before children) (closed : ClosedValues children)
    (proper : path ≠ []) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) children terms)
    (selected : (Term.node symbol terms).atPath path = some part) : meaning holds ambient result part := by
  have natural (term : Term Symbol) (path : EqualityNormalize.Path) :
      SymbolicSignedPaths.lookup term (path.map Int.ofNat) = term.atPath path := by
    have decoded : SymbolicSignedPaths.decode (path.map Int.ofNat) = some path := by
      induction path with
      | nil => rfl
      | cons index rest ih => simp [SymbolicSignedPaths.decode, ih]
    rw [SymbolicSignedPaths.lookup_decode, decoded, Option.bind_some]
  cases path with
  | nil => exact False.elim (proper rfl)
  | cons index rest =>
      exact SourceEqualityProjectionAPI.forest_included actual semantic available closed holds ambient symbol terms part
        accepted (by
          change SymbolicSignedPaths.lookup (.node symbol terms) ((index :: rest).map Int.ofNat) = some part
          rw [natural]
          exact selected)

section ActualGuards
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Read the literal accessor classes of one returned physical edge. -/
noncomputable def edgeView (edge : EdgeValue Symbol Guard) :
    SourceCurrentConjunctionEmptinessRows.Edge (Value Symbol Guard) Symbol :=
  ⟨edge.entry.key.symbol, edge.children, SourceCompactGuards.sourceEqualities edge.entry.key.constraint⟩

/-- Actual guarded acceptance derives an accepted tuple operand without an exposure oracle. -/
theorem read_accepted [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : Read value before edges after) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
    (accepted : meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term) :
    ∃ edge ∈ edges, SourceCurrentConjunctionEmptinessRows.EdgeAccepts
      (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) (edgeView edge) term := by
  obtain ⟨edge, member, terms, shape, forest, guard⟩ :=
    (actual.exact semantic available closed (SourceEqualityPCSGuard.holds formulas solver) ambient term).mpr accepted
  exact ⟨edge, member, terms, shape, forest,
    SourceEqualityPCSGuard.own_sat formulas solver edge.entry.key.constraint term guard⟩

end ActualGuards
end MicroCFTA.SourceCurrentConjunctionCompletionReads
