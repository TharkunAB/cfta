import MicroCFTA.SourceCurrentConstrainedCapMergeGuardEffects
import MicroCFTA.SourceEqualityProjectionOutcomeMemos

/-!
# Causal guard heaps at every projection outcome

Each branch retains the literal returned heap. A failed exposure or child
call retains its completed prefix. Ordinary reconstruction adds no Mu
record. The input values need not be closed. These laws do not prove that
the projection succeeds or that every edge guard satisfies the predicate.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapProjectionGuardOutcome
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache (Keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityRequiredWorker (Result work)
open SourceEqualityProjectionWorker (readAll union project rows forest)
open SourceEqualityProjectionGraph (select select_member)
open SourceEqualityProjectionOutcomePrimitives (reached)
open SourceCurrentConstrainedCapGuardHeap (Heap)
variable {Symbol Guard : Type}
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private theorem bind_heap {A B : Type} {annotation : Guard → Prop}
    {actual : Result Symbol Guard A}
    {next : A → State Symbol Guard → Result Symbol Guard B}
    (first : Heap annotation (reached actual))
    (later : ∀ value after, actual = .done value after → Heap annotation after →
      Heap annotation (reached (next value after))) :
    Heap annotation (reached (actual.bind next)) := by
  cases actual with
  | done value after => exact later value after rfl first
  | pending key after => exact first
  | unresolved name after => exact first
  | exhausted limit after => exact first

private theorem map_reached {A B : Type} (actual : Result Symbol Guard A) (f : A → B) :
    reached (actual.bind fun value after => .done (f value) after) = reached actual := by
  cases actual <;> rfl

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem readAll_heap (annotation : Guard → Prop) (h : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (known : Heap annotation before) :
    Heap annotation (reached (readAll h values before)) := by
  induction values generalizing before with
  | nil => exact known
  | cons value values ih =>
      have own := SourceCurrentConstrainedCapMergeGuardEffects.nodeEdges_heap annotation h value before
        semantic known (available value List.mem_cons_self)
      cases actual : MergedFreshOrdinaryExposure.nodeEdges h value before with
      | done edges middle =>
          have middleHeap : Heap annotation middle := by
            simpa only [actual, MergedSourceExposure.Result.state] using own
          have effects := SourceEqualityProjectionCosts.read_effects (.done h actual) semantic costs
            (available value List.mem_cons_self)
          have later := ih middle effects.2.1 effects.2.2.1
            (fun child member => effects.1.available child (available child (List.mem_cons_of_mem _ member)))
            middleHeap
          simpa only [readAll, actual, map_reached] using later
      | pending key after =>
          simpa only [readAll, actual, reached, MergedSourceExposure.Result.state] using own
      | unresolved name after =>
          simpa only [readAll, actual, reached, MergedSourceExposure.Result.state] using own
      | exhausted after =>
          simpa only [readAll, actual, reached, MergedSourceExposure.Result.state] using own

private theorem head_heap (annotation : Guard → Prop) (h : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Available before value)
    (known : Heap annotation before) :
    Heap annotation (reached (SourceEqualityRequiredWorker.head h value before)) := by
  have own := SourceCurrentConstrainedCapMergeGuardEffects.nodeEdges_heap annotation h value before
    semantic known available
  cases actual : MergedFreshOrdinaryExposure.nodeEdges h value before with
  | done edges middle =>
      have middleHeap : Heap annotation middle := by
        simpa only [actual, MergedSourceExposure.Result.state] using own
      have retained := SourceCurrentConstrainedCapGuardHeap.preserve annotation middle
        (run (makeNode edges) middle).2 middleHeap (InternedShallowHeap.makeNode_noNewMu edges middle)
      simpa only [SourceEqualityRequiredWorker.head, actual, work, reached] using retained
  | pending key after =>
      simpa only [SourceEqualityRequiredWorker.head, actual, reached, MergedSourceExposure.Result.state] using own
  | unresolved name after =>
      simpa only [SourceEqualityRequiredWorker.head, actual, reached, MergedSourceExposure.Result.state] using own
  | exhausted after =>
      simpa only [SourceEqualityRequiredWorker.head, actual, reached, MergedSourceExposure.Result.state] using own

private theorem union_heap (annotation : Guard → Prop) (h : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (known : Heap annotation before) :
    Heap annotation (reached (union h values before)) := by
  rw [union]
  apply bind_heap (readAll_heap annotation h values before semantic costs available known)
  intro edges middle _ middleHeap
  exact SourceCurrentConstrainedCapGuardHeap.preserve annotation middle
    (run (makeNode edges) middle).2 middleHeap (InternedShallowHeap.makeNode_noNewMu edges middle)

private theorem rows_from (annotation : Guard → Prop) (p h : Nat) (path : List Int)
    (smaller : ∀ (value : Value Symbol Guard) (before : State Symbol Guard),
      SemanticReady before → CostHeap before → Available before value → Heap annotation before →
      Heap annotation (reached (project p h path value before)))
    (index : Int) (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (known : Heap annotation before) :
    Heap annotation (reached (rows (project p h path) index edges before)) := by
  induction edges generalizing before with
  | nil => exact known
  | cons edge edges ih =>
      have tail := fun row member => resident row (List.mem_cons_of_mem _ member)
      cases found : select edge.children index with
      | none => simpa only [rows, found] using ih before semantic costs tail known
      | some child =>
          rw [rows, found]
          have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
            (resident edge List.mem_cons_self) child (select_member found)
          apply bind_heap (smaller child before semantic costs available known)
          intro value middle completed middleHeap
          have effects := SourceEqualityProjectionOutcomeMemos.project_effects p h path child before
            semantic costs available
          have current : Keeps before middle ∧ SemanticReady middle ∧ CostHeap middle := by
            simpa only [completed, reached] using
              And.intro effects.1 (And.intro effects.2.1 effects.2.2.1)
          have later := ih middle current.2.1 current.2.2
            (fun row member => InternedEdgeResidency.edge_grows before middle current.1.growth row (tail row member))
            middleHeap
          simpa only [map_reached] using later

/-- Every literal node outcome retains the current causal Mu guard observations. -/
theorem project_heap (annotation : Guard → Prop) (p h : Nat) (path : List Int)
    (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (known : Heap annotation before) :
    Heap annotation (reached (project p h path value before)) := by
  induction p generalizing path value before with
  | zero => exact known
  | succ p ih =>
      cases path with
      | nil => exact known
      | cons index path =>
          have expose (original : Value Symbol Guard) (present : Available before original) :
              Heap annotation (reached ((SourceEqualityRequiredWorker.head h original before).bind
                fun exposed after => project p h (index :: path) exposed after)) := by
            apply bind_heap (head_heap annotation h original before semantic present known)
            intro exposed after completed afterHeap
            have effects := SourceEqualityProjectionOutcomePrimitives.head_effects h original before
              semantic costs present
            have current : Keeps before after ∧ SemanticReady after ∧ CostHeap after := by
              simpa only [completed, reached] using
                And.intro effects.1 (And.intro effects.2.1 effects.2.2.1)
            exact ih (index :: path) exposed after current.2.1 current.2.2
              (effects.2.2.2 exposed after completed) afterHeap
          cases value with
          | empty => exact known
          | reference name => exact known
          | mu entry body depth ordinary => exact expose (.mu entry body depth ordinary) available
          | union entry members depth free => exact expose (.union entry members depth free) available
          | node entry edges depth free =>
              rw [project]
              have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked
                (.node entry edges depth free) available.resident
              apply bind_heap (rows_from annotation p h path
                (fun child heap sem cost present guards => ih path child heap sem cost present guards)
                index edges before semantic costs resident known)
              intro values middle completed middleHeap
              have effects := SourceEqualityProjectionOutcomeMemos.rows_effects p h path index edges before
                semantic costs resident
              have current : Keeps before middle ∧ SemanticReady middle ∧ CostHeap middle := by
                simpa only [completed, reached] using
                  And.intro effects.1 (And.intro effects.2.1 effects.2.2.1)
              exact union_heap annotation h values middle current.2.1 current.2.2
                (effects.2.2.2 values middle completed) middleHeap

/-- Every selected row prefix retains the causal guard heap, including a failed child. -/
theorem rows_heap (annotation : Guard → Prop) (p h : Nat) (path : List Int) (index : Int)
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (known : Heap annotation before) :
    Heap annotation (reached (rows (project p h path) index edges before)) :=
  rows_from annotation p h path
    (fun value heap sem cost present guards => project_heap annotation p h path value heap sem cost present guards)
    index edges before semantic costs resident known

/-- Every forest outcome retains causal guard observations from current open operands. -/
theorem forest_heap (annotation : Guard → Prop) (p h : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (known : Heap annotation before) :
    Heap annotation (reached (forest p h path values before)) := by
  cases path with
  | nil => exact union_heap annotation h values before semantic costs available known
  | cons index path =>
      cases found : select values index with
      | none => simpa only [forest, found, reached] using known
      | some value =>
          simpa only [forest, found] using
            project_heap annotation p h path value before semantic costs (available value (select_member found)) known

end MicroCFTA.SourceCurrentConstrainedCapProjectionGuardOutcome
