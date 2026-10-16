import MicroCFTA.SourceCurrentAllocatedReadDeterminism
import MicroCFTA.SourceCurrentConjunctionGlobalMemos

/-!
# Validity of supplied projection global reads

These proofs follow the supplied ordered projection receipts. Each row
exposure uses uniqueness only at its recorded fuel. Child projections
and unions retain their own returned tables through actual heap effects.
-/
namespace MicroCFTA.SourceCurrentAllocatedProjectionReadValidity
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceEqualityProjectionMemos
open SourceEqualityRequiredHead (Head)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard
local notation "Correct" => InternedFreshOrdinaryUnfoldMemo.Correct
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A supplied row read derives correctness for its own fixed-fuel returned unfolding table. -/
theorem read {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    {trace : Read value before edges after} {memo final : UMemo} (reads : ReadReads trace memo final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (correct : Correct before memo) : Correct after final ∧ Extends memo final := by
  cases reads with
  | @done fuel value before after edges actual memo final calls =>
      obtain ⟨saved, constructed, checked, retained⟩ := SourceEqualityExposureMemos.nodeEdges_reads
        fuel value before semantic costs available memo correct
      have same := SourceCurrentAllocatedReadDeterminism.exposure_unique constructed calls
      subst saved
      exact ⟨by simpa only [actual, MergedSourceExposure.Result.state] using checked, retained⟩

private theorem node_correct (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (resident : Edges before edges) (memo : UMemo) (correct : Correct before memo) :
    Correct (run (makeNode edges) before).2 memo := by
  have actual := SourceEqualityOpenOrdinaryHead.node edges before semantic resident
  exact InternedFreshOrdinaryUnfoldMemo.grows before _ semantic.ready.semantic.1.normal.facts.coherent.valid
    actual.1.growth actual.1.history memo correct

/-- A supplied head keeps the same returned read table through its exact node constructor. -/
theorem head {value result : Value Symbol Guard} {before after : State Symbol Guard}
    {trace : Head value before result after} {memo final : UMemo} (reads : HeadReads trace memo final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (correct : Correct before memo) : Correct after final ∧ Extends memo final := by
  cases reads with
  | @read fuel value result before middle after edges exposed rebuilt memo final calls =>
      have first := read calls semantic costs available correct
      have effects := SourceEqualityProjectionCosts.read_effects (.done fuel exposed) semantic costs available
      have last := node_correct edges middle effects.2.1 effects.2.2.2 final first.1
      exact ⟨by simpa only [rebuilt] using last, first.2⟩

/-- Supplied union reads thread literal tables in original operand order. -/
theorem readAll {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {edges : List (EdgeValue Symbol Guard)} {trace : ReadAll values before edges after} {memo final : UMemo}
    (reads : ReadAllReads trace memo final) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (correct : Correct before memo) : Correct after final ∧ Extends memo final := by
  revert semantic costs available correct
  induction reads with
  | nil => intro _ _ _ initialCorrect; exact ⟨initialCorrect, extends_refl _⟩
  | @cons value before rows middle firstTrace memo middleMemo values more after restTrace final first rest ih =>
      intro initialSemantic initialCosts inputAvailable initialCorrect
      have checked := read first initialSemantic initialCosts (inputAvailable _ List.mem_cons_self) initialCorrect
      have effects := SourceEqualityProjectionCosts.read_effects firstTrace initialSemantic initialCosts (inputAvailable _ List.mem_cons_self)
      have later := ih effects.2.1 effects.2.2.1
        (fun child member => effects.1.available child (inputAvailable child (List.mem_cons_of_mem _ member))) checked.1
      exact ⟨later.1, extends_trans checked.2 later.2⟩

/-- The actual source union constructor retains the supplied final operand-read table. -/
theorem union {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    {trace : Union values before result after} {memo final : UMemo} (reads : UnionReads trace memo final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (correct : Correct before memo) : Correct after final ∧ Extends memo final := by
  cases reads with
  | node calls =>
      rename_i middle edges actual built
      have first := readAll calls semantic costs available correct
      have effects := SourceEqualityProjectionCosts.readAll_effects actual semantic costs available
      have last := node_correct edges middle effects.2.1 effects.2.2.2 final first.1
      exact ⟨by simpa only [built] using last, first.2⟩

-- Both actual recursive read graphs use the same initial-state physical facts.
local macro "projection_induction" recursor:ident reads:ident semantic:ident costs:ident available:ident correct:ident : tactic => `(tactic|
  (revert $semantic $costs $available $correct
   apply $recursor
     (motive_1 := fun {_path value before _result after} _ memo final _ =>
       SemanticReady before → CostHeap before → Available before value → Correct before memo →
         Correct after final ∧ Extends memo final)
     (motive_2 := fun {_path _index edges before _results after} _ memo final _ =>
       SemanticReady before → CostHeap before → Edges before edges → Correct before memo →
         Correct after final ∧ Extends memo final)
     (t := $reads)
   · intro value before memo _ _ _ initialCorrect
     exact ⟨initialCorrect, extends_refl _⟩
   · intro index path before memo _ _ _ initialCorrect
     exact ⟨initialCorrect, extends_refl _⟩
   · intro entry depth free path index edges before values middle rowsTrace memo middleMemo result after unionTrace final rowCalls unionCalls ih initialSemantic initialCosts inputAvailable initialCorrect
     have resident := InternedEdgeResidency.resident_edges before initialSemantic.ready.semantic.1.normal.facts.linked _ inputAvailable.resident
     have first := ih initialSemantic initialCosts resident initialCorrect
     have effects := SourceEqualityProjectionCosts.rows_effects rowsTrace initialSemantic initialCosts resident
     have last := union unionCalls effects.2.1 effects.2.2.1 effects.2.2.2 first.1
     exact ⟨last.1, extends_trans first.2 last.2⟩
   · intro original before exposed middle headTrace memo middleMemo index path result after bodyTrace final recursive headCalls bodyCalls ih initialSemantic initialCosts inputAvailable initialCorrect
     have first := head headCalls initialSemantic initialCosts inputAvailable initialCorrect
     have effects := SourceEqualityProjectionCosts.head_effects headTrace initialSemantic initialCosts inputAvailable
     have rest := ih effects.2.1 effects.2.2.1 effects.2.2.2 first.1
     exact ⟨rest.1, extends_trans first.2 rest.2⟩
   · intro path index before memo _ _ _ initialCorrect
     exact ⟨initialCorrect, extends_refl _⟩
   · intro path index edges before results after restTrace memo final edge absent restCalls ih initialSemantic initialCosts resident initialCorrect
     exact ih initialSemantic initialCosts (fun edge member => resident edge (List.mem_cons_of_mem _ member)) initialCorrect
   · intro path child before result middle firstTrace memo middleMemo index edges results after restTrace final edge found firstCalls restCalls firstIH restIH initialSemantic initialCosts resident initialCorrect
     have inputAvailable := initialSemantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
       (resident edge List.mem_cons_self) child (select_member found)
     have first := firstIH initialSemantic initialCosts inputAvailable initialCorrect
     have effects := SourceEqualityProjectionCosts.project_effects firstTrace initialSemantic initialCosts inputAvailable
     have rest := restIH effects.2.1 effects.2.2.1
       (fun edge member => InternedEdgeResidency.edge_grows before middle effects.1.growth edge
         (resident edge (List.mem_cons_of_mem _ member))) first.1
     exact ⟨rest.1, extends_trans first.2 rest.2⟩))

/-- A supplied actual projection derives correctness of its own returned unfolding table. -/
theorem project {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    {trace : Project path value before result after} {memo final : UMemo} (reads : ProjectReads trace memo final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (correct : Correct before memo) : Correct after final ∧ Extends memo final := by
  projection_induction ProjectReads.rec reads semantic costs available correct

/-- Supplied selected-row reads preserve their actual table sequence. -/
theorem rows {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)} {results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} {trace : ProjectRows path index edges before results after} {memo final : UMemo}
    (reads : RowsReads trace memo final) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Edges before edges) (correct : Correct before memo) : Correct after final ∧ Extends memo final := by
  projection_induction RowsReads.rec reads semantic costs available correct

/-- Root, missing, and selected forest branches retain each supplied unfolding receipt. -/
theorem forest_unfold {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : State Symbol Guard} {trace : Forest path values before result after} {memo final : UMemo}
    (reads : ForestReads trace memo final) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (correct : Correct before memo) : Correct after final ∧ Extends memo final := by
  cases reads with
  | root calls => exact union calls semantic costs available correct
  | missing => exact ⟨correct, extends_refl _⟩
  | selected calls => exact project calls semantic costs (available _ (select_member (by assumption))) correct

/-- A supplied full forest receipt derives all three final tables without closing unrelated siblings. -/
theorem forest {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : State Symbol Guard} {trace : Forest path values before result after} {memos final : Memos}
    (reads : SourceEqualityQueryGlobalMemos.ProjectionReads trace memos final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  have checked := forest_unfold reads.1 semantic costs available valid.unfolding
  have effects := SourceEqualityProjectionCosts.forest_effects trace semantic costs available
  refine ⟨⟨checked.1, ?_⟩, checked.2, reads.2⟩
  rw [reads.2]
  exact SourceEndpointMemo.grows before after effects.1.growth effects.1.history memos.query valid.query

end MicroCFTA.SourceCurrentAllocatedProjectionReadValidity


/-!
# Validity of supplied current conjunction read receipts

Each theorem uses the supplied operational read graph. Actual physical
effects derive the inputs for its next read. The proof retains the exact
returned global bundle. It does not compare different read schedules.
-/
namespace MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionCompletionReads (Exposures Projections Inputs jobs)
open SourceCurrentConjunctionRequirements (ClassRequirements Requirements)
open SourceCurrentConjunctionRowsAllocation (Tuple Tuples Rows Ready)
open SourceCurrentConjunctionWorklist (Run PendingReady)
open SourceCurrentConjunctionGlobalMemos
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A supplied completed exposure derives coherence for its own saved bundle. -/
theorem read
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    {actual : SourceEqualityProjectionRead.Read value before edges after} {memos final : Memos}
    (reads : ReadReads actual memos final) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  rcases reads with ⟨calls, same⟩
  cases calls with
  | @done fuel value before after edges completed memo saved calls =>
      simpa only [completed, MergedSourceExposure.Result.state] using
        SourceCurrentAllocatedReadDeterminism.exposure ⟨calls, same⟩ semantic costs available valid

/-- The actual exposure prefix derives each following original operand's residency. -/
theorem exposures
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {edges : List (List (EdgeValue Symbol Guard))} {actual : Exposures values before edges after}
    {memos final : Memos} (reads : ExposuresReads actual memos final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  induction reads with
  | nil => exact ⟨valid, extends_refl _, rfl⟩
  | @cons value before edges middle first memos middleMemo values more after rest final firstRead restRead ih =>
      have firstMemo := read firstRead semantic costs (available _ List.mem_cons_self) valid
      have own := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
      have later := ih own.2.1 own.2.2.1
        (fun value member => own.1.available value (available value (List.mem_cons_of_mem _ member))) firstMemo.1
      exact ⟨later.1, extends_trans firstMemo.2.1 later.2.1, later.2.2.trans firstMemo.2.2⟩

/-- Supplied projection jobs pass their actual returned bundle in row-major order. -/
theorem projections
    {work : List (SourceCurrentConjunctionCompletionReads.Job Symbol Guard)} {before after : State Symbol Guard}
    {values : List (Value Symbol Guard)} {actual : Projections work before values after}
    {memos final : Memos} (reads : ProjectionsReads actual memos final)
    (semantic : SemanticReady before) (costs : CostHeap before) (inputs : Inputs before work)
    (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  induction reads with
  | nil => exact ⟨valid, extends_refl _, rfl⟩
  | @cons path forest before value middle first memos middleMemo remaining values after rest final firstRead restRead ih =>
      have ownInputs := inputs _ List.mem_cons_self
      have firstMemo := SourceCurrentAllocatedProjectionReadValidity.forest firstRead semantic costs ownInputs.1 valid
      have own := SourceEqualityProjectionCosts.forest_effects first semantic costs ownInputs.1
      have later := ih own.2.1 own.2.2.1
        (SourceCurrentConjunctionCompletionReads.Inputs.keeps
          (fun job member => inputs job (List.mem_cons_of_mem _ member)) own.1) firstMemo.1
      exact ⟨later.1, extends_trans firstMemo.2.1 later.2.1, later.2.2.trans firstMemo.2.2⟩

/-- The actual class projection prefix retains all original closed forests. -/
theorem classes
    {forests : List (List (Value Symbol Guard))} {constraints : EqualityNormalize.Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    {actual : ClassRequirements forests constraints before requirements after} {memos final : Memos}
    (reads : ClassesReads actual memos final) (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : SourceCurrentConjunctionRequirements.RowsReady before forests) (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  induction reads with
  | nil => exact ⟨valid, extends_refl _, rfl⟩
  | @cons paths before projected middle first memos middleMemo constraints requirements after rest final firstRead restRead ih =>
      have jobsReady := SourceCurrentConjunctionCompletionReads.jobs_inputs before forests paths
        (fun forest member => (inputs forest member).1) (fun forest member => (inputs forest member).2)
      have firstMemo := projections firstRead semantic costs jobsReady valid
      have own := first.verified (fun _ => True) semantic costs (fun _ _ _ => trivial) jobsReady
      have later := ih own.1.semantic own.1.costs
        (fun forest member => ⟨fun value included => own.1.keeps.available value ((inputs forest member).1 value included),
          (inputs forest member).2⟩) firstMemo.1
      exact ⟨later.1, extends_trans firstMemo.2.1 later.2.1, later.2.2.trans firstMemo.2.2⟩

/-- Child-column canonicalization adds no read before the supplied class receipts. -/
theorem requirements
    {tuple : List (EdgeValue Symbol Guard)} {constraints : EqualityNormalize.Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    {actual : Requirements tuple constraints before requirements after} {memos final : Memos}
    (reads : RequirementsReads actual memos final) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before tuple) (closed : ClosedEdges tuple) (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases reads with
  | run calls =>
      exact classes calls semantic costs
        (SourceCurrentConjunctionRequirements.tuple_inputs tuple before semantic resident closed) valid

/-- Equality allocation retains globals before the supplied live requirement reads. -/
theorem tuple
    {tuple : List (EdgeValue Symbol Guard)} {before after : Physical}
    {row : Option (List (List (Value Symbol Guard)))} {actual : Tuple tuple before row after} {memos final : Memos}
    (reads : TupleReads actual memos final) (ready : Ready before)
    (resident : Edges before.heap tuple) (closed : ClosedEdges tuple) (valid : Valid before.heap memos) :
    Valid after.heap final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases reads with
  | contradiction => exact ⟨valid, extends_refl _, rfl⟩
  | live calls => exact requirements calls ready.semantic ready.costs resident closed valid

/-- Actual tuple prefixes derive every subsequent current physical input. -/
theorem tuples
    {items : List (List (EdgeValue Symbol Guard))} {before after : Physical}
    {rows : List (List (List (Value Symbol Guard)))} {actual : Tuples items before rows after} {memos final : Memos}
    (reads : TuplesReads actual memos final) (ready : Ready before)
    (resident : ∀ item ∈ items, Edges before.heap item) (closed : ∀ item ∈ items, ClosedEdges item)
    (valid : Valid before.heap memos) :
    Valid after.heap final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  induction reads with
  | nil => exact ⟨valid, extends_refl _, rfl⟩
  | @skip item before middle first memos middleMemo items rows after rest final firstRead restRead ih =>
      have own := first.verified ready (resident item List.mem_cons_self) (closed item List.mem_cons_self)
      have firstMemo := tuple firstRead ready (resident item List.mem_cons_self) (closed item List.mem_cons_self) valid
      have later := ih own.1.ready
        (fun chosen member edge included => InternedEdgeResidency.edge_grows before.heap middle.heap own.1.keeps.growth
          edge (resident chosen (List.mem_cons_of_mem _ member) edge included))
        (fun chosen member => closed chosen (List.mem_cons_of_mem _ member)) firstMemo.1
      exact ⟨later.1, extends_trans firstMemo.2.1 later.2.1, later.2.2.trans firstMemo.2.2⟩
  | @keep item before row middle first memos middleMemo items rows after rest final firstRead restRead ih =>
      have own := first.verified ready (resident item List.mem_cons_self) (closed item List.mem_cons_self)
      have firstMemo := tuple firstRead ready (resident item List.mem_cons_self) (closed item List.mem_cons_self) valid
      have later := ih own.1.ready
        (fun chosen member edge included => InternedEdgeResidency.edge_grows before.heap middle.heap own.1.keeps.growth
          edge (resident chosen (List.mem_cons_of_mem _ member) edge included))
        (fun chosen member => closed chosen (List.mem_cons_of_mem _ member)) firstMemo.1
      exact ⟨later.1, extends_trans firstMemo.2.1 later.2.1, later.2.2.trans firstMemo.2.2⟩

/-- Supplied row reads retain their own tables through actual equality effects. -/
theorem rows [DecidableEq Symbol]
    {nodes : List (Value Symbol Guard)} {before after : Physical}
    {rows : List (List (List (Value Symbol Guard)))} {actual : Rows nodes before rows after} {memos final : Memos}
    (reads : RowsReads actual memos final) (ready : Ready before) (available : Values before.heap nodes)
    (closed : ClosedValues nodes) (valid : Valid before.heap memos) :
    Valid after.heap final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases reads with
  | @run edges heap exposed memos middleMemo rows after allocated final exposedRead allocatedRead =>
      have firstMemo := exposures exposedRead ready.semantic ready.costs available valid
      have own := exposed.verified (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
        ready.semantic ready.costs ready.fields available closed
      have middle : Ready (⟨heap, before.equality⟩ : Physical) :=
        ⟨own.1.semantic, own.1.costs, ready.valid, own.1.annotations⟩
      have later := tuples allocatedRead middle
        (fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified
          (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
          exposed ready.semantic ready.costs ready.fields available closed tuple member).2.1)
        (fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified
          (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
          exposed ready.semantic ready.costs ready.fields available closed tuple member).2.2) firstMemo.1
      exact ⟨later.1, extends_trans firstMemo.2.1 later.2.1, later.2.2.trans firstMemo.2.2⟩

/-- Every actual admission derives the physical inputs used by its supplied suffix reads. -/
theorem run [DecidableEq Symbol]
    {budget : Nat} {table entered : List (SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard))}
    {pending : List (List (Value Symbol Guard))} {before after : Physical}
    {actual : Run budget table pending before entered after} {memos final : Memos}
    (reads : RunReads actual memos final) (ready : Ready before) (available : PendingReady before pending)
    (valid : Valid before.heap memos) :
    Valid after.heap final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  induction reads with
  | done => exact ⟨valid, extends_refl _, rfl⟩
  | empty restRead ih =>
      exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) valid
  | skip restRead ih =>
      exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) valid
  | @admit nodes before requirements middle rowTrace memos middleMemo budget table pending entered after rest final nonempty fresh rowRead restRead ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted
        (SourceCurrentConjunctionRequirements.key : Value Symbol Guard → Int)
        SourceCurrentConjunctionWorklist.closed budget table nodes fresh
      have inputs := available nodes List.mem_cons_self
      have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      have own := SourceCurrentConjunctionRowsSoundness.rows_verified rowTrace ready inputs noFree
      have firstMemo := rows rowRead ready inputs noFree valid
      have nextPending : PendingReady middle (requirements.flatten ++ pending) := by
        intro requirement member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
          exact (own.2 row rowIn requirement requirementIn).1
        · exact SourceCurrentConjunctionWorklist.pending_keeps own.1.keeps
            (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) requirement earlier
      have later := ih own.1.ready nextPending firstMemo.1
      exact ⟨later.1, extends_trans firstMemo.2.1 later.2.1, later.2.2.trans firstMemo.2.2⟩

/-- Open-input and fixed-point guards add no reads around the supplied worklist. -/
theorem decision [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {query : Value Symbol Guard} {before after : Physical} {answer : Bool}
    {actual : SourceCurrentConjunctionDecision.Decision budget query before answer after} {memos final : Memos}
    (reads : DecisionReads actual memos final) (ready : Ready before) (available : Available before.heap query)
    (valid : Valid before.heap memos) :
    Valid after.heap final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases reads with
  | open_input => exact ⟨valid, extends_refl _, rfl⟩
  | closed calls =>
      exact run calls ready (by
        intro nodes member value included
        cases List.mem_singleton.mp member
        cases List.mem_singleton.mp included
        exact available) valid

/-- The supplied current memo hit or miss derives its own coherent returned global tables. -/
theorem call [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {memo saved : SourceCurrentEmptinessMemo.Memo} {query : Value Symbol Guard}
    {before after : Physical} {answer : Bool}
    {actual : SourceCurrentConjunctionMemo.Call budget memo query before answer after saved} {memos final : Memos}
    (reads : CallReads actual memos final) (ready : Ready before) (available : Available before.heap query)
    (valid : Valid before.heap memos) :
    Valid after.heap final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases reads with
  | hit => exact ⟨valid, extends_refl _, rfl⟩
  | miss calls => exact decision calls ready available valid

end MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity
