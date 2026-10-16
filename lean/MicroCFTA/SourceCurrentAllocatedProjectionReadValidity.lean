import MicroCFTA.SourceCurrentAllocatedReadDeterminism

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
