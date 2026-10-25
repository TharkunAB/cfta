import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceEqualityQueryGlobalMemos

/-!
# Global memo receipts through completed required-path calls

Head reads record their actual bounded unfolding calls. Child and row
receipts pass the returned tables in source order. Constructors retain
the same tables. Completed graphs derive final coherence and retain both
query tables and every earlier unfolding entry. These receipts do not
assert a native lazy evaluation schedule or general worker completion.
-/
namespace MicroCFTA.SourceCurrentRequiredQueryMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceEqualityRequiredHead (Head)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A head receipt records exposure before its constructor-only suffix. -/
inductive HeadReads [DecidableEq (EdgeKey Symbol Guard)] :
    {value : Value Symbol Guard} → {before : State Symbol Guard} → {result : Value Symbol Guard} →
      {after : State Symbol Guard} → Head value before result after → Memos → Memos → Prop where
  | read {fuel : Nat} {value result : Value Symbol Guard} {before middle after : State Symbol Guard}
      {edges : List (EdgeValue Symbol Guard)}
      {exposed : MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done edges middle}
      {rebuilt : run (makeNode edges) middle = (result, after)} {memos saved : Memos}
      (calls : SourceEqualityQueryGlobalMemos.ExposureReads fuel value before memos saved) :
      HeadReads (.read fuel edges middle exposed rebuilt) memos saved

mutual
  /-- One completed required-node call retains its actual unfolding calls. -/
  inductive NodeReads [DecidableEq (EdgeKey Symbol Guard)] :
      {needed : SourceEqualityNeeded.Needed} → {value : Value Symbol Guard} →
        {before : State Symbol Guard} → {result : Value Symbol Guard} → {after : State Symbol Guard} →
        RequireNode needed value before result after → Memos → Memos → Prop where
    | identity : NodeReads .identity memos memos
    | empty : NodeReads (.empty nonempty) memos memos
    | ordinary (rows : RowsReads rowsTrace memos saved) :
        NodeReads (.ordinary nonempty rowsTrace rebuilt) memos saved
    | recursive (head : HeadReads headTrace memos middleMemo) (body : NodeReads bodyTrace middleMemo saved) :
        NodeReads (.recursive nonempty recursive headTrace bodyTrace) memos saved

  /-- Children pass each returned table to the next original position. -/
  inductive ChildrenReads [DecidableEq (EdgeKey Symbol Guard)] :
      {entries : List (Int × SourceEqualityNeeded.Needed)} → {index : Nat} →
        {values : List (Value Symbol Guard)} → {before : State Symbol Guard} →
        {results : List (Value Symbol Guard)} → {after : State Symbol Guard} →
        RequireChildren entries index values before results after → Memos → Memos → Prop where
    | nil : ChildrenReads .nil memos memos
    | unselected {entries : List (Int × SourceEqualityNeeded.Needed)} {index : Nat}
        {values results : List (Value Symbol Guard)} {before after : State Symbol Guard} {value : Value Symbol Guard}
        {absent : SourceEqualityNeededMap.lookup (index : Int) entries = none}
        {restTrace : RequireChildren entries (index + 1) values before results after} {memos saved : Memos}
        (rest : ChildrenReads restTrace memos saved) :
        ChildrenReads (.unselected (value := value) index absent restTrace) memos saved
    | selected {entries : List (Int × SourceEqualityNeeded.Needed)} {index : Nat} {needed : SourceEqualityNeeded.Needed}
        {values results : List (Value Symbol Guard)} {value result : Value Symbol Guard} {before middle after : State Symbol Guard}
        {found : SourceEqualityNeededMap.lookup (index : Int) entries = some needed}
        {firstTrace : RequireNode needed value before result middle}
        {restTrace : RequireChildren entries (index + 1) values middle results after} {memos middleMemo saved : Memos}
        (first : NodeReads firstTrace memos middleMemo) (rest : ChildrenReads restTrace middleMemo saved) :
        ChildrenReads (.selected index found firstTrace restTrace) memos saved

  /-- Row rejection makes no call; retained rows follow children, edge construction, and remaining rows. -/
  inductive RowsReads [DecidableEq (EdgeKey Symbol Guard)] :
      {entries : List (Int × SourceEqualityNeeded.Needed)} → {edges : List (EdgeValue Symbol Guard)} →
        {before : State Symbol Guard} → {results : List (EdgeValue Symbol Guard)} → {after : State Symbol Guard} →
        RequireRows entries edges before results after → Memos → Memos → Prop where
    | nil : RowsReads .nil memos memos
    | rejected (rest : RowsReads restTrace memos saved) : RowsReads (.rejected rejected restTrace) memos saved
    | kept (children : ChildrenReads childTrace memos middleMemo) (rest : RowsReads restTrace middleMemo saved) :
        RowsReads (.kept fits childTrace rebuilt restTrace) memos saved
end

/-- Actual head exposure derives all three coherent tables through its final constructor. -/
theorem head_memos [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Head value before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (memos : Memos) (valid : Valid before memos) :
    ∃ saved, HeadReads trace memos saved ∧ Valid after saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases trace with
  | read fuel edges middle exposed rebuilt =>
      obtain ⟨saved, calls, coherent, retained⟩ :=
        SourceEqualityQueryGlobalMemos.exposure_memos fuel value before semantic costs available memos valid
      have read := SourceEqualityExposureCosts.nodeEdges_verified fuel value before semantic costs available
      have middleSemantic : SemanticReady middle := by
        simpa only [exposed, MergedSourceExposure.Result.state] using read.semantic
      have middleValid : Valid middle saved := by
        simpa only [exposed, MergedSourceExposure.Result.state] using coherent
      have constructor := SourceEqualityOpenOrdinaryHead.node edges middle middleSemantic (read.rows _ _ exposed)
      have finalValid := SourceQueryUnfoldMemo.valid_grows middle _ middleSemantic constructor.1 saved middleValid
      refine ⟨saved, .read (exposed := exposed) (rebuilt := rebuilt) calls, ?_, retained, calls.2⟩
      simpa only [rebuilt] using finalValid

private def NodeWitness [DecidableEq (EdgeKey Symbol Guard)]
    {needed : SourceEqualityNeeded.Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : RequireNode needed value before result after) : Prop :=
  SemanticReady before → CostHeap before → Available before value →
    ∀ memos : Memos, Valid before memos →
      ∃ saved, NodeReads trace memos saved ∧ Valid after saved ∧
        Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query

private def ChildrenWitness [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × SourceEqualityNeeded.Needed)} {index : Nat}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireChildren entries index values before results after) : Prop :=
  SemanticReady before → CostHeap before → Values before values →
    ∀ memos : Memos, Valid before memos →
      ∃ saved, ChildrenReads trace memos saved ∧ Valid after saved ∧
        Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query

private def RowsWitness [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × SourceEqualityNeeded.Needed)} {edges results : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} (trace : RequireRows entries edges before results after) : Prop :=
  SemanticReady before → CostHeap before → Edges before edges →
    ∀ memos : Memos, Valid before memos →
      ∃ saved, RowsReads trace memos saved ∧ Valid after saved ∧
        Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query

private theorem witnesses [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ needed (value : Value Symbol Guard) before result after
      (trace : RequireNode needed value before result after), NodeWitness trace) ∧
    (∀ entries index (values : List (Value Symbol Guard)) before results after
      (trace : RequireChildren entries index values before results after), ChildrenWitness trace) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after
      (trace : RequireRows entries edges before results after), RowsWitness trace) := by
  have identityCase : ∀ {value : Value Symbol Guard} {state},
      NodeWitness (RequireNode.identity (value := value) (state := state)) := by
    intro value state _ _ _ memos valid
    exact ⟨memos, .identity, valid, extends_refl _, rfl⟩
  have emptyCase : ∀ {entries : List (Int × SourceEqualityNeeded.Needed)} {state : State Symbol Guard}
      (nonempty : entries ≠ []), NodeWitness (RequireNode.empty (state := state) nonempty) := by
    intro entries state nonempty _ _ _ memos valid
    exact ⟨memos, .empty (nonempty := nonempty), valid, extends_refl _, rfl⟩
  have ordinaryCase : ∀ {entries edges before rebuilt middle result after entry depth free}
      (nonempty : entries ≠ []) (rows : RequireRows entries edges before rebuilt middle)
      (built : run (makeNode rebuilt) middle = (result, after)), RowsWitness rows →
      NodeWitness (.ordinary (entry := entry) (depth := depth) (free := free) nonempty rows built) := by
    intro entries edges before rebuilt middle result after entry depth free nonempty rows built ih semantic costs available memos valid
    have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    obtain ⟨saved, calls, coherent, retained, queries⟩ := ih semantic costs resident memos valid
    have effects := SourceCurrentRequiredHeapEffects.rows (fun _ => True) rows semantic costs
      (by intro _ _ _; trivial) resident
    have constructor := SourceEqualityOpenOrdinaryHead.node rebuilt middle effects.2.1 effects.2.2.2.2
    have finalValid := SourceQueryUnfoldMemo.valid_grows middle _ effects.2.1 constructor.1 saved coherent
    exact ⟨saved, .ordinary (nonempty := nonempty) (rebuilt := built) calls,
      by simpa only [built] using finalValid, retained, queries⟩
  have recursiveCase : ∀ {entries original before exposed middle result after}
      (nonempty : entries ≠ []) (recursive : Recursive original) (head : Head original before exposed middle)
      (body : RequireNode (.node entries) exposed middle result after),
      NodeWitness body → NodeWitness (.recursive nonempty recursive head body) := by
    intro entries original before exposed middle result after nonempty recursive head body ih semantic costs available memos valid
    obtain ⟨middleMemo, headCalls, middleValid, firstRetained, firstQueries⟩ :=
      head_memos head semantic costs available memos valid
    have effects := SourceCurrentRequiredHeapEffects.head (fun _ => True) head semantic costs
      (by intro _ _ _; trivial) available
    obtain ⟨saved, bodyCalls, finalValid, restRetained, restQueries⟩ :=
      ih effects.2.1 effects.2.2.1 effects.2.2.2.2 middleMemo middleValid
    exact ⟨saved, .recursive (nonempty := nonempty) (recursive := recursive) headCalls bodyCalls, finalValid,
      extends_trans firstRetained restRetained, restQueries.trans firstQueries⟩
  have nilChildren : ∀ {entries : List (Int × SourceEqualityNeeded.Needed)} {index : Nat} {state : State Symbol Guard},
      ChildrenWitness (RequireChildren.nil (entries := entries) (index := index) (state := state)) := by
    intro entries index state _ _ _ memos valid
    exact ⟨memos, .nil, valid, extends_refl _, rfl⟩
  have unselectedCase : ∀ {entries values before results after value} (index : Nat)
      (absent : SourceEqualityNeededMap.lookup (index : Int) entries = none)
      (rest : RequireChildren entries (index + 1) values before results after),
      ChildrenWitness rest → ChildrenWitness (.unselected (value := value) index absent rest) := by
    intro entries values before results after value index absent rest ih semantic costs available memos valid
    obtain ⟨saved, calls, coherent, retained, queries⟩ :=
      ih semantic costs (fun child member => available child (List.mem_cons_of_mem _ member)) memos valid
    exact ⟨saved, .unselected (absent := absent) calls, coherent, retained, queries⟩
  have selectedCase : ∀ {entries needed value before result middle values results after} (index : Nat)
      (found : SourceEqualityNeededMap.lookup (index : Int) entries = some needed)
      (first : RequireNode needed value before result middle)
      (rest : RequireChildren entries (index + 1) values middle results after),
      NodeWitness first → ChildrenWitness rest → ChildrenWitness (.selected index found first rest) := by
    intro entries needed value before result middle values results after index found first rest firstIH restIH semantic costs available memos valid
    have valueAvailable := available value List.mem_cons_self
    obtain ⟨middleMemo, firstCalls, middleValid, firstRetained, firstQueries⟩ := firstIH semantic costs valueAvailable memos valid
    have effects := SourceCurrentRequiredHeapEffects.node (fun _ => True) first semantic costs
      (by intro _ _ _; trivial) valueAvailable
    obtain ⟨saved, restCalls, finalValid, restRetained, restQueries⟩ := restIH effects.2.1 effects.2.2.1
      (fun child member => effects.1.available child (available child (List.mem_cons_of_mem _ member))) middleMemo middleValid
    exact ⟨saved, .selected (found := found) firstCalls restCalls, finalValid,
      extends_trans firstRetained restRetained, restQueries.trans firstQueries⟩
  have nilRows : ∀ {entries : List (Int × SourceEqualityNeeded.Needed)} {state : State Symbol Guard},
      RowsWitness (RequireRows.nil (entries := entries) (state := state)) := by
    intro entries state _ _ _ memos valid
    exact ⟨memos, .nil, valid, extends_refl _, rfl⟩
  have rejectedCase : ∀ {entries edges before results after} {edge : EdgeValue Symbol Guard}
      (rejected : SourceEqualityNeeded.fits (.node entries) edge.children.length = false)
      (rest : RequireRows entries edges before results after),
      RowsWitness rest → RowsWitness (.rejected rejected rest) := by
    intro entries edges before results after edge rejected rest ih semantic costs resident memos valid
    obtain ⟨saved, calls, coherent, retained, queries⟩ :=
      ih semantic costs (fun original member => resident original (List.mem_cons_of_mem _ member)) memos valid
    exact ⟨saved, .rejected (rejected := rejected) calls, coherent, retained, queries⟩
  have keptCase : ∀ {entries before values middle result afterEdge edges results after} {edge : EdgeValue Symbol Guard}
      (fits : SourceEqualityNeeded.fits (.node entries) edge.children.length = true)
      (children : RequireChildren entries 0 edge.children before values middle)
      (rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge))
      (rest : RequireRows entries edges afterEdge results after), ChildrenWitness children → RowsWitness rest →
      RowsWitness (.kept fits children rebuilt rest) := by
    intro entries before values middle result afterEdge edges results after edge fits children rebuilt rest childIH restIH semantic costs resident memos valid
    have available : Values before edge.children := semantic.ready.semantic.1.normal.facts.cached.edges
      edge.entry.key edge (resident edge List.mem_cons_self)
    obtain ⟨middleMemo, childCalls, middleValid, firstRetained, firstQueries⟩ := childIH semantic costs available memos valid
    have effects := SourceCurrentRequiredHeapEffects.children (fun _ => True) children semantic costs
      (by intro _ _ _; trivial) available
    have constructor := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle
      effects.2.1.ready effects.2.2.2.2
    have afterKept : Keeps middle afterEdge := by simpa only [rebuilt] using constructor.1
    have afterSemantic : SemanticReady afterEdge := by
      simpa only [rebuilt] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol
        edge.entry.key.constraint values middle effects.2.1 effects.2.2.2.2
    have afterCosts : CostHeap afterEdge := by
      have same : CostHeap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 := effects.2.2.1
      simpa only [rebuilt] using same
    have afterValid := SourceQueryUnfoldMemo.valid_grows middle afterEdge effects.2.1 afterKept middleMemo middleValid
    obtain ⟨saved, restCalls, finalValid, restRetained, restQueries⟩ := restIH afterSemantic afterCosts
      (fun original member => InternedEdgeResidency.edge_grows before afterEdge (effects.1.trans afterKept).growth original
        (resident original (List.mem_cons_of_mem _ member))) middleMemo afterValid
    exact ⟨saved, .kept (fits := fits) (rebuilt := rebuilt) childCalls restCalls, finalValid,
      extends_trans firstRetained restRetained, restQueries.trans firstQueries⟩
  refine ⟨?_, ?_, ?_⟩
  · intro needed value before result after trace
    exact RequireNode.rec
      (motive_1 := fun _ _ _ _ _ trace => NodeWitness trace)
      (motive_2 := fun _ _ _ _ _ _ trace => ChildrenWitness trace)
      (motive_3 := fun _ _ _ _ _ trace => RowsWitness trace)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase trace
  · intro entries index values before results after trace
    exact RequireChildren.rec
      (motive_1 := fun _ _ _ _ _ trace => NodeWitness trace)
      (motive_2 := fun _ _ _ _ _ _ trace => ChildrenWitness trace)
      (motive_3 := fun _ _ _ _ _ trace => RowsWitness trace)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase trace
  · intro entries edges before results after trace
    exact RequireRows.rec
      (motive_1 := fun _ _ _ _ _ trace => NodeWitness trace)
      (motive_2 := fun _ _ _ _ _ _ trace => ChildrenWitness trace)
      (motive_3 := fun _ _ _ _ _ trace => RowsWitness trace)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase trace

/-- Every completed required-node graph derives its actual coherent global memo calls. -/
theorem node_memos [DecidableEq (EdgeKey Symbol Guard)]
    {needed : SourceEqualityNeeded.Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : RequireNode needed value before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (memos : Memos) (valid : Valid before memos) :
    ∃ saved, NodeReads trace memos saved ∧ Valid after saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query :=
  witnesses.1 _ _ _ _ _ trace semantic costs available memos valid

/-- Every completed child graph derives ordered calls and coherence in its actual final heap. -/
theorem children_memos [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × SourceEqualityNeeded.Needed)} {index : Nat}
    {values results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireChildren entries index values before results after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (memos : Memos) (valid : Valid before memos) :
    ∃ saved, ChildrenReads trace memos saved ∧ Valid after saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query :=
  witnesses.2.1 _ _ _ _ _ _ trace semantic costs available memos valid

/-- Every completed row graph derives its original ordered unfolding calls and retained entries. -/
theorem rows_memos [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × SourceEqualityNeeded.Needed)} {edges results : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} (trace : RequireRows entries edges before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges)
    (memos : Memos) (valid : Valid before memos) :
    ∃ saved, RowsReads trace memos saved ∧ Valid after saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query :=
  witnesses.2.2 _ _ _ _ _ trace semantic costs resident memos valid

/-- Literal requireAll receipts use its actual compiled Needed child graph. -/
def RequireAllReads [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List (List Int)) (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (memos saved : Memos) : Prop :=
  match SourceEqualityNeeded.build paths with
  | .node entries => ∃ trace : RequireChildren entries 0 values before results after, ChildrenReads trace memos saved

/-- A completed literal requireAll derives coherent global tables without a future-validity premise. -/
theorem requireAll_memos [DecidableEq (EdgeKey Symbol Guard)]
    (fuel readFuel : Nat) (paths : List (List Int)) (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (memos : Memos) (valid : Valid before memos) :
    ∃ saved, RequireAllReads paths values results before after memos saved ∧ Valid after saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  have trace := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr ⟨fuel, readFuel, done⟩
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [compiled] at trace
      obtain ⟨saved, calls, coherent, retained, queries⟩ := children_memos trace semantic costs available memos valid
      exact ⟨saved, by simpa only [RequireAllReads, compiled] using ⟨trace, calls⟩, coherent, retained, queries⟩

end MicroCFTA.SourceCurrentRequiredQueryMemos
