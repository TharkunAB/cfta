import MicroCFTA.SourceEqualityExposureMemos
import MicroCFTA.SourceEqualityProjectionCosts

/-!
# Ordered unfolding memo receipts for actual projections

Each receipt follows an actual projection graph. Row exposure records its
global unfolding calls. Head and union construction retain the same table.
Selected children and rows pass returned tables in source order. Current
semantic and cost effects derive every intermediate memo premise.
-/
namespace MicroCFTA.SourceEqualityProjectionMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceEqualityRequiredHead (Head)
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo
local notation "Correct" => InternedFreshOrdinaryUnfoldMemo.Correct
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A completed row read records its actual bounded exposure calls. -/
inductive ReadReads [DecidableEq (EdgeKey Symbol Guard)] :
    {value : Value Symbol Guard} → {before : State Symbol Guard} → {edges : List (EdgeValue Symbol Guard)} →
      {after : State Symbol Guard} → Read value before edges after → UMemo Symbol Guard → UMemo Symbol Guard → Prop where
  | done {fuel : Nat} {value : Value Symbol Guard} {before after : State Symbol Guard}
      {edges : List (EdgeValue Symbol Guard)}
      {actual : MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done edges after}
      {memo saved : UMemo Symbol Guard}
      (calls : SourceEqualityExposureMemos.NodeEdgesReads fuel value before memo saved) :
      ReadReads (.done fuel actual) memo saved

/-- A head read records row exposure before constructor-only node rebuilding. -/
inductive HeadReads [DecidableEq (EdgeKey Symbol Guard)] :
    {value : Value Symbol Guard} → {before : State Symbol Guard} → {result : Value Symbol Guard} →
      {after : State Symbol Guard} → Head value before result after → UMemo Symbol Guard → UMemo Symbol Guard → Prop where
  | read {fuel : Nat} {value result : Value Symbol Guard} {before middle after : State Symbol Guard}
      {edges : List (EdgeValue Symbol Guard)}
      {exposed : MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done edges middle}
      {rebuilt : run (makeNode edges) middle = (result, after)} {memo saved : UMemo Symbol Guard}
      (calls : ReadReads (.done fuel exposed) memo saved) :
      HeadReads (.read fuel edges middle exposed rebuilt) memo saved

/-- Ordered source union reads pass each returned memo to the next operand. -/
inductive ReadAllReads [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {before : State Symbol Guard} → {edges : List (EdgeValue Symbol Guard)} →
      {after : State Symbol Guard} → ReadAll values before edges after → UMemo Symbol Guard → UMemo Symbol Guard → Prop where
  | nil : ReadAllReads .nil memo memo
  | cons (first : ReadReads firstTrace memo middleMemo) (rest : ReadAllReads restTrace middleMemo saved) :
      ReadAllReads (.cons firstTrace restTrace) memo saved

/-- A source union retains all row-read calls and makes no extra unfolding call at makeNode. -/
inductive UnionReads [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {before : State Symbol Guard} → {result : Value Symbol Guard} →
      {after : State Symbol Guard} → Union values before result after → UMemo Symbol Guard → UMemo Symbol Guard → Prop where
  | node {values : List (Value Symbol Guard)} {before middle after : State Symbol Guard}
      {edges : List (EdgeValue Symbol Guard)} {result : Value Symbol Guard}
      {read : ReadAll values before edges middle} {built : run (makeNode edges) middle = (result, after)}
      {memo saved : UMemo Symbol Guard} (calls : ReadAllReads read memo saved) : UnionReads (.node read built) memo saved

mutual
/-- One actual projection records each unfolding call in its original order. -/
inductive ProjectReads [DecidableEq (EdgeKey Symbol Guard)] :
    {path : List Int} → {value : Value Symbol Guard} → {before : State Symbol Guard} →
      {result : Value Symbol Guard} → {after : State Symbol Guard} →
      Project path value before result after → UMemo Symbol Guard → UMemo Symbol Guard → Prop where
  | root : ProjectReads .root memo memo
  | empty : ProjectReads .empty memo memo
  | ordinary (rows : RowsReads rowsTrace memo middleMemo) (union : UnionReads unionTrace middleMemo saved) :
      ProjectReads (.ordinary rowsTrace unionTrace) memo saved
  | recursive (head : HeadReads headTrace memo middleMemo) (body : ProjectReads bodyTrace middleMemo saved) :
      ProjectReads (.recursive recursive headTrace bodyTrace) memo saved

/-- Missing positions make no call; selected rows pass their returned memo to the remaining rows. -/
inductive RowsReads [DecidableEq (EdgeKey Symbol Guard)] :
    {path : List Int} → {index : Int} → {edges : List (EdgeValue Symbol Guard)} → {before : State Symbol Guard} →
      {results : List (Value Symbol Guard)} → {after : State Symbol Guard} →
      ProjectRows path index edges before results after → UMemo Symbol Guard → UMemo Symbol Guard → Prop where
  | nil : RowsReads .nil memo memo
  | missing (rest : RowsReads restTrace memo saved) : RowsReads (.missing absent restTrace) memo saved
  | selected (first : ProjectReads firstTrace memo middleMemo) (rest : RowsReads restTrace middleMemo saved) :
      RowsReads (.selected found firstTrace restTrace) memo saved
end

/-- Forest projection retains its distinct root union, missing lookup, and selected call. -/
inductive ForestReads [DecidableEq (EdgeKey Symbol Guard)] :
    {path : List Int} → {values : List (Value Symbol Guard)} → {before : State Symbol Guard} →
      {result : Value Symbol Guard} → {after : State Symbol Guard} →
      Forest path values before result after → UMemo Symbol Guard → UMemo Symbol Guard → Prop where
  | root (calls : UnionReads union memo saved) : ForestReads (.root union) memo saved
  | missing : ForestReads (.missing absent) memo memo
  | selected (calls : ProjectReads body memo saved) : ForestReads (.selected found body) memo saved

/-- An actual complete row read derives coherent ordered memo calls and retains earlier entries. -/
theorem read_reads [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : Read value before edges after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (memo : UMemo Symbol Guard) (correct : Correct before memo) :
    ∃ saved, ReadReads trace memo saved ∧ Correct after saved ∧ Extends memo saved := by
  cases trace with
  | done fuel actual =>
      obtain ⟨saved, calls, coherent, retained⟩ :=
        SourceEqualityExposureMemos.nodeEdges_reads fuel value before semantic costs available memo correct
      exact ⟨saved, .done (actual := actual) calls, by simpa only [actual, MergedSourceExposure.Result.state] using coherent, retained⟩

private theorem node_correct [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (resident : Edges before edges)
    (memo : UMemo Symbol Guard) (correct : Correct before memo) :
    Correct (run (makeNode edges) before).2 memo := by
  have actual := SourceEqualityOpenOrdinaryHead.node edges before semantic resident
  exact InternedFreshOrdinaryUnfoldMemo.grows before _ semantic.ready.semantic.1.normal.facts.coherent.valid
    actual.1.growth actual.1.history memo correct

/-- Actual head rebuilding retains the returned row-read memo through its constructor-only suffix. -/
theorem head_reads [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Head value before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (memo : UMemo Symbol Guard) (correct : Correct before memo) :
    ∃ saved, HeadReads trace memo saved ∧ Correct after saved ∧ Extends memo saved := by
  cases trace with
  | read fuel edges middle exposed rebuilt =>
      obtain ⟨saved, calls, coherent, retained⟩ := read_reads (.done fuel exposed) semantic costs available memo correct
      have effects := SourceEqualityProjectionCosts.read_effects (.done fuel exposed) semantic costs available
      have finalCorrect := node_correct edges middle effects.2.1 effects.2.2.2 saved coherent
      have same := congrArg Prod.snd rebuilt
      dsimp only at same
      exact ⟨saved, .read (exposed := exposed) (rebuilt := rebuilt) calls, same ▸ finalCorrect, retained⟩

/-- Actual ordered union operand reads derive each intermediate memo from current effects. -/
theorem readAll_reads [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : ReadAll values before edges after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (memo : UMemo Symbol Guard) (correct : Correct before memo) :
    ∃ saved, ReadAllReads trace memo saved ∧ Correct after saved ∧ Extends memo saved := by
  revert correct memo available costs semantic
  induction trace with
  | nil => intro _ _ _ memo correct; exact ⟨memo, .nil, correct, extends_refl _⟩
  | cons first rest ih =>
      intro semantic costs available memo correct
      obtain ⟨middleMemo, firstCalls, middleCorrect, firstRetained⟩ :=
        read_reads first semantic costs (available _ List.mem_cons_self) memo correct
      have effects := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
      obtain ⟨saved, restCalls, finalCorrect, restRetained⟩ := ih effects.2.1 effects.2.2.1
        (fun child member => effects.1.available child (available child (List.mem_cons_of_mem _ member))) middleMemo middleCorrect
      exact ⟨saved, .cons firstCalls restCalls, finalCorrect, extends_trans firstRetained restRetained⟩

/-- An actual source union retains the last read memo through its exact node construction. -/
theorem union_reads [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (trace : Union values before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (memo : UMemo Symbol Guard) (correct : Correct before memo) :
    ∃ saved, UnionReads trace memo saved ∧ Correct after saved ∧ Extends memo saved := by
  cases trace with
  | node read built =>
      obtain ⟨saved, calls, coherent, retained⟩ := readAll_reads read semantic costs available memo correct
      have effects := SourceEqualityProjectionCosts.readAll_effects read semantic costs available
      have finalCorrect := node_correct _ _ effects.2.1 effects.2.2.2 saved coherent
      have same := congrArg Prod.snd built
      dsimp only at same
      exact ⟨saved, .node (read := read) (built := built) calls, same ▸ finalCorrect, retained⟩

private def NodeWitness [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project path value before result after) : Prop :=
  SemanticReady before → CostHeap before → Available before value →
    ∀ memo : UMemo Symbol Guard, Correct before memo →
      ∃ saved, ProjectReads trace memo saved ∧ Correct after saved ∧ Extends memo saved

private def RowsWitness [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)} {results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (trace : ProjectRows path index edges before results after) : Prop :=
  SemanticReady before → CostHeap before → Edges before edges →
    ∀ memo : UMemo Symbol Guard, Correct before memo →
      ∃ saved, RowsReads trace memo saved ∧ Correct after saved ∧ Extends memo saved

private theorem witnesses [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ path (value : Value Symbol Guard) before result after (trace : Project path value before result after), NodeWitness trace) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after
      (trace : ProjectRows path index edges before results after), RowsWitness trace) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeWitness (Project.root (value := value) (state := state)) := by
    intro value state semantic costs available memo correct
    exact ⟨memo, .root, correct, extends_refl _⟩
  have emptyCase : ∀ {index path} {state : State Symbol Guard},
      NodeWitness (Project.empty (index := index) (path := path) (state := state)) := by
    intro index path state semantic costs available memo correct
    exact ⟨memo, .empty, correct, extends_refl _⟩
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free}
      (rows : ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle)
      (union : Union values middle result after), RowsWitness rows →
      NodeWitness (Project.ordinary (entry := entry) (depth := depth) (free := free) rows union) := by
    intro path index edges before values middle result after entry depth free rows union ih semantic costs available memo correct
    have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have effects := SourceEqualityProjectionCosts.rows_effects rows semantic costs resident
    obtain ⟨middleMemo, rowsCalls, middleCorrect, firstRetained⟩ := ih semantic costs resident memo correct
    obtain ⟨saved, unionCalls, finalCorrect, restRetained⟩ :=
      union_reads union effects.2.1 effects.2.2.1 effects.2.2.2 middleMemo middleCorrect
    exact ⟨saved, .ordinary rowsCalls unionCalls, finalCorrect, extends_trans firstRetained restRetained⟩
  have recursiveCase : ∀ {original before exposed middle path index result after}
      (recursive : SourceEqualityRequiredGraph.Recursive original) (head : Head original before exposed middle)
      (body : Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after),
      NodeWitness body → NodeWitness (.recursive recursive head body) := by
    intro original before exposed middle path index result after recursive head body ih semantic costs available memo correct
    have effects := SourceEqualityProjectionCosts.head_effects head semantic costs available
    obtain ⟨middleMemo, headCalls, middleCorrect, firstRetained⟩ := head_reads head semantic costs available memo correct
    obtain ⟨saved, bodyCalls, finalCorrect, restRetained⟩ :=
      ih effects.2.1 effects.2.2.1 effects.2.2.2 middleMemo middleCorrect
    exact ⟨saved, .recursive (recursive := recursive) headCalls bodyCalls, finalCorrect, extends_trans firstRetained restRetained⟩
  have nilCase : ∀ {path index} {state : State Symbol Guard},
      RowsWitness (ProjectRows.nil (path := path) (index := index) (state := state)) := by
    intro path index state semantic costs resident memo correct
    exact ⟨memo, .nil, correct, extends_refl _⟩
  have missingCase : ∀ {edge : EdgeValue Symbol Guard} {path index edges before results after} (absent : select edge.children index = none)
      (rest : ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after),
      RowsWitness rest → RowsWitness (.missing absent rest) := by
    intro edge path index edges before results after absent rest ih semantic costs resident memo correct
    obtain ⟨saved, calls, coherent, retained⟩ :=
      ih semantic costs (fun value member => resident value (List.mem_cons_of_mem _ member)) memo correct
    exact ⟨saved, .missing (absent := absent) calls, coherent, retained⟩
  have selectedCase : ∀ {edge : EdgeValue Symbol Guard} {index child path before result middle edges results after}
      (found : select edge.children index = some child)
      (first : Project (Symbol := Symbol) (Guard := Guard) path child before result middle)
      (rest : ProjectRows path index edges middle results after),
      NodeWitness first → RowsWitness rest → RowsWitness (.selected found first rest) := by
    intro edge index child path before result middle edges results after found first rest firstIH restIH semantic costs resident memo correct
    have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
      (resident edge List.mem_cons_self) child (select_member found)
    have effects := SourceEqualityProjectionCosts.project_effects first semantic costs available
    obtain ⟨middleMemo, firstCalls, middleCorrect, firstRetained⟩ := firstIH semantic costs available memo correct
    obtain ⟨saved, restCalls, finalCorrect, restRetained⟩ := restIH effects.2.1 effects.2.2.1
      (fun edge present => InternedEdgeResidency.edge_grows before middle effects.1.growth edge
        (resident edge (List.mem_cons_of_mem _ present))) middleMemo middleCorrect
    exact ⟨saved, .selected (found := found) firstCalls restCalls, finalCorrect, extends_trans firstRetained restRetained⟩
  constructor
  · intro path value before result after trace
    exact Project.rec (motive_1 := fun _ _ _ _ _ trace => NodeWitness trace)
      (motive_2 := fun _ _ _ _ _ _ trace => RowsWitness trace)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace
  · intro path index edges before results after trace
    exact ProjectRows.rec (motive_1 := fun _ _ _ _ _ trace => NodeWitness trace)
      (motive_2 := fun _ _ _ _ _ _ trace => RowsWitness trace)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace

/-- Actual completed projection derives coherent unfolding calls without a closed-input premise. -/
theorem project_reads [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project path value before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (memo : UMemo Symbol Guard) (correct : Correct before memo) :
    ∃ saved, ProjectReads trace memo saved ∧ Correct after saved ∧ Extends memo saved :=
  witnesses.1 _ _ _ _ _ trace semantic costs available memo correct

/-- Actual selected-row traversal derives its ordered calls and retains every earlier memo entry. -/
theorem rows_reads [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)} {results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (trace : ProjectRows path index edges before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges)
    (memo : UMemo Symbol Guard) (correct : Correct before memo) :
    ∃ saved, RowsReads trace memo saved ∧ Correct after saved ∧ Extends memo saved :=
  witnesses.2 _ _ _ _ _ _ trace semantic costs resident memo correct

/-- Every actual forest projection derives a coherent returned memo at its exact final heap. -/
theorem forest_reads [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Forest path values before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (memo : UMemo Symbol Guard) (correct : Correct before memo) :
    ∃ saved, ForestReads trace memo saved ∧ Correct after saved ∧ Extends memo saved := by
  cases trace with
  | root union =>
      obtain ⟨saved, calls, coherent, retained⟩ := union_reads union semantic costs available memo correct
      exact ⟨saved, .root calls, coherent, retained⟩
  | missing absent => exact ⟨memo, .missing (absent := absent), correct, extends_refl _⟩
  | selected found body =>
      obtain ⟨saved, calls, coherent, retained⟩ :=
        project_reads body semantic costs (available _ (select_member found)) memo correct
      exact ⟨saved, .selected (found := found) calls, coherent, retained⟩

end MicroCFTA.SourceEqualityProjectionMemos
