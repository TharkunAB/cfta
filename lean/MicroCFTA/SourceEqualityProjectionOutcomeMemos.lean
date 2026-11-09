import MicroCFTA.SourceEqualityProjectionOutcomePrimitives
import MicroCFTA.SourceEqualityProjectionWorkerSound
import MicroCFTA.SourceEqualityProjectionCosts

/-!
# Ordered unfolding receipts for every literal projection outcome

The receipt retains each actual selected child and head read in order.
Completed prefixes pass their returned memo to the suffix. Pending records,
unresolved references, and both exhausted bounds retain their actual tags
and heaps. Current inputs derive physical effects and memo correctness.
The existing successful semantic projection graphs remain unchanged.
-/
namespace MicroCFTA.SourceEqualityProjectionOutcomeMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityRequiredWorker (Result)
open SourceEqualityProjectionWorker (project rows forest)
open SourceEqualityProjectionGraph (select select_member)
open SourceEqualityRequiredGraph (Recursive)
open SourceEqualityProjectionOutcomePrimitives (reached HeadReads UnionReads)
variable {Symbol Guard : Type}
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "UMemo" => InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard
local notation "Correct" => InternedFreshOrdinaryUnfoldMemo.Correct
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

mutual
/-- Node receipts preserve source branch priority and the exact first stopped prefix. -/
inductive ProjectReads [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → Nat → List Int → Node → Heap → UMemo → UMemo → Prop where
  | exhausted : ProjectReads 0 h path value before memo memo
  | root : ProjectReads (p + 1) h [] value before memo memo
  | empty : ProjectReads (p + 1) h (index :: path) .empty before memo memo
  | reference : ProjectReads (p + 1) h (index :: path) (.reference name) before memo memo
  | ordinary (scanned : rows (project p h path) index edges before = .done values middle)
      (first : RowsReads p h path index edges before memo middleMemo)
      (last : UnionReads h values middle middleMemo saved) :
      ProjectReads (p + 1) h (index :: path) (.node entry edges depth free) before memo saved
  | ordinary_pending (scanned : rows (project p h path) index edges before = .pending key after)
      (calls : RowsReads p h path index edges before memo saved) :
      ProjectReads (p + 1) h (index :: path) (.node entry edges depth free) before memo saved
  | ordinary_unresolved (scanned : rows (project p h path) index edges before = .unresolved name after)
      (calls : RowsReads p h path index edges before memo saved) :
      ProjectReads (p + 1) h (index :: path) (.node entry edges depth free) before memo saved
  | ordinary_exhausted (scanned : rows (project p h path) index edges before = .exhausted limit after)
      (calls : RowsReads p h path index edges before memo saved) :
      ProjectReads (p + 1) h (index :: path) (.node entry edges depth free) before memo saved
  | recursive (recursive : Recursive original) (exposed : SourceEqualityRequiredWorker.head h original before = .done value middle)
      (first : HeadReads h original before memo middleMemo)
      (last : ProjectReads p h (index :: path) value middle middleMemo saved) :
      ProjectReads (p + 1) h (index :: path) original before memo saved
  | recursive_pending (recursive : Recursive original) (exposed : SourceEqualityRequiredWorker.head h original before = .pending key after)
      (calls : HeadReads h original before memo saved) : ProjectReads (p + 1) h (index :: path) original before memo saved
  | recursive_unresolved (recursive : Recursive original) (exposed : SourceEqualityRequiredWorker.head h original before = .unresolved name after)
      (calls : HeadReads h original before memo saved) : ProjectReads (p + 1) h (index :: path) original before memo saved
  | recursive_exhausted (recursive : Recursive original) (exposed : SourceEqualityRequiredWorker.head h original before = .exhausted limit after)
      (calls : HeadReads h original before memo saved) : ProjectReads (p + 1) h (index :: path) original before memo saved

/-- Rows retain each selected child before its actual tail, including a stopped tail. -/
inductive RowsReads [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → Nat → List Int → Int → List Edge → Heap → UMemo → UMemo → Prop where
  | nil : RowsReads p h path index [] before memo memo
  | missing {edge : Edge} (absent : select edge.children index = none)
      (rest : RowsReads p h path index edges before memo saved) :
      RowsReads p h path index (edge :: edges) before memo saved
  | selected {edge : Edge} (found : select edge.children index = some child)
      (projected : project p h path child before = .done value middle)
      (first : ProjectReads p h path child before memo middleMemo)
      (rest : RowsReads p h path index edges middle middleMemo saved) :
      RowsReads p h path index (edge :: edges) before memo saved
  | pending {edge : Edge} (found : select edge.children index = some child)
      (projected : project p h path child before = .pending key after)
      (calls : ProjectReads p h path child before memo saved) :
      RowsReads p h path index (edge :: edges) before memo saved
  | unresolved {edge : Edge} (found : select edge.children index = some child)
      (projected : project p h path child before = .unresolved name after)
      (calls : ProjectReads p h path child before memo saved) :
      RowsReads p h path index (edge :: edges) before memo saved
  | exhausted {edge : Edge} (found : select edge.children index = some child)
      (projected : project p h path child before = .exhausted limit after)
      (calls : ProjectReads p h path child before memo saved) :
      RowsReads p h path index (edge :: edges) before memo saved
end

/-- Forest receipts preserve the root union, absent signed position, and actual selected node call. -/
inductive ForestReads [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → Nat → List Int → List Node → Heap → UMemo → UMemo → Prop where
  | root (calls : UnionReads h values before memo saved) : ForestReads p h [] values before memo saved
  | missing (absent : select values index = none) : ForestReads p h (index :: path) values before memo memo
  | selected (found : select values index = some value) (calls : ProjectReads p h path value before memo saved) :
      ForestReads p h (index :: path) values before memo saved

variable [DecidableEq (EdgeKey Symbol Guard)]

private structure Safe (before after : Heap) : Prop where
  keeps : Keeps before after
  semantic : SemanticReady after
  costs : CostHeap after

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem pure_safe (before : Heap) (semantic : SemanticReady before) (costs : CostHeap before) :
    Safe before before := ⟨pure_keeps _ semantic.ready, semantic, costs⟩

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem bind_safe {A B : Type} {before : Heap} {actual : Result Symbol Guard A}
    {next : A → Heap → Result Symbol Guard B} (first : Safe before (reached actual))
    (continuation : ∀ value after, actual = .done value after → Safe after (reached (next value after))) :
    Safe before (reached (actual.bind next)) := by
  cases actual with
  | done value after =>
      have last := continuation value after rfl
      exact ⟨first.keeps.trans last.keeps, last.semantic, last.costs⟩
  | pending key after => exact first
  | unresolved name after => exact first
  | exhausted limit after => exact first

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem map_reached {A B : Type} (actual : Result Symbol Guard A) (f : A → B) :
    reached (actual.bind fun value after => .done (f value) after) = reached actual := by
  cases actual <;> rfl

private theorem rows_safe (p h : Nat) (path : List Int)
    (smaller : ∀ (value : Node) (before : Heap), SemanticReady before → CostHeap before → Available before value →
      Safe before (reached (project p h path value before)))
    (index : Int) (edges : List Edge) (before : Heap) (semantic : SemanticReady before)
    (costs : CostHeap before) (resident : Edges before edges) :
    Safe before (reached (rows (project p h path) index edges before)) := by
  induction edges generalizing before with
  | nil => exact pure_safe before semantic costs
  | cons edge edges ih =>
      have tail := fun row member => resident row (List.mem_cons_of_mem _ member)
      cases found : select edge.children index with
      | none => simpa only [rows, found] using ih before semantic costs tail
      | some child =>
          rw [rows, found]
          have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
            (resident edge List.mem_cons_self) child (select_member found)
          have first := smaller child before semantic costs available
          apply bind_safe first
          intro value middle completed
          have kept : Safe before middle := by simpa only [completed, reached] using first
          have last := ih middle kept.semantic kept.costs
            (fun row member => InternedEdgeResidency.edge_grows before middle kept.keeps.growth row (tail row member))
          simpa only [map_reached] using last

private theorem project_safe (p h : Nat) (path : List Int) (value : Node) (before : Heap)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value) :
    Safe before (reached (project p h path value before)) := by
  induction p generalizing path value before with
  | zero => exact pure_safe before semantic costs
  | succ p ih =>
      cases path with
      | nil => exact pure_safe before semantic costs
      | cons index path =>
          have expose (original : Node) (present : Available before original) :
              Safe before (reached ((SourceEqualityRequiredWorker.head h original before).bind fun exposed after =>
                project p h (index :: path) exposed after)) := by
            have first := SourceEqualityProjectionOutcomePrimitives.head_effects h original before semantic costs present
            apply bind_safe ⟨first.1, first.2.1, first.2.2.1⟩
            intro exposed after completed
            have kept : Keeps before after ∧ SemanticReady after ∧ CostHeap after := by
              simpa only [completed, reached] using And.intro first.1 (And.intro first.2.1 first.2.2.1)
            exact ih (index :: path) exposed after kept.2.1 kept.2.2 (first.2.2.2 exposed after completed)
          cases value with
          | empty => exact pure_safe before semantic costs
          | reference name => exact pure_safe before semantic costs
          | node entry edges depth free =>
              rw [project]
              have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked
                (.node entry edges depth free) available.resident
              have first := rows_safe p h path (fun child after sem cost present => ih path child after sem cost present)
                index edges before semantic costs resident
              apply bind_safe first
              intro values after completed
              have kept : Safe before after := by simpa only [completed, reached] using first
              have graph := SourceEqualityProjectionWorkerSound.rows_graph (project p h path) path
                (fun child heap result returned done => SourceEqualityProjectionWorkerSound.project_graph p h path child heap result returned done)
                index edges before values after completed
              have inputs := (SourceEqualityProjectionCosts.rows_effects graph semantic costs resident).2.2.2
              have last := SourceEqualityProjectionOutcomePrimitives.union_effects h values after kept.semantic kept.costs inputs
              exact ⟨last.1, last.2.1, last.2.2.1⟩
          | mu entry body depth ordinary => exact expose (.mu entry body depth ordinary) available
          | union entry members depth free => exact expose (.union entry members depth free) available

/-- Every node outcome retains both current heaps and the actual successful value's residency. -/
theorem project_effects (p h : Nat) (path : List Int) (value : Node) (before : Heap)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value) :
    Keeps before (reached (project p h path value before)) ∧ SemanticReady (reached (project p h path value before)) ∧
      CostHeap (reached (project p h path value before)) ∧
      ∀ result after, project p h path value before = .done result after → Available after result := by
  have safe := project_safe p h path value before semantic costs available
  refine ⟨safe.keeps, safe.semantic, safe.costs, ?_⟩
  intro result after actual
  exact (SourceEqualityProjectionCosts.project_effects
    (SourceEqualityProjectionWorkerSound.project_graph p h path value before result after actual)
    semantic costs available).2.2.2

/-- Every row-scan outcome retains both heaps and all actual completed outputs. -/
theorem rows_effects (p h : Nat) (path : List Int) (index : Int) (edges : List Edge) (before : Heap)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges) :
    Keeps before (reached (rows (project p h path) index edges before)) ∧
      SemanticReady (reached (rows (project p h path) index edges before)) ∧
      CostHeap (reached (rows (project p h path) index edges before)) ∧
      ∀ results after, rows (project p h path) index edges before = .done results after → Values after results := by
  have safe := rows_safe p h path (fun value heap sem cost present => project_safe p h path value heap sem cost present)
    index edges before semantic costs resident
  refine ⟨safe.keeps, safe.semantic, safe.costs, ?_⟩
  intro results after actual
  exact (SourceEqualityProjectionCosts.rows_effects
    (SourceEqualityProjectionWorkerSound.rows_graph (project p h path) path
      (fun value heap result returned done => SourceEqualityProjectionWorkerSound.project_graph p h path value heap result returned done)
      index edges before results after actual) semantic costs resident).2.2.2

/-- Every literal forest outcome derives physical effects without a completed graph premise. -/
theorem forest_effects (p h : Nat) (path : List Int) (values : List Node) (before : Heap)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values) :
    Keeps before (reached (forest p h path values before)) ∧ SemanticReady (reached (forest p h path values before)) ∧
      CostHeap (reached (forest p h path values before)) ∧
      ∀ result after, forest p h path values before = .done result after → Available after result := by
  cases path with
  | nil => exact SourceEqualityProjectionOutcomePrimitives.union_effects h values before semantic costs available
  | cons index path =>
      cases found : select values index with
      | none =>
          simp only [forest, found, reached]
          refine ⟨pure_keeps _ semantic.ready, semantic, costs, ?_⟩
          intro result after actual
          cases actual
          exact empty_available _
      | some value =>
          simpa only [forest, found] using project_effects p h path value before semantic costs (available value (select_member found))

private theorem rows_memos_from (p h : Nat) (path : List Int)
    (smaller : ∀ (value : Node) (before : Heap), SemanticReady before → CostHeap before → Available before value →
      ∀ memo : UMemo, Correct before memo → ∃ saved, ProjectReads p h path value before memo saved ∧
        Correct (reached (project p h path value before)) saved ∧ Extends memo saved)
    (index : Int) (edges : List Edge) (before : Heap) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (memo : UMemo) (correct : Correct before memo) :
    ∃ saved, RowsReads p h path index edges before memo saved ∧
      Correct (reached (rows (project p h path) index edges before)) saved ∧ Extends memo saved := by
  induction edges generalizing before memo with
  | nil => exact ⟨memo, .nil, correct, extends_refl _⟩
  | cons edge edges ih =>
      have tail := fun row member => resident row (List.mem_cons_of_mem _ member)
      cases found : select edge.children index with
      | none =>
          obtain ⟨saved, calls, coherent, retained⟩ := ih before semantic costs tail memo correct
          exact ⟨saved, .missing found calls, by simpa only [rows, found] using coherent, retained⟩
      | some child =>
          have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
            (resident edge List.mem_cons_self) child (select_member found)
          obtain ⟨middleMemo, first, coherent, retained⟩ := smaller child before semantic costs available memo correct
          cases projected : project p h path child before with
          | pending key after =>
              exact ⟨middleMemo, .pending found projected first,
                by simpa only [rows, found, projected, Result.bind, reached] using coherent, retained⟩
          | unresolved name after =>
              exact ⟨middleMemo, .unresolved found projected first,
                by simpa only [rows, found, projected, Result.bind, reached] using coherent, retained⟩
          | exhausted limit after =>
              exact ⟨middleMemo, .exhausted found projected first,
                by simpa only [rows, found, projected, Result.bind, reached] using coherent, retained⟩
          | done value middle =>
              have currentCorrect : Correct middle middleMemo := by simpa only [projected, reached] using coherent
              have firstEffects := project_effects p h path child before semantic costs available
              have current : Keeps before middle ∧ SemanticReady middle ∧ CostHeap middle := by
                simpa only [projected, reached] using And.intro firstEffects.1 (And.intro firstEffects.2.1 firstEffects.2.2.1)
              obtain ⟨saved, last, finalCorrect, finalRetained⟩ := ih middle current.2.1 current.2.2
                (fun row member => InternedEdgeResidency.edge_grows before middle current.1.growth row (tail row member))
                middleMemo currentCorrect
              refine ⟨saved, .selected found projected first last, ?_, extends_trans retained finalRetained⟩
              have mapped : Correct (reached ((rows (project p h path) index edges middle).bind
                  fun values after => .done (value :: values) after)) saved := by
                rw [map_reached]
                exact finalCorrect
              simpa only [rows, found, projected, Result.bind] using mapped

/-- Literal node execution derives ordered receipts and a correct memo on every outcome. -/
theorem project_memos (p h : Nat) (path : List Int) (value : Node) (before : Heap)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (memo : UMemo) (correct : Correct before memo) :
    ∃ saved, ProjectReads p h path value before memo saved ∧
      Correct (reached (project p h path value before)) saved ∧ Extends memo saved := by
  induction p generalizing path value before memo with
  | zero => exact ⟨memo, .exhausted, correct, extends_refl _⟩
  | succ p ih =>
      cases path with
      | nil => exact ⟨memo, .root, correct, extends_refl _⟩
      | cons index path =>
          have expose (original : Node) (recursive : Recursive original) (present : Available before original) :
              ∃ saved, ProjectReads (p + 1) h (index :: path) original before memo saved ∧
                Correct (reached ((SourceEqualityRequiredWorker.head h original before).bind fun exposed after => project p h (index :: path) exposed after)) saved ∧
                Extends memo saved := by
            obtain ⟨middleMemo, first, coherent, retained⟩ :=
              SourceEqualityProjectionOutcomePrimitives.head_memos h original before semantic costs present memo correct
            cases exposed : SourceEqualityRequiredWorker.head h original before with
            | pending key after =>
                exact ⟨middleMemo, .recursive_pending recursive exposed first,
                  by simpa only [exposed, Result.bind, reached] using coherent, retained⟩
            | unresolved name after =>
                exact ⟨middleMemo, .recursive_unresolved recursive exposed first,
                  by simpa only [exposed, Result.bind, reached] using coherent, retained⟩
            | exhausted limit after =>
                exact ⟨middleMemo, .recursive_exhausted recursive exposed first,
                  by simpa only [exposed, Result.bind, reached] using coherent, retained⟩
            | done value middle =>
                have currentCorrect : Correct middle middleMemo := by simpa only [exposed, reached] using coherent
                have firstEffects := SourceEqualityProjectionOutcomePrimitives.head_effects h original before semantic costs present
                have current : Keeps before middle ∧ SemanticReady middle ∧ CostHeap middle := by
                  simpa only [exposed, reached] using And.intro firstEffects.1 (And.intro firstEffects.2.1 firstEffects.2.2.1)
                obtain ⟨saved, last, finalCorrect, finalRetained⟩ := ih (index :: path) value middle current.2.1 current.2.2
                  (firstEffects.2.2.2 value middle exposed) middleMemo currentCorrect
                exact ⟨saved, .recursive recursive exposed first last,
                  by simpa only [exposed, Result.bind] using finalCorrect, extends_trans retained finalRetained⟩
          cases value with
          | empty => exact ⟨memo, .empty, correct, extends_refl _⟩
          | reference name => exact ⟨memo, .reference, correct, extends_refl _⟩
          | mu entry body depth ordinary => exact expose (.mu entry body depth ordinary) True.intro available
          | union entry members depth free => exact expose (.union entry members depth free) True.intro available
          | node entry edges depth free =>
              have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked
                (.node entry edges depth free) available.resident
              obtain ⟨middleMemo, first, coherent, retained⟩ := rows_memos_from p h path
                (fun child heap sem cost present old valid => ih path child heap sem cost present old valid)
                index edges before semantic costs resident memo correct
              cases scanned : rows (project p h path) index edges before with
              | pending key after =>
                  exact ⟨middleMemo, .ordinary_pending scanned first,
                    by simpa only [project, scanned, Result.bind, reached] using coherent, retained⟩
              | unresolved name after =>
                  exact ⟨middleMemo, .ordinary_unresolved scanned first,
                    by simpa only [project, scanned, Result.bind, reached] using coherent, retained⟩
              | exhausted limit after =>
                  exact ⟨middleMemo, .ordinary_exhausted scanned first,
                    by simpa only [project, scanned, Result.bind, reached] using coherent, retained⟩
              | done values middle =>
                  have currentCorrect : Correct middle middleMemo := by simpa only [scanned, reached] using coherent
                  have firstEffects := rows_effects p h path index edges before semantic costs resident
                  have current : Keeps before middle ∧ SemanticReady middle ∧ CostHeap middle := by
                    simpa only [scanned, reached] using And.intro firstEffects.1 (And.intro firstEffects.2.1 firstEffects.2.2.1)
                  obtain ⟨saved, last, finalCorrect, finalRetained⟩ := SourceEqualityProjectionOutcomePrimitives.union_memos
                    h values middle current.2.1 current.2.2 (firstEffects.2.2.2 values middle scanned) middleMemo currentCorrect
                  exact ⟨saved, .ordinary scanned first last,
                    by simpa only [project, scanned, Result.bind] using finalCorrect, extends_trans retained finalRetained⟩

/-- Literal row execution derives only the selected calls and retains every actual stopped prefix. -/
theorem rows_memos (p h : Nat) (path : List Int) (index : Int) (edges : List Edge) (before : Heap)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges)
    (memo : UMemo) (correct : Correct before memo) :
    ∃ saved, RowsReads p h path index edges before memo saved ∧
      Correct (reached (rows (project p h path) index edges before)) saved ∧ Extends memo saved :=
  rows_memos_from p h path (fun value heap sem cost present old valid => project_memos p h path value heap sem cost present old valid)
    index edges before semantic costs resident memo correct

/-- Original current forest inputs derive ordered memo receipts at every literal returned heap. -/
theorem forest_memos (p h : Nat) (path : List Int) (values : List Node) (before : Heap)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (memo : UMemo) (correct : Correct before memo) :
    ∃ saved, ForestReads p h path values before memo saved ∧
      Correct (reached (forest p h path values before)) saved ∧ Extends memo saved := by
  cases path with
  | nil =>
      obtain ⟨saved, calls, coherent, retained⟩ :=
        SourceEqualityProjectionOutcomePrimitives.union_memos h values before semantic costs available memo correct
      exact ⟨saved, .root calls, coherent, retained⟩
  | cons index path =>
      cases found : select values index with
      | none =>
          exact ⟨memo, .missing found, by simpa only [forest, found, reached] using correct, extends_refl _⟩
      | some value =>
          obtain ⟨saved, calls, coherent, retained⟩ :=
            project_memos p h path value before semantic costs (available value (select_member found)) memo correct
          exact ⟨saved, .selected found calls, by simpa only [forest, found] using coherent, retained⟩

end MicroCFTA.SourceEqualityProjectionOutcomeMemos
