import MicroCFTA.SourceCurrentMemoMergeGraph
import MicroCFTA.SourceCurrentConjunctionRowsAllocation
import MicroCFTA.SourceEqualityMkEdgeAllocation

/-!
# Completed merge calls with actual Top-field allocation

Large rows intern the canonical empty equality field before their raw edge
request. Small rows retain their stored field. Completed hits skip the body.
Erasure retains the constructor heap, the result, and the merge memo.
This graph uses the existing column-first completed serial schedule.
It does not establish GHC forcing order or pending memo publication.
The comparison predicate remains an explicit parameter.
-/
namespace MicroCFTA.SourceCurrentAllocatedMergeGraph
open Cache InternedConstructorTemplates
open MergedOrdinaryHeight (recursiveBoundary ordinaryUnion)
namespace Old
export SourceCurrentMemoMergeGraph (Entry Memo remember winner)
end Old
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
abbrev State := SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
abbrev Memo := Old.Memo Symbol Guard
abbrev top : Guard := SourceEqualityConstraintConstructors.top

/-- Instructions distinguish direct Top construction from unchanged raw work. -/
inductive Code : Type → Type 1 where
  | pure (value : Result) : Code Result
  | work (job : Work Symbol Guard Result) : Code Result
  | topRow (symbol : Symbol) (children : List (Value Symbol Guard)) : Code (EdgeValue Symbol Guard)
  | select (inputs : List (Value Symbol Guard)) : Code (List (Value Symbol Guard))
  | request (input : Value Symbol Guard) : Code (Value Symbol Guard)
  | bind (first : Code First) (next : First → Code Result) : Code Result

/-- Ordered maps retain each returned physical state and merge memo. -/
def map (call : Input → Code Output) : List Input → Code (List Output)
  | [] => .pure []
  | first :: rest => .bind (call first) fun value => .bind (map call rest) fun values => .pure (value :: values)

/-- Singleton and recursive-boundary branches retain the original column logic. -/
def retainedColumn (retained : List (Value Symbol Guard)) : Code (Value Symbol Guard) :=
  match retained with
  | [single] => .pure single
  | others => if others.any recursiveBoundary then .work (makeUnion others)
    else .bind (.work (ordinaryUnion others)) Code.request

/-- Small rows retain their original complete field after recursive child calls. -/
def small (edge : EdgeValue Symbol Guard) : Code (EdgeValue Symbol Guard) :=
  .bind (map Code.request edge.children) fun children =>
    .work (makeEdge edge.entry.key.symbol edge.entry.key.constraint children)

/-- Actual selection precedes retained-column normalization. -/
def column (inputs : List (Value Symbol Guard)) : Code (Value Symbol Guard) :=
  .bind (.select inputs) retainedColumn

/-- The completed serial schedule allocates the Top field after its columns. -/
def large (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) : Code (EdgeValue Symbol Guard) :=
  .bind (map column
    (MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length))
    fun children => .topRow first.entry.key.symbol children

/-- The threshold retains at most four rows and merges larger groups. -/
def group (edges : List (EdgeValue Symbol Guard)) : Code (List (EdgeValue Symbol Guard)) :=
  if edges.length ≤ 4 then map small edges
  else match edges with
  | [] => .pure []
  | first :: rest => .bind (large first rest) fun edge => .pure [edge]

/-- Final node construction follows the actual ordered group results. -/
def root (groups : List (List (EdgeValue Symbol Guard))) : Code (Value Symbol Guard) :=
  .bind (map group groups) fun rows => .work (makeNode rows.flatten)

/-- Only closed ordinary inputs enter grouping. -/
def body [DecidableEq Symbol] (input : Value Symbol Guard) : Code (Value Symbol Guard) :=
  match input with
  | .node _ edges _ free => if free = [] then root (MergedSourceGrouping.groups edges) else .pure input
  | _ => .pure input

/-- Erasure removes only the separate equality allocation instruction. -/
def erase : Code Output → SourceCurrentMemoMergeGraph.Code Symbol Guard Output
  | .pure value => .pure value
  | .work job => .work job
  | .topRow symbol children => .work (makeEdge symbol top children)
  | .select inputs => .select inputs
  | .request input => .request input
  | .bind first next => .bind (erase first) (fun value => erase (next value))

theorem erase_map (call : Input → Code Output) (inputs : List Input) :
    erase (map call inputs) = SourceCurrentMemoMergeGraph.map (fun input => erase (call input)) inputs := by
  induction inputs with
  | nil => rfl
  | cons first rest ih => simp only [map, erase, ih, SourceCurrentMemoMergeGraph.map]

theorem erase_retainedColumn (inputs : List (Value Symbol Guard)) :
    erase (retainedColumn inputs) = SourceCurrentMemoMergeGraph.retainedColumn inputs := by
  cases inputs with
  | nil => simp only [retainedColumn, SourceCurrentMemoMergeGraph.retainedColumn]; split <;> rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second rest => simp only [retainedColumn, SourceCurrentMemoMergeGraph.retainedColumn]; split <;> rfl

theorem erase_small (edge : EdgeValue Symbol Guard) : erase (small edge) = SourceCurrentMemoMergeGraph.small edge := by
  simp only [small, erase, erase_map, SourceCurrentMemoMergeGraph.small]

theorem erase_column (inputs : List (Value Symbol Guard)) : erase (column inputs) = SourceCurrentMemoMergeGraph.column inputs := by
  simp only [column, erase, erase_retainedColumn, SourceCurrentMemoMergeGraph.column]

theorem erase_large (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) :
    erase (large first rest) = SourceCurrentMemoMergeGraph.large top first rest := by
  simp only [large, erase, erase_map, erase_column, SourceCurrentMemoMergeGraph.large]

theorem erase_group (edges : List (EdgeValue Symbol Guard)) :
    erase (group edges) = SourceCurrentMemoMergeGraph.group top edges := by
  unfold group SourceCurrentMemoMergeGraph.group
  split
  · simp only [erase_map, erase_small]
  · cases edges with
    | nil => rfl
    | cons first rest => simp only [erase, erase_large]

theorem erase_root (groups : List (List (EdgeValue Symbol Guard))) :
    erase (root groups) = SourceCurrentMemoMergeGraph.root top groups := by
  simp only [root, erase, erase_map, erase_group, SourceCurrentMemoMergeGraph.root]

theorem erase_body [DecidableEq Symbol] (input : Value Symbol Guard) :
    erase (body input) = SourceCurrentMemoMergeGraph.body top input := by
  cases input <;> simp only [body, SourceCurrentMemoMergeGraph.body, erase]
  split <;> simp only [erase_root, erase]

mutual
  /-- Actual instructions retain the complete constructor and equality states. -/
  inductive Run [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) :
      {Output : Type} → Code Output → State → Memo → Output → State → Memo → Prop where
    | pure (value : Output) (state : State) (memo : Memo) : Run clear (.pure value) state memo value state memo
    | work (job : Work Symbol Guard Output) (state : State) (memo : Memo) :
        Run clear (.work job) state memo (run job state.heap).1 ⟨(run job state.heap).2, state.equality⟩ memo
    | topRow (symbol : Symbol) (children : List (Value Symbol Guard)) (state : State) (memo : Memo) :
        Run clear (.topRow symbol children) state memo (run (makeEdge symbol top children) state.heap).1
          ⟨(run (makeEdge symbol top children) state.heap).2, SourceEqualityMkEdgeAllocation.emptyField state.equality⟩ memo
    | select (fuel : Nat) (done : SourceMergedSelection.select clear fuel inputs before.heap = .done values heap) :
        Run clear (.select inputs) before memo values ⟨heap, before.equality⟩ memo
    | request (actual : Call clear input before memo output after saved) :
        Run clear (.request input) before memo output after saved
    | bind (first : Run clear code before memo value middle current)
        (later : Run clear (next value) middle current output after saved) :
        Run clear (.bind code next) before memo output after saved

  /-- Completed hits are unchanged. Misses run the allocated body and reread the winner. -/
  inductive Call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) :
      Value Symbol Guard → State → Memo → Value Symbol Guard → State → Memo → Prop where
    | hit (found : memo input.referenceOf = some entry) : Call clear input before memo entry.result before memo
    | miss (absent : memo input.referenceOf = none) (actual : Run clear (body input) before memo candidate after current) :
        Call clear input before memo (Old.winner current input candidate).result after (Old.remember current input candidate)
end

/-- Erasure preserves the exact old heap graph, result, and completed memo. -/
theorem Run.graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {code : Code Output} {before after : State} {memo saved : Memo} {output : Output}
    (actual : Run clear code before memo output after saved) :
    SourceCurrentMemoMergeGraph.Run clear top (erase code) before.heap memo output after.heap saved := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ =>
        SourceCurrentMemoMergeGraph.Call clear top input before.heap memo output after.heap saved) with
  | pure => exact .pure _ _ _
  | work => exact .work _ _ _
  | topRow => exact .work _ _ _
  | select fuel done => exact .select fuel done
  | request _ ih => exact .request ih
  | bind _ _ first later => exact .bind first later
  | hit found => exact .hit found
  | miss absent _ ih => exact .miss absent (by simpa only [erase_body] using ih)

/-- Every allocated completed call has the same old completed call. -/
theorem Call.graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {input output : Value Symbol Guard} {before after : State} {memo saved : Memo}
    (actual : Call clear input before memo output after saved) :
    SourceCurrentMemoMergeGraph.Call clear top input before.heap memo output after.heap saved := by
  exact SourceCurrentMemoMergeGraph.Run.request_iff.mp (Run.graph (.request actual))

private def Selected [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (code : SourceCurrentMemoMergeGraph.Code Symbol Guard Output)
    (before : InternedConstructorTemplates.State Symbol Guard) (memo : Memo) (output : Output)
    (after : InternedConstructorTemplates.State Symbol Guard) (saved : Memo) : Prop :=
  match code with
  | .select inputs => ∃ fuel, SourceMergedSelection.select clear fuel inputs before = .done output after ∧ saved = memo
  | _ => False

private theorem lift_select [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} (code : Code Output)
    {before after : InternedConstructorTemplates.State Symbol Guard} {memo saved : Memo} {output : Output}
    (selected : Selected clear (erase code) before memo output after saved)
    (operations : SourceEqualityConstraintMemoAllocation.State) :
    ∃ final, Run clear code ⟨before, operations⟩ memo output ⟨after, final⟩ saved := by
  cases code <;> simp only [erase, Selected] at selected
  obtain ⟨fuel, done, rfl⟩ := selected
  exact ⟨operations, .select fuel done⟩

private def Requested [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (code : SourceCurrentMemoMergeGraph.Code Symbol Guard Output)
    (before : InternedConstructorTemplates.State Symbol Guard) (memo : Memo) (output : Output)
    (after : InternedConstructorTemplates.State Symbol Guard) (saved : Memo) : Prop :=
  match code with
  | .request input => ∀ operations, ∃ final,
      Call clear input ⟨before, operations⟩ memo output ⟨after, final⟩ saved
  | _ => False

private theorem lift_request [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} (code : Code Output)
    {before after : InternedConstructorTemplates.State Symbol Guard} {memo saved : Memo} {output : Output}
    (requested : Requested clear (erase code) before memo output after saved)
    (operations : SourceEqualityConstraintMemoAllocation.State) :
    ∃ final, Run clear code ⟨before, operations⟩ memo output ⟨after, final⟩ saved := by
  cases code <;> simp only [erase, Requested] at requested
  obtain ⟨final, actual⟩ := requested operations
  exact ⟨final, .request actual⟩

private def RequestProjection [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool)
    (code : Code Output) (before : State) (memo : Memo) (output : Output) (after : State) (saved : Memo) : Prop :=
  match code with
  | .request input => Call clear input before memo output after saved
  | _ => True

private theorem request_projection [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {code : Code Output} {before after : State} {memo saved : Memo} {output : Output}
    (actual : Run clear code before memo output after saved) : RequestProjection clear code before memo output after saved := by
  cases actual <;> trivial

private theorem lift_run [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {original : SourceCurrentMemoMergeGraph.Code Symbol Guard Output}
    {before after : InternedConstructorTemplates.State Symbol Guard} {memo saved : Memo} {output : Output}
    (actual : SourceCurrentMemoMergeGraph.Run clear top original before memo output after saved) :
    ∀ code : Code Output, erase code = original → ∀ operations,
      ∃ final, Run clear code ⟨before, operations⟩ memo output ⟨after, final⟩ saved := by
  induction actual using SourceCurrentMemoMergeGraph.Run.rec
      (motive_2 := fun input before memo output after saved _ => ∀ operations,
        ∃ final, Call clear input ⟨before, operations⟩ memo output ⟨after, final⟩ saved) with
  | pure value heap memo =>
      intro code same operations
      cases code <;> cases same
      exact ⟨operations, .pure _ _ _⟩
  | work job heap memo =>
      intro code same operations
      cases code with
      | pure value => cases same
      | work current => cases same; exact ⟨operations, .work _ _ _⟩
      | topRow symbol children => cases same; exact ⟨_, .topRow _ _ _ _⟩
      | select inputs => cases same
      | request input => cases same
      | bind first next => cases same
  | select fuel done =>
      intro code same operations
      apply lift_select code (operations := operations)
      rw [same]
      exact ⟨fuel, done, rfl⟩
  | request actual ih =>
      intro code same operations
      apply lift_request code (operations := operations)
      rw [same]
      exact ih
  | bind first later ihFirst ihLater =>
      intro code same operations
      cases code <;> cases same
      obtain ⟨middle, first⟩ := ihFirst _ rfl operations
      obtain ⟨final, later⟩ := ihLater _ rfl middle
      exact ⟨final, .bind first later⟩
  | hit found => exact ⟨_, .hit found⟩
  | miss absent actual ih operations =>
      obtain ⟨final, completed⟩ := ih _ (erase_body _) operations
      exact ⟨final, .miss absent completed⟩

/-- Every actual old erased program has an allocated run from the supplied equality state. -/
theorem run_lift [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} (code : Code Output)
    {before after : InternedConstructorTemplates.State Symbol Guard} {memo saved : Memo} {output : Output}
    (actual : SourceCurrentMemoMergeGraph.Run clear top (erase code) before memo output after saved)
    (operations : SourceEqualityConstraintMemoAllocation.State) :
    ∃ final, Run clear code ⟨before, operations⟩ memo output ⟨after, final⟩ saved :=
  lift_run actual code rfl operations

/-- Completed old calls construct their allocated recursive calls without a future-state premise. -/
theorem call_lift [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {input output : Value Symbol Guard}
    {before after : InternedConstructorTemplates.State Symbol Guard} {memo saved : Memo}
    (actual : SourceCurrentMemoMergeGraph.Call clear top input before memo output after saved)
    (operations : SourceEqualityConstraintMemoAllocation.State) :
    ∃ final, Call clear input ⟨before, operations⟩ memo output ⟨after, final⟩ saved := by
  have request := lift_run (SourceCurrentMemoMergeGraph.Run.request actual)
    (.request input) rfl operations
  obtain ⟨final, completed⟩ := request
  exact ⟨final, request_projection completed⟩

end MicroCFTA.SourceCurrentAllocatedMergeGraph
