import MicroCFTA.SourceMergedWorker

/-!
# Completed recursive merge requests

The body keeps the source row groups and child order. Each recursive child
uses the result memo. A selection carries its actual completed comparison
receipt and its own finite comparison bound.

This graph is a completed sequential projection. A miss runs its recursive
body before it records completion. It then retains the first stored entry
and rereads the winner. The graph does not model the source's earlier lazy
publication, pending ancestors, concurrent forcing, or the GHC runtime.
-/
namespace MicroCFTA.SourceCurrentMemoMergeGraph
open Cache InternedBinderProtocol InternedConstructorTemplates
open MergedOrdinaryHeight (recursiveBoundary ordinaryUnion)

/-- A completed entry retains its original argument and complete returned record. -/
structure Entry (Symbol Guard : Type) where
  original : Value Symbol Guard
  result : Value Symbol Guard

/-- A fixed symbol type has one merge table keyed by the literal tagged node reference. -/
abbrev Memo (Symbol Guard : Type) := NodeRef → Option (Entry Symbol Guard)

/-- The initial completed result table contains no entries. -/
def empty : Memo Symbol Guard := fun _ => none

/-- Completion preserves an earlier winner at the requested physical key. -/
def remember (memo : Memo Symbol Guard) (input output : Value Symbol Guard) : Memo Symbol Guard :=
  keepFirst memo input.referenceOf ⟨input, output⟩

/-- The returned result comes from the actual winner reread after completion. -/
def winner (memo : Memo Symbol Guard) (input output : Value Symbol Guard) : Entry Symbol Guard :=
  ((remember memo input output) input.referenceOf).getD ⟨input, output⟩

/-- Merge instructions retain real constructor work, selection, and recursive requests. -/
inductive Code (Symbol Guard : Type) : Type → Type 1 where
  | pure (value : Result) : Code Symbol Guard Result
  | work (job : Work Symbol Guard Result) : Code Symbol Guard Result
  | select (inputs : List (Value Symbol Guard)) : Code Symbol Guard (List (Value Symbol Guard))
  | request (input : Value Symbol Guard) : Code Symbol Guard (Value Symbol Guard)
  | bind (first : Code Symbol Guard First) (next : First → Code Symbol Guard Result) : Code Symbol Guard Result

/-- Ordered traversal threads both the physical heap and the result table between children. -/
def map (call : Input → Code Symbol Guard Output) : List Input → Code Symbol Guard (List Output)
  | [] => .pure []
  | first :: rest => .bind (call first) fun value => .bind (map call rest) fun values => .pure (value :: values)

/-- A retained singleton returns directly; other columns keep the actual boundary and union branches. -/
def retainedColumn (retained : List (Value Symbol Guard)) : Code Symbol Guard (Value Symbol Guard) :=
  match retained with
  | [single] => .pure single
  | others => if others.any recursiveBoundary then .work (makeUnion others)
    else .bind (.work (ordinaryUnion others)) Code.request

/-- A small row requests its children in source order and retains its original guard. -/
def small (edge : EdgeValue Symbol Guard) : Code Symbol Guard (EdgeValue Symbol Guard) :=
  .bind (map Code.request edge.children) fun children =>
    .work (makeEdge edge.entry.key.symbol edge.entry.key.constraint children)

/-- Actual completed filtering precedes retained-column normalization. -/
def column (inputs : List (Value Symbol Guard)) : Code Symbol Guard (Value Symbol Guard) :=
  .bind (.select inputs) retainedColumn

/-- A large group processes each column before it constructs the source Top row. -/
def large (top : Guard) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) :
    Code Symbol Guard (EdgeValue Symbol Guard) :=
  .bind (map column
    (MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length))
    fun children => .work (makeEdge first.entry.key.symbol top children)

/-- The source keeps up to four rows and uses the column branch above that threshold. -/
def group (top : Guard) (edges : List (EdgeValue Symbol Guard)) : Code Symbol Guard (List (EdgeValue Symbol Guard)) :=
  if edges.length ≤ 4 then map small edges
  else match edges with
  | [] => .pure []
  | first :: rest => .bind (large top first rest) fun edge => .pure [edge]

/-- Every group finishes before the final ordinary node constructor runs. -/
def root (top : Guard) (groups : List (List (EdgeValue Symbol Guard))) : Code Symbol Guard (Value Symbol Guard) :=
  .bind (map (group top) groups) fun rows => .work (makeNode rows.flatten)

/-- Only closed ordinary roots enter the source grouping traversal. -/
def body [DecidableEq Symbol] (top : Guard) (input : Value Symbol Guard) : Code Symbol Guard (Value Symbol Guard) :=
  match input with
  | .node _ edges _ free => if free = [] then root top (MergedSourceGrouping.groups edges) else .pure input
  | _ => .pure input

mutual
  /-- Actual completed instructions retain exact intermediate heaps and result tables. -/
  inductive Run [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard) :
      {Output : Type} → Code Symbol Guard Output → State Symbol Guard → Memo Symbol Guard →
        Output → State Symbol Guard → Memo Symbol Guard → Prop where
    | pure (value : Output) (state : State Symbol Guard) (memo : Memo Symbol Guard) :
        Run clear top (.pure value) state memo value state memo
    | work (job : Work Symbol Guard Output) (state : State Symbol Guard) (memo : Memo Symbol Guard) :
        Run clear top (.work job) state memo (run job state).1 (run job state).2 memo
    | select (fuel : Nat)
        (done : SourceMergedSelection.select clear fuel inputs before = .done values after) :
        Run clear top (.select inputs) before memo values after memo
    | request (actual : Call clear top input before memo output after saved) :
        Run clear top (.request input) before memo output after saved
    | bind (first : Run clear top code before memo value middle current)
        (later : Run clear top (next value) middle current output after saved) :
        Run clear top (.bind code next) before memo output after saved

  /-- A completed hit skips the body; a miss executes the actual recursive memo-aware body. -/
  inductive Call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard) :
      Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Value Symbol Guard →
        State Symbol Guard → Memo Symbol Guard → Prop where
    | hit (found : memo input.referenceOf = some entry) :
        Call clear top input before memo entry.result before memo
    | miss (absent : memo input.referenceOf = none)
        (actual : Run clear top (body top input) before memo candidate after current) :
        Call clear top input before memo (winner current input candidate).result after (remember current input candidate)
end

/-- Completion retains every previously stored original and result. -/
theorem remember_extends (memo : Memo Symbol Guard) (input output : Value Symbol Guard) :
    Extends memo (remember memo input output) := keepFirst_extends _ _ _

/-- A completion always leaves its requested physical key present with the returned winner. -/
theorem winner_found (memo : Memo Symbol Guard) (input output : Value Symbol Guard) :
    remember memo input output input.referenceOf = some (winner memo input output) := by
  obtain ⟨entry, found⟩ := keepFirst_present memo input.referenceOf (Entry.mk input output)
  simp only [winner, remember, found, Option.getD_some]

/-- An existing winner supplies the returned record and prevents a completion replacement. -/
theorem winner_existing (memo : Memo Symbol Guard) (input output : Value Symbol Guard) (entry : Entry Symbol Guard)
    (found : memo input.referenceOf = some entry) :
    remember memo input output = memo ∧ winner memo input output = entry := by
  constructor
  · simp only [remember, keepFirst, found]
  · simp only [winner, remember, keepFirst, found, Option.getD_some]

/-- Every actual completed instruction retains all earlier result-table entries. -/
theorem Run.extends [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) : Extends memo saved := by
  induction actual using Run.rec
      (motive_2 := fun _ _ memo _ _ saved _ => Extends memo saved) with
  | pure => exact extends_refl _
  | work => exact extends_refl _
  | select => exact extends_refl _
  | request _ ih => exact ih
  | bind _ _ first later => exact extends_trans first later
  | hit => exact extends_refl _
  | miss _ _ ih => exact extends_trans ih (remember_extends _ _ _)

/-- Completed hit and miss requests retain all earlier result-table entries. -/
theorem Call.extends [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) : Extends memo saved := by
  induction actual using Call.rec
      (motive_1 := fun {_} _ _ memo _ _ saved _ => Extends memo saved) with
  | pure => exact extends_refl _
  | work => exact extends_refl _
  | select => exact extends_refl _
  | request _ ih => exact ih
  | bind _ _ first later => exact extends_trans first later
  | hit => exact extends_refl _
  | miss _ _ ih => exact extends_trans ih (remember_extends _ _ _)

/-- A completion at an absent key stores exactly its original argument and returned candidate. -/
theorem remember_absent (memo : Memo Symbol Guard) (input output : Value Symbol Guard)
    (absent : memo input.referenceOf = none) :
    remember memo input output input.referenceOf = some ⟨input, output⟩ ∧
      winner memo input output = ⟨input, output⟩ := by
  simp [remember, keepFirst, absent, put, winner]

/-- Every stored completion is an old entry or the literal new candidate. -/
theorem remember_cases (memo : Memo Symbol Guard) (input output : Value Symbol Guard)
    (key : NodeRef) (entry : Entry Symbol Guard) (found : remember memo input output key = some entry) :
    memo key = some entry ∨ key = input.referenceOf ∧ entry = ⟨input, output⟩ :=
  InternedRecordCoherence.record_cases _ _ _ _ _ found

/-- A completed request with an initially present key changes neither heap nor result table. -/
theorem Call.hit_unchanged [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (entry : Entry Symbol Guard)
    (found : memo input.referenceOf = some entry) :
    after = before ∧ saved = memo ∧ output = entry.result := by
  cases actual with
  | hit present => cases Option.some.inj (present.symm.trans found); exact ⟨rfl, rfl, rfl⟩
  | miss absent _ => rw [absent] at found; cases found

/-- An initially absent completed call exposes its actual recursive body and winner reread. -/
theorem Call.miss_cases [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (absent : memo input.referenceOf = none) :
    ∃ candidate current, Run clear top (body top input) before memo candidate after current ∧
      saved = remember current input candidate ∧ output = (winner current input candidate).result := by
  cases actual with
  | hit present => rw [absent] at present; cases present
  | miss _ actual => exact ⟨_, _, actual, rfl, rfl⟩

/-- Every completed call returns the result of an entry present in its actual returned table. -/
theorem Call.present [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) :
    ∃ entry, saved input.referenceOf = some entry ∧ output = entry.result := by
  cases actual with
  | hit found => exact ⟨_, found, rfl⟩
  | miss _ _ => exact ⟨_, winner_found _ _ _, rfl⟩

/-- A pure instruction retains exactly its value, heap, and completed table. -/
theorem Run.pure_iff [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {value output : Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} :
    Run clear top (.pure value) before memo output after saved ↔ output = value ∧ after = before ∧ saved = memo := by
  constructor
  · intro actual; cases actual; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; exact .pure _ _ _

/-- A work instruction executes the literal physical constructor program and retains the result table. -/
theorem Run.work_iff [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {job : Work Symbol Guard Output} {output : Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} :
    Run clear top (.work job) before memo output after saved ↔
      output = (run job before).1 ∧ after = (run job before).2 ∧ saved = memo := by
  constructor
  · intro actual; cases actual; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; exact .work _ _ _

private def project [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (code : Code Symbol Guard Output)
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (output : Output)
    (after : State Symbol Guard) (saved : Memo Symbol Guard) : Prop :=
  match code with
  | .select inputs => (∃ fuel, SourceMergedSelection.select clear fuel inputs before = .done output after) ∧ saved = memo
  | .request input => Call clear top input before memo output after saved
  | _ => True

private theorem Run.project [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) : project clear top code before memo output after saved := by
  induction actual using Run.rec (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | pure | work | bind => trivial
  | select fuel done => exact ⟨⟨fuel, done⟩, rfl⟩
  | request call _ => exact call
  | hit | miss => trivial

/-- Every selected column has its own actual completed comparison bound and unchanged result table. -/
theorem Run.select_iff [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {inputs values : List (Value Symbol Guard)}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} :
    Run clear top (.select inputs) before memo values after saved ↔
      (∃ fuel, SourceMergedSelection.select clear fuel inputs before = .done values after) ∧ saved = memo := by
  constructor
  · intro actual; exact actual.project
  · rintro ⟨⟨fuel, done⟩, rfl⟩; exact .select fuel done

/-- A recursive instruction is exactly the reached completed result-memo request. -/
theorem Run.request_iff [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} :
    Run clear top (.request input) before memo output after saved ↔ Call clear top input before memo output after saved := by
  constructor
  · intro actual; exact actual.project
  · exact Run.request

/-- Sequencing exposes the exact first result, heap, and table used by the continuation. -/
theorem Run.bind_iff [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {first : Code Symbol Guard First} {next : First → Code Symbol Guard Output}
    {output : Output} {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} :
    Run clear top (.bind first next) before memo output after saved ↔
      ∃ value middle current, Run clear top first before memo value middle current ∧
        Run clear top (next value) middle current output after saved := by
  constructor
  · intro actual; cases actual with | bind first later => exact ⟨_, _, _, first, later⟩
  · rintro ⟨_, _, _, first, later⟩; exact .bind first later

/-- Ordered list traversal uses the exact first child's returned heap and table for the rest. -/
theorem Run.map_cons_iff [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {call : Input → Code Symbol Guard Output}
    {input : Input} {inputs : List Input} {outputs : List Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} :
    Run clear top (map call (input :: inputs)) before memo outputs after saved ↔
      ∃ value values middle current, Run clear top (call input) before memo value middle current ∧
        Run clear top (map call inputs) middle current values after saved ∧ outputs = value :: values := by
  constructor
  · intro actual
    obtain ⟨value, middle, current, first, later⟩ := Run.bind_iff.mp actual
    obtain ⟨values, final, last, rest, returned⟩ := Run.bind_iff.mp later
    obtain ⟨same, rfl, rfl⟩ := Run.pure_iff.mp returned
    exact ⟨_, _, _, _, first, rest, same⟩
  · rintro ⟨value, values, middle, current, first, rest, rfl⟩
    exact .bind first (.bind rest (.pure _ _ _))

/-- The small-group branch retains all original rows in their original order. -/
theorem group_small (top : Guard) (edges : List (EdgeValue Symbol Guard)) (smallGroup : edges.length ≤ 4) :
    group top edges = map small edges := by simp [group, smallGroup]

/-- The large-group branch runs columns before it returns its one merged row. -/
theorem group_large (top : Guard) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (largeGroup : 4 < (first :: rest).length) :
    group top (first :: rest) = .bind (large top first rest) (fun edge => .pure [edge]) := by
  unfold group
  split
  · omega
  · rfl

/-- A closed ordinary body uses the source symbol/arity buckets before final construction. -/
theorem body_closed [DecidableEq Symbol] (top : Guard) (entry : Interned NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (depth : Nat) :
    body top (.node entry edges depth []) = root top (MergedSourceGrouping.groups edges) := by
  simp [body]

/-- Every open body input returns its original complete record without constructor or child work. -/
theorem body_open [DecidableEq Symbol] (top : Guard) (input : Value Symbol Guard) (openInput : input.free ≠ []) :
    body top input = .pure input := by
  cases input <;> simp_all [body, Value.free]

end MicroCFTA.SourceCurrentMemoMergeGraph
