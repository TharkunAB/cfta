import MicroCFTA.SourceEqualityPartialMemoWorker
import MicroCFTA.SourceEqualityPartialKeyTransport
import MicroCFTA.FlatMemoThunkReturned

/-!
# Table invariants of actual recursive result-memo execution

The invariant links each published request to its physical constraint key.
Every source continuation retains earlier running and returned cells.
These laws concern all observations, including source errors and exhausted
bounds. Native heap and result-language preservation are separate laws.
-/
namespace MicroCFTA.SourceEqualityPartialMemoFrame
open Cache InternedConstructorTemplates SourceEqualityPartialMemoWorker
open SourceEqualityPartialKeyTransport
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- The table projection omits native effects without discarding either memo table. -/
structure Tables where
  constraints : Cache.State SourceEqualityPartialConstraintKey.Key
  memo : Memo

/-- A key records the original inherited payload and exact node reference. -/
def KeyOf (cache : Cache.State SourceEqualityPartialConstraintKey.Key) (request : Request) (key : SourceEqualityPartialMemoWorker.Key) : Prop :=
  Recorded cache request.inherited key.1 ∧ request.value.referenceOf = key.2

/-- The physical interner is valid and every allocated result handle retains its original key. -/
def Valid (tables : Tables) : Prop := Cache.Valid tables.constraints ∧
  FlatMemoThunk.Valid (KeyOf tables.constraints) (fun _ => True) tables.memo

/-- Read both tables at a complete source continuation. -/
def stateTables (state : SourceEqualityPartialMemoWorker.State width) : Tables := ⟨state.constraints, state.memo⟩

/-- Every unfinished source branch retains the same two table components. -/
def observationTables : Observation width → Tables
  | .exhausted _ _ state | .busy _ _ state | .absent _ _ state | .pending _ state => stateTables state
  | .guarded _ constraints memo => ⟨constraints, memo⟩

/-- Read tables from success, source error, or the exact unfinished observation. -/
def resultTables : Result width Output → Tables
  | .done _ state => stateTables state
  | .incomplete observation => observationTables observation

/-- Source work grows keys and preserves every earlier running or completed cell. -/
structure Frame (before after : Tables) : Prop where
  valid : Valid after
  constraints : Cache.Extends before.constraints.table after.constraints.table
  published : Cache.Extends before.memo.table after.memo.table
  running : FlatMemoThunk.Running before.memo after.memo
  returned : FlatMemoThunk.Returned before.memo after.memo

/-- No table effects preserve the full invariant. -/
theorem Frame.refl (tables : Tables) (valid : Valid tables) : Frame tables tables :=
  ⟨valid, Cache.extends_refl _, Cache.extends_refl _, .refl _, .refl _⟩

/-- Table effects compose through the actual returned intermediate tables. -/
theorem Frame.trans (first : Frame before middle) (second : Frame middle after) : Frame before after :=
  ⟨second.valid, Cache.extends_trans first.constraints second.constraints,
    Cache.extends_trans first.published second.published, first.running.trans second.running,
    first.returned.trans second.returned⟩

/-- Physical key links remain valid after constraint table growth. -/
theorem key_grows {before after : Cache.State SourceEqualityPartialConstraintKey.Key}
    (growth : Cache.Extends before.table after.table) (request : Request) (key : SourceEqualityPartialMemoWorker.Key)
    (recorded : KeyOf before request key) : KeyOf after request key :=
  ⟨recorded.1.grows growth, recorded.2⟩

private theorem intern_growth (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (key : SourceEqualityPartialConstraintKey.Key) : Cache.Extends cache.table (Cache.intern cache key).2.table := by
  cases found : cache.table key with
  | some entry => simpa only [Cache.intern, found] using Cache.extends_refl cache.table
  | none =>
      simpa only [Cache.intern, found, Cache.install, Cache.reserve] using
        Cache.keepFirst_extends cache.table key (Cache.reserve cache key).1

/-- Actual physical payload identification preserves every previous constraint entry. -/
theorem identify_growth (payload : SourceEqualityPrecheck.Constraint) (cache : Cache.State SourceEqualityPartialConstraintKey.Key) :
    Cache.Extends cache.table (SourceEqualityPartialConstraintKey.identify payload cache).2.table := by
  cases payload with
  | none => exact Cache.extends_refl _
  | some records => exact intern_growth cache (SourceEqualityPartialConstraintKey.key records)

/-- Preparing a request retains all earlier cells and transports their physical key witnesses. -/
theorem prepare_frame (candidate : Request) (before : SourceEqualityPartialMemoWorker.State width)
    (valid : Valid (stateTables before)) : Frame (stateTables before) (stateTables (prepare candidate before).2) := by
  have growth := identify_growth candidate.inherited before.constraints
  have constraintValid : Cache.Valid (SourceEqualityPartialConstraintKey.identify candidate.inherited before.constraints).2 := by
    cases candidate.inherited with
    | none => exact valid.1
    | some records => exact (SourceEqualityPartialConstraintKey.identify_live records before.constraints valid.1).1
  exact ⟨⟨constraintValid, valid.2.keyMap _ _ _ _ (key_grows growth)⟩,
    growth, Cache.extends_refl _, .refl _, .refl _⟩

/-- Preparing the actual candidate supplies its own key link before publication. -/
theorem prepare_key (candidate : Request) (before : SourceEqualityPartialMemoWorker.State width)
    (valid : Valid (stateTables before)) : KeyOf (prepare candidate before).2.constraints candidate (prepare candidate before).1 :=
  ⟨recorded_identify before.constraints valid.1 candidate.inherited, rfl⟩

/-- Publishing an actual linked candidate preserves every earlier cell. -/
theorem lookup_frame (key : SourceEqualityPartialMemoWorker.Key) (candidate : Request) (before : Tables)
    (valid : Valid before) (recorded : KeyOf before.constraints candidate key) :
    Frame before ⟨before.constraints, (FlatMemoThunk.lookupOrInsert key candidate before.memo).2⟩ :=
  ⟨⟨valid.1, FlatMemoThunk.lookup_valid key candidate before.memo _ _ valid.2 recorded trivial⟩,
    Cache.extends_refl _, FlatMemoThunk.lookup_extends key candidate before.memo,
    FlatMemoThunk.lookup_running key candidate before.memo _ valid.2,
    FlatMemoThunk.lookup_returned key candidate before.memo _ valid.2⟩

private theorem demand_table (handle : Nat) (memo : Memo) : (FlatMemoThunk.demand handle memo).2.table = memo.table := by
  cases found : memo.cells handle with
  | none => simp only [FlatMemoThunk.demand, found]
  | some cell => cases cell with
    | mk request status => cases status <;> simp only [FlatMemoThunk.demand, found, FlatMemoThunk.setStatus]

/-- Demand retains the table and all earlier running or returned cells. -/
theorem demand_frame (handle : Nat) (before : Tables) (valid : Valid before) :
    Frame before ⟨before.constraints, (FlatMemoThunk.demand handle before.memo).2⟩ := by
  refine ⟨⟨valid.1, FlatMemoThunk.demand_valid handle before.memo _ valid.2⟩, Cache.extends_refl _, ?_,
    FlatMemoThunk.demand_running handle before.memo, FlatMemoThunk.demand_returned handle before.memo⟩
  rw [demand_table]
  exact Cache.extends_refl _

/-- Every returned observation is compared with the tables at its actual input. -/
def Framed (before : SourceEqualityPartialMemoWorker.State width) (result : Result width Output) : Prop :=
  Frame (stateTables before) (resultTables result)

/-- A recursive callback preserves both tables for every input and every result channel. -/
def Preserves (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → SourceEqualityPartialMemoWorker.State width →
      Result width (Value Symbol Guard)) : Prop :=
  ∀ inherited value before, Valid (stateTables before) → Framed before (call inherited value before)

/-- Source sequencing composes table effects only after an actual successful first result. -/
theorem bind_frame (before : SourceEqualityPartialMemoWorker.State width) (first : Result width First)
    (next : First → SourceEqualityPartialMemoWorker.State width → Result width Output)
    (framed : Framed before first)
    (continued : ∀ value middle, first = .done (.ok value) middle → Framed middle (next value middle)) :
    Framed before (first.bind next) := by
  cases first with
  | incomplete observation => exact framed
  | done answer middle =>
      cases answer with
      | error message => exact framed
      | ok value => exact framed.trans (continued value middle rfl)

/-- Actual indexed traversal retains ancestors and earlier completed siblings. -/
theorem childrenWalk_frame (call) (preserves : Preserves call) (payload index values)
    (before : SourceEqualityPartialMemoWorker.State width) (valid : Valid (stateTables before)) :
    Framed before (childrenWalk call payload index values before) := by
  induction values generalizing index before with
  | nil => exact .refl _ valid
  | cons value values ih =>
      apply bind_frame before _ _ (preserves _ _ _ valid)
      intro result middle first
      have head := preserves (SourceEqualityDescend.descend payload index) value before valid
      rw [first] at head
      apply bind_frame middle _ _ (ih (index + 1) middle head.valid)
      intro results after rest
      have tail := ih (index + 1) middle head.valid
      rw [rest] at tail
      exact .refl _ tail.valid

/-- Contradiction and live traversal both preserve every table invariant. -/
theorem children_frame (call) (preserves : Preserves call) (payload values)
    (before : SourceEqualityPartialMemoWorker.State width) (valid : Valid (stateTables before)) :
    Framed before (children call payload values before) := by
  cases payload with
  | none => exact .refl _ valid
  | some records => exact childrenWalk_frame call preserves (some records) 0 values before valid

/-- Own readback, combination, recursive descendants, and edge reconstruction retain both tables. -/
theorem descendants_frame [DecidableEq (EdgeKey Symbol Guard)]
    (call) (preserves : Preserves call) (edge inherited)
    (before : SourceEqualityPartialMemoWorker.State width) (valid : Valid (stateTables before)) :
    Framed before (descendants call edge inherited before) := by
  unfold descendants
  split
  · exact .refl _ valid
  · split
    · exact .refl _ valid
    · rename_i payload combined
      apply bind_frame before _ _ (children_frame call preserves payload edge.children before valid)
      intro values middle actual
      have child := children_frame call preserves payload edge.children before valid
      rw [actual] at child
      exact .refl _ child.valid

/-- All native edge outcomes retain the two memo tables before the descendant continuation. -/
theorem edge_frame [DecidableEq Symbol]
    [DecidableEq (EdgeKey Symbol Guard)]
    (call) (preserves : Preserves call) (g e p h c n edge inherited)
    (before : SourceEqualityPartialMemoWorker.State width) (valid : Valid (stateTables before)) :
    Framed before (SourceEqualityPartialMemoWorker.edge call g e p h c n edge inherited before) := by
  unfold SourceEqualityPartialMemoWorker.edge
  split
  · rename_i narrowed middle actual
    exact descendants_frame call preserves narrowed inherited { before with native := middle } valid
  · exact .refl _ valid
  · exact .refl _ valid

/-- Ordered rows preserve all cells from earlier rows and ancestor requests. -/
theorem rows_frame [DecidableEq Symbol]
    [DecidableEq (EdgeKey Symbol Guard)]
    (call) (preserves : Preserves call) (g e p h c n inherited edges)
    (before : SourceEqualityPartialMemoWorker.State width) (valid : Valid (stateTables before)) :
    Framed before (rows call g e p h c n inherited edges before) := by
  induction edges generalizing before with
  | nil => exact .refl _ valid
  | cons edge edges ih =>
      apply bind_frame before _ _ (edge_frame call preserves g e p h c n edge inherited before valid)
      intro result middle first
      have head := edge_frame call preserves g e p h c n edge inherited before valid
      rw [first] at head
      apply bind_frame middle _ _ (ih middle head.valid)
      intro results after rest
      have tail := ih middle head.valid
      rw [rest] at tail
      exact .refl _ tail.valid

/-- Every actual source body branch preserves original memo request links. -/
theorem step_frame [DecidableEq Symbol]
    [DecidableEq (EdgeKey Symbol Guard)]
    (call) (preserves : Preserves call) (g e p h c n) (candidate : Request)
    (before : SourceEqualityPartialMemoWorker.State width) (valid : Valid (stateTables before)) :
    Framed before (step call g e p h c n candidate before) := by
  unfold step
  split
  · exact .refl _ valid
  · exact .refl _ valid
  · exact .refl _ valid
  · split <;> exact .refl _ valid
  · rename_i entry edges depth free actualValue
    apply bind_frame before _ _ (rows_frame call preserves g e p h c n candidate.inherited edges before valid)
    intro results middle actual
    have checked := rows_frame call preserves g e p h c n candidate.inherited edges before valid
    rw [actual] at checked
    exact .refl _ checked.valid

private theorem finish_table (handle : Nat) (value) (memo : Memo) :
    (FlatMemoThunk.finish handle value memo).table = memo.table := by
  cases found : memo.cells handle with
  | none => simp only [FlatMemoThunk.finish, found]
  | some cell => cases cell with
    | mk request status => cases status <;> simp only [FlatMemoThunk.finish, found, FlatMemoThunk.setStatus]

/-- Completion retains all input running cells when its own handle was not running at that input. -/
theorem finish_frame (before : SourceEqualityPartialMemoWorker.State width) (handle : Nat)
    (result : Result width (Value Symbol Guard))
    (framed : Framed before result)
    (different : ∀ original, before.memo.cells handle ≠ some ⟨original, .evaluating⟩) :
    Framed before (finish handle result) := by
  cases result with
  | incomplete observation => exact framed
  | done answer after =>
      cases answer with
      | error message => exact framed
      | ok value =>
          refine ⟨⟨framed.valid.1, FlatMemoThunk.finish_valid handle value after.memo _ framed.valid.2⟩,
            framed.constraints, ?_, ?_, framed.returned.trans (FlatMemoThunk.finish_returned handle value after.memo)⟩
          · simpa only [SourceEqualityPartialMemoWorker.finish, resultTables, stateTables, finish_table] using framed.published
          · intro other original stored
            have separate : other ≠ handle := by intro same; subst other; exact different original stored
            exact FlatMemoThunk.finish_running_other handle other value after.memo original separate (framed.running other original stored)

/-- Publication and demand ensure a body cannot complete an ancestor's running handle. -/
theorem request_frame (body : Nat → Request → SourceEqualityPartialMemoWorker.State width →
      Result width (Value Symbol Guard))
    (bodies : ∀ handle original before, Valid (stateTables before) → Framed before (body handle original before))
    (candidate : Request) (before : SourceEqualityPartialMemoWorker.State width) (valid : Valid (stateTables before)) :
    Framed before (request body candidate before) := by
  let prepared := prepare candidate before
  let published := FlatMemoThunk.lookupOrInsert prepared.1 candidate prepared.2.memo
  let demanded := FlatMemoThunk.demand published.1 published.2
  let running : SourceEqualityPartialMemoWorker.State width := { prepared.2 with memo := demanded.2 }
  have preparation := prepare_frame candidate before valid
  have publication := preparation.trans (lookup_frame prepared.1 candidate (stateTables prepared.2) preparation.valid
    (prepare_key candidate before valid))
  have demand := publication.trans (demand_frame published.1 ⟨prepared.2.constraints, published.2⟩ publication.valid)
  change Framed before (match demanded.1 with
    | .absent => .incomplete (.absent prepared.1 published.1 running)
    | .busy => .incomplete (.busy prepared.1 published.1 running)
    | .ready value => .done (.ok value) running
    | .evaluate original => finish published.1 (body published.1 original running))
  cases outcome : demanded.1 with
  | absent | busy | ready value => exact demand
  | evaluate original =>
      apply finish_frame before published.1 _ (demand.trans (bodies published.1 original running demand.valid))
      intro earlier stored
      have started : FlatMemoThunk.demand published.1 published.2 = (.evaluate original, demanded.2) := Prod.ext outcome rfl
      have suspended := (FlatMemoThunk.demand_evaluate published.1 published.2 demanded.2 original started).1
      have retained := publication.running published.1 earlier stored
      have impossible := Option.some.inj (retained.symm.trans suspended)
      cases impossible

/-- Every bounded recursive execution preserves actual physical request links and earlier cell phases. -/
theorem run_frame [DecidableEq Symbol]
    [DecidableEq (EdgeKey Symbol Guard)]
    (g e p h c n fuel : Nat) : Preserves (SourceEqualityPartialMemoWorker.run (width := width) g e p h c n fuel) := by
  induction fuel with
  | zero =>
      intro inherited value before valid
      exact request_frame (fun handle original state => .incomplete (.exhausted original handle state))
        (fun _ _ _ bodyValid => .refl _ bodyValid) ⟨inherited, value⟩ before valid
  | succ fuel ih =>
      intro inherited value before valid
      exact request_frame _ (fun _ original state bodyValid => step_frame _ ih g e p h c n original state bodyValid)
        ⟨inherited, value⟩ before valid

/-- Cold native input starts with both actual table invariants and no supplied memo answers. -/
theorem initial_valid (native : SourceEqualityClassFoldGraph.NativeState width
    Symbol Guard) :
    Valid (stateTables (initial native)) :=
  ⟨Cache.empty_valid, FlatMemoThunk.empty_valid _ _⟩

end MicroCFTA.SourceEqualityPartialMemoFrame
