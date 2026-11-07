import MicroCFTA.SourceSizedConjunctionRows
import MicroCFTA.SourceSizedFiniteKeys

/-!
# Capped conjunction-key exploration

The step follows `intersectionCountingRows.explore`. It checks visited keys
before the key cap. It reads at most cap plus one raw conjunction rows. It
then checks the row cap, inserts the new key, and prepends the rows' children.
Association-list entries represent the finite source map. Their keys remain
distinct. Their list order is insertion order, not `Map.toList` order.

The finite classified input supplies a maximum child arity. That maximum
gives a computed bound on recursive control steps. No caller supplies fuel,
an arity bound, a closure proof, or a completed exploration. This bound does
not bound tuple generation, native map operations, or total execution cost.
-/
namespace MicroCFTA.SourceSizedConjunctionWorklist
open SourceSizedDecided

variable {State Symbol : Type}

/-- The complete finite classified source input. -/
abbrev Classified (State Symbol : Type) := SourceSizedFiniteKeys.Table State Symbol (List (List Nat))

/-- Finite map entries for conjunction keys and their ordered row lists. -/
abbrev Stored (State Symbol : Type) :=
  List (List State × List (Row (List State) Symbol (List (List Nat))))

/-- Derive the maximum transition arity from every original classified row. -/
def maxArity (classified : Classified State Symbol) : Nat :=
  (classified.flatMap fun entry => entry.2.map fun row => row.children.length).foldr max 0

private theorem member_le_maximum (values : List Nat) (value : Nat) (member : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

/-- Merged original lookup cannot exceed the maximum arity of the explicit input. -/
theorem original_arity [DecidableEq State]
    (classified : Classified State Symbol) (state : State)
    (row : Row State Symbol (List (List Nat)))
    (member : row ∈ SourceSizedFiniteKeys.lookup classified state) :
    row.children.length ≤ maxArity classified := by
  unfold SourceSizedFiniteKeys.lookup at member
  obtain ⟨entry, present, selected⟩ := List.mem_flatMap.mp member
  have stored : row ∈ entry.2 := by
    split at selected
    · exact selected
    · cases selected
  exact member_le_maximum _ _ (List.mem_flatMap.mpr
    ⟨entry, present, List.mem_map.mpr ⟨row, stored, rfl⟩⟩)

/-- Intersection rows retain an original input row's arity. -/
theorem generated_arity [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol) (key : List State)
    (row : Row (List State) Symbol (List (List Nat)))
    (member : row ∈ SourceSizedConjunctionRows.rows (SourceSizedFiniteKeys.lookup classified) key) :
    row.children.length ≤ maxArity classified := by
  obtain ⟨owner, _, original, stored, arity⟩ :=
    SourceSizedConjunctionRows.rows_arity (SourceSizedFiniteKeys.lookup classified) key row member
  rw [arity]
  exact original_arity classified owner original stored

/-- Read the exact source prefix used to detect a per-key transition overflow. -/
def cappedRows [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (key : List State) :
    List (Row (List State) Symbol (List (List Nat))) :=
  (SourceSizedConjunctionRows.rows (SourceSizedFiniteKeys.lookup classified) key).take (limit + 1)

/-- The extra transition detects precisely the overflow of the full raw row list. -/
theorem cappedRows_over_iff [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (key : List State) :
    limit < (cappedRows limit classified key).length ↔
      limit < (SourceSizedConjunctionRows.rows (SourceSizedFiniteKeys.lookup classified) key).length := by
  simp only [cappedRows, List.length_take]
  omega

/-- A successful cap check retains the entire original conjunction row list. -/
theorem cappedRows_eq [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (key : List State)
    (within : (cappedRows limit classified key).length ≤ limit) :
    cappedRows limit classified key =
      SourceSizedConjunctionRows.rows (SourceSizedFiniteKeys.lookup classified) key := by
  have rawWithin : (SourceSizedConjunctionRows.rows (SourceSizedFiniteKeys.lookup classified) key).length ≤ limit := by
    apply Nat.le_of_not_gt
    intro over
    have tooLong := (cappedRows_over_iff limit classified key).mpr over
    omega
  exact List.take_of_length_le (Nat.le_trans rawWithin (by omega))

private theorem children_length_bound (rows : List (Row State Symbol Payload)) (arity : Nat)
    (bounded : ∀ row ∈ rows, row.children.length ≤ arity) :
    (rows.flatMap fun row => row.children).length ≤ rows.length * arity := by
  induction rows with
  | nil => simp
  | cons head tail ih =>
      have first := bounded head (by simp)
      have rest := ih (fun row present => bounded row (List.mem_cons_of_mem _ present))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- A retained key prepends at most limit times the input maximum arity children. -/
theorem children_bound [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (key : List State)
    (within : (cappedRows limit classified key).length ≤ limit) :
    ((cappedRows limit classified key).flatMap fun row => row.children).length ≤ limit * maxArity classified := by
  apply Nat.le_trans (children_length_bound _ _ ?_) (Nat.mul_le_mul_right _ within)
  intro row present
  exact generated_arity classified key row (List.mem_of_mem_take present)

/-- One source checking round either finishes, fails a cap, or recurses. -/
inductive Action (State Symbol : Type) where
  | ready (table : Stored State Symbol)
  | limitExceeded
  | next (table : Stored State Symbol) (pending : List (List State))

/-- Execute the source visited check, both cap checks, insertion, and pending order. -/
def step [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (table : Stored State Symbol) :
    List (List State) → Action State Symbol
  | [] => .ready table
  | key :: pending =>
      if key ∈ table.map Prod.fst then .next table pending
      else if limit ≤ table.length then .limitExceeded
      else
        let row := cappedRows limit classified key
        if limit < row.length then .limitExceeded
        else .next ((key, row) :: table) ((row.flatMap fun transition => transition.children) ++ pending)

/-- A visited key is skipped even when the map has reached its cap. -/
theorem step_visited [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (table : Stored State Symbol)
    (key : List State) (pending : List (List State)) (visited : key ∈ table.map Prod.fst) :
    step limit classified table (key :: pending) = .next table pending := by
  simp only [step, ite_eq_left visited]

/-- The map cap rejects an unseen key before it can be inserted. -/
theorem step_map_limit [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (table : Stored State Symbol)
    (key : List State) (pending : List (List State)) (fresh : key ∉ table.map Prod.fst)
    (over : limit ≤ table.length) :
    step limit classified table (key :: pending) = .limitExceeded := by
  simp only [step, ite_eq_right fresh, ite_eq_left over]

/-- The row cap rejects an unseen key whose raw conjunction tuples exceed the cap. -/
theorem step_row_limit [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (table : Stored State Symbol)
    (key : List State) (pending : List (List State)) (fresh : key ∉ table.map Prod.fst)
    (space : table.length < limit)
    (over : limit < (cappedRows limit classified key).length) :
    step limit classified table (key :: pending) = .limitExceeded := by
  have notFull : ¬limit ≤ table.length := by omega
  simp only [step, ite_eq_right fresh, ite_eq_right notFull, ite_eq_left over]

/-- Successful stored maps have distinct keys, bounded rows, and full source row readback. -/
structure Valid [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (table : Stored State Symbol) : Prop where
  distinct : (table.map Prod.fst).Nodup
  capacity : table.length ≤ limit
  rowBounds : ∀ entry ∈ table, entry.2.length ≤ limit
  rowReadback : ∀ entry ∈ table,
    entry.2 = SourceSizedConjunctionRows.rows (SourceSizedFiniteKeys.lookup classified) entry.1

/-- The empty source map satisfies all stored-map invariants. -/
theorem empty_valid [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) : Valid limit classified [] := by
  constructor
  · simp
  · simp
  · intro entry member; cases member
  · intro entry member; cases member

private theorem step_ready_eq [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (table returned : Stored State Symbol)
    (pending : List (List State)) (checked : step limit classified table pending = .ready returned) :
    returned = table := by
  cases pending with
  | nil => exact (Action.ready.inj checked).symm
  | cons key pending =>
      simp only [step] at checked
      split at checked
      · cases checked
      · split at checked
        · cases checked
        · split at checked <;> cases checked

/-- Each recursive source step preserves the stored-map invariants. -/
theorem step_valid [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol)
    (table nextTable : Stored State Symbol) (pending nextPending : List (List State))
    (valid : Valid limit classified table)
    (checked : step limit classified table pending = .next nextTable nextPending) :
    Valid limit classified nextTable := by
  cases pending with
  | nil => cases checked
  | cons key pending =>
      simp only [step] at checked
      split at checked
      · rcases Action.next.inj checked with ⟨rfl, rfl⟩
        exact valid
      · rename_i fresh
        split at checked
        · cases checked
        · rename_i space
          split at checked
          · cases checked
          · rename_i within
            rcases Action.next.inj checked with ⟨rfl, rfl⟩
            constructor
            · exact List.nodup_cons.mpr ⟨fresh, valid.distinct⟩
            · simp only [List.length_cons]
              omega
            · intro entry member
              rcases List.mem_cons.mp member with rfl | previous
              · exact Nat.le_of_not_gt within
              · exact valid.rowBounds entry previous
            · intro entry member
              rcases List.mem_cons.mp member with rfl | previous
              · exact cappedRows_eq limit classified key (Nat.le_of_not_gt within)
              · exact valid.rowReadback entry previous

/-- Account for all child keys that remaining successful insertions can schedule. -/
def potential (limit : Nat) (classified : Classified State Symbol)
    (table : Stored State Symbol) (pending : List (List State)) : Nat :=
  (limit - table.length) * (limit * maxArity classified) + pending.length

/-- Every recursive step strictly decreases the derived control potential. -/
theorem step_decreases [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol)
    (table nextTable : Stored State Symbol) (pending nextPending : List (List State))
    (checked : step limit classified table pending = .next nextTable nextPending) :
    potential limit classified nextTable nextPending < potential limit classified table pending := by
  cases pending with
  | nil => cases checked
  | cons key pending =>
      simp only [step] at checked
      split at checked
      · rcases Action.next.inj checked with ⟨rfl, rfl⟩
        simp only [potential, List.length_cons]
        omega
      · split at checked
        · cases checked
        · rename_i space
          split at checked
          · cases checked
          · rename_i within
            rcases Action.next.inj checked with ⟨rfl, rfl⟩
            have children := children_bound limit classified key (Nat.le_of_not_gt within)
            have remaining : limit - (table.length + 1) + 1 = limit - table.length := by omega
            have budget := congrArg (fun count => count * (limit * maxArity classified)) remaining
            simp only [Nat.add_mul, Nat.one_mul] at budget
            simp only [potential, List.length_cons, List.length_append]
            omega

/-- The bounded implementation retains the source cap failure and ready-map results. -/
inductive Outcome (State Symbol : Type) where
  | ready (table : Stored State Symbol)
  | limitExceeded
  | exhausted

/-- Iterate the concrete source step with an internal recursion bound. -/
def run [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) :
    Nat → Stored State Symbol → List (List State) → Outcome State Symbol
  | fuel, table, pending =>
      match step limit classified table pending with
      | .ready returned => .ready returned
      | .limitExceeded => .limitExceeded
      | .next nextTable nextPending =>
          match fuel with
          | 0 => .exhausted
          | fuel + 1 => run limit classified fuel nextTable nextPending

/-- Record source control rounds without a caller-supplied recursion bound. -/
inductive Evaluation [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) :
    Stored State Symbol → List (List State) → Nat → Outcome State Symbol → Prop where
  | ready (checked : step limit classified table pending = .ready returned) :
      Evaluation limit classified table pending 1 (.ready returned)
  | limitExceeded (checked : step limit classified table pending = .limitExceeded) :
      Evaluation limit classified table pending 1 .limitExceeded
  | next (checked : step limit classified table pending = .next nextTable nextPending)
      (following : Evaluation limit classified nextTable nextPending calls result) :
      Evaluation limit classified table pending (calls + 1) result

/-- Finite source evaluations cannot return the internal exhaustion marker. -/
theorem Evaluation.terminal [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (table : Stored State Symbol)
    (pending : List (List State)) (calls : Nat) (result : Outcome State Symbol)
    (execution : Evaluation limit classified table pending calls result) : result ≠ .exhausted := by
  induction execution with
  | ready _ => intro equal; cases equal
  | limitExceeded _ => intro equal; cases equal
  | next _ _ ih => exact ih

/-- Enough derived potential evaluates the literal source control and bounds its rounds. -/
theorem run_evaluates [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (fuel : Nat)
    (table : Stored State Symbol) (pending : List (List State))
    (enough : potential limit classified table pending ≤ fuel) :
    ∃ calls, calls ≤ fuel + 1 ∧
      Evaluation limit classified table pending calls (run limit classified fuel table pending) := by
  induction fuel generalizing table pending with
  | zero =>
      have emptyLength : pending.length = 0 := by
        unfold potential at enough
        omega
      have empty : pending = [] := List.length_eq_zero_iff.mp emptyLength
      subst pending
      refine ⟨1, by omega, ?_⟩
      change Evaluation limit classified table [] 1 (.ready table)
      exact .ready rfl
  | succ fuel ih =>
      cases checked : step limit classified table pending with
      | ready returned =>
          refine ⟨1, by omega, ?_⟩
          rw [run, checked]
          exact .ready checked
      | limitExceeded =>
          refine ⟨1, by omega, ?_⟩
          rw [run, checked]
          exact .limitExceeded checked
      | next nextTable nextPending =>
          have decreases := step_decreases limit classified table nextTable pending nextPending checked
          obtain ⟨calls, bounded, execution⟩ := ih nextTable nextPending (by omega)
          refine ⟨calls + 1, by omega, ?_⟩
          rw [run, checked]
          exact .next checked execution

private def ReadyValid [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) : Outcome State Symbol → Prop
  | .ready table => Valid limit classified table
  | _ => True

private theorem evaluation_valid [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (table : Stored State Symbol)
    (pending : List (List State)) (calls : Nat) (result : Outcome State Symbol)
    (execution : Evaluation limit classified table pending calls result) :
    Valid limit classified table → ReadyValid limit classified result := by
  induction execution with
  | ready checked =>
      intro valid
      have same := step_ready_eq limit classified _ _ _ checked
      rw [same]
      exact valid
  | limitExceeded _ => intro _; trivial
  | next checked _ ih =>
      intro valid
      exact ih (step_valid limit classified _ _ _ _ valid checked)

/-- Compute fuel from the cap and the complete classified input's maximum arity. -/
def fuel (limit : Nat) (classified : Classified State Symbol) : Nat :=
  limit * (limit * maxArity classified) + 1

/-- Start exactly at the singleton initial-state key with the empty source map. -/
def explore [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (root : State) : Outcome State Symbol :=
  run limit classified (fuel limit classified) [] [[root]]

/-- The public explorer executes source rounds within its computed bound. -/
theorem explore_evaluates [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (root : State) :
    ∃ calls, calls ≤ fuel limit classified + 1 ∧
      Evaluation limit classified [] [[root]] calls (explore limit classified root) := by
  exact run_evaluates limit classified (fuel limit classified) [] [[root]]
    (by simp [potential, fuel])

/-- Exhaustion is impossible at the public explorer's computed fuel. -/
theorem explore_terminal [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (root : State) :
    explore limit classified root ≠ .exhausted := by
  obtain ⟨calls, _, execution⟩ := explore_evaluates limit classified root
  exact Evaluation.terminal limit classified [] [[root]] calls _ execution

/-- Every returned map has distinct keys, both caps, and full source conjunction rows. -/
theorem explore_ready [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (limit : Nat) (classified : Classified State Symbol) (root : State) (returned : Stored State Symbol)
    (success : explore limit classified root = .ready returned) : Valid limit classified returned := by
  obtain ⟨calls, _, execution⟩ := explore_evaluates limit classified root
  have valid := evaluation_valid limit classified [] [[root]] calls _ execution (empty_valid limit classified)
  rw [success] at valid
  exact valid

/-- Use the literal source counting limit with no caller fuel or boundary premises. -/
def prepare [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol) (root : State) : Outcome State Symbol :=
  explore 1024 classified root

/-- The source-sized public preparation cannot exhaust its internal control bound. -/
theorem prepare_terminal [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol) (root : State) : prepare classified root ≠ .exhausted :=
  explore_terminal 1024 classified root

/-- Successful public preparation supplies both caps and literal original conjunction row readback. -/
theorem prepare_ready [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (classified : Classified State Symbol) (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) : Valid 1024 classified returned :=
  explore_ready 1024 classified root returned success

end MicroCFTA.SourceSizedConjunctionWorklist
