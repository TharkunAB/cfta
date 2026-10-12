import MicroCFTA.GroupedMinimum

/-!
# Validate the final recursive family discovery table

The accumulating discovery loop can retain a key or minimum that its final
body no longer has. The source rejects that result before returning a tied
family. Monotone constructor programs pass this check automatically.
-/
namespace MicroCFTA.GroupedProbeValidation
open MinimumSize GroupedProbe GroupedMinimum

/-- One entry is below another when the latter contains all its discoveries. -/
def Below (left right : Option (Option Nat)) : Prop := join left right = right

/-- Pointwise order on discovered keys and their attained minima. -/
def TableBelow (left right : Table Key) : Prop := ∀ key, Below (left key) (right key)

/-- A builder preserves the key and minimum discovery order. -/
def Monotone (build : Table Key → Table Key) : Prop :=
  ∀ left right, TableBelow left right → TableBelow (build left) (build right)

theorem best_assoc (a b c : Option Nat) : best (best a b) c = best a (best b c) := by
  cases a <;> cases b <;> cases c <;> simp [best, Nat.min_assoc]

theorem best_comm (a b : Option Nat) : best a b = best b a := by
  cases a <;> cases b <;> simp [best, Nat.min_comm]

theorem join_assoc (a b c : Option (Option Nat)) : join (join a b) c = join a (join b c) := by
  cases a <;> cases b <;> cases c <;> simp [join, best_assoc]

theorem join_comm (a b : Option (Option Nat)) : join a b = join b a := by
  cases a <;> cases b <;> simp [join, best_comm]

theorem below_refl (entry : Option (Option Nat)) : Below entry entry := by
  rcases entry with _ | (_ | size) <;> simp [Below, join, best]

/-- Combining alternatives preserves both input improvements. -/
theorem join_mono (a b c d : Option (Option Nat)) (left : Below a b) (right : Below c d) :
    Below (join a c) (join b d) := by
  unfold Below at *
  calc
    join (join a c) (join b d) = join (join a b) (join c d) := by
      rw [join_assoc, ← join_assoc c b d, join_comm c b, join_assoc b c d, ← join_assoc a b]
    _ = join b d := by rw [left, right]

/-- A pay increases both finite minima by one and preserves absence. -/
theorem pay_mono (a b : Option (Option Nat)) (below : Below a b) :
    Below (a.map (fun size => size.map (· + 1))) (b.map (fun size => size.map (· + 1))) := by
  rcases a with _ | (_ | a) <;> rcases b with _ | (_ | b) <;>
    simp_all [Below, join, best] <;> omega

/-- Product minima preserve key presence and every finite improvement. -/
theorem product_mono (a b c d : Option (Option Nat)) (left : Below a b) (right : Below c d) :
    Below (productEntry a c) (productEntry b d) := by
  rcases a with _ | (_ | a) <;> rcases b with _ | (_ | b) <;>
    rcases c with _ | (_ | c) <;> rcases d with _ | (_ | d) <;>
    simp_all [Below, join, best, productEntry, RecursionProbe.productMinimum] <;> omega

/-- The supported constructor algebra derives monotonicity without a callback premise. -/
theorem evaluate_mono (expression : Expression Key) (left right : Table Key) (below : TableBelow left right) :
    Below (evaluate expression left) (evaluate expression right) := by
  induction expression with
  | source sizes => exact below_refl _
  | occurrence key => exact below key
  | pay inner ih => exact pay_mono _ _ ih
  | choice first second ihl ihr => exact join_mono _ _ _ _ ihl ihr
  | product first second ihl ihr => exact product_mono _ _ _ _ ihl ihr

theorem build_monotone (program : Key → Expression Key) : Monotone (build program) :=
  fun left right below key => evaluate_mono (program key) left right below

/-- A monotone builder reached from an increasing step has a genuine fixed point. -/
theorem converge_builder_fixed (keys : List Key) (complete : ∀ key, key ∈ keys)
    (builder : Table Key → Table Key) (monotone : Monotone builder) (known : Table Key)
    (increasing : TableBelow known (builder known)) :
    builder (converge keys complete builder known) = converge keys complete builder known := by
  revert increasing
  induction known using converge.induct keys complete builder with
  | case1 known grown stable =>
      intro increasing
      dsimp only [grown] at stable
      have step_body : step builder known = builder known := funext increasing
      have fixed := (sameTable_correct keys complete _ _).mp stable
      rw [GroupedProbe.converge.eq_def]
      simp only [dite_eq_left stable]
      exact step_body.symm.trans fixed
  | case2 known grown unstable ih =>
      intro increasing
      dsimp only [grown] at unstable
      have step_body : step builder known = builder known := funext increasing
      have next : TableBelow (step builder known) (builder (step builder known)) := by
        rw [step_body]
        exact monotone known (builder known) increasing
      rw [GroupedProbe.converge.eq_def]
      simp only [dite_eq_right unstable]
      exact ih next

/-- The final source check compares the actual body table with the accumulated table. -/
def checked (keys : List Key) (complete : ∀ key, key ∈ keys)
    (builder : Table Key → Table Key) : Option (Table Key) :=
  let result := converge keys complete builder (fun _ => none)
  if sameTable keys (builder result) result then some result else none

/-- Successful validation derives an actual body fixed point, not only a stable union. -/
theorem checked_fixed (keys : List Key) (complete : ∀ key, key ∈ keys)
    (builder : Table Key → Table Key) (result : Table Key)
    (success : checked keys complete builder = some result) : builder result = result := by
  dsimp only [checked] at success
  split at success
  next fixed =>
    have same := Option.some.inj success
    subst result
    exact (sameTable_correct keys complete _ _).mp fixed
  next rejected => cases success

/-- No successful return can retain a vanished key or an earlier unsupported minimum. -/
theorem checked_entry (keys : List Key) (complete : ∀ key, key ∈ keys)
    (builder : Table Key → Table Key) (result : Table Key)
    (success : checked keys complete builder = some result) (key : Key) :
    builder result key = result key := congrFun (checked_fixed keys complete builder result success) key

/-- Every monotone builder from the empty table passes the new source check. -/
theorem checked_monotone (keys : List Key) (complete : ∀ key, key ∈ keys)
    (builder : Table Key → Table Key) (monotone : Monotone builder) :
    checked keys complete builder = some (converge keys complete builder (fun _ => none)) := by
  have fixed := converge_builder_fixed keys complete builder monotone (fun _ => none)
    (fun key => by simp [Below, join])
  simp [checked, (sameTable_correct keys complete _ _).mpr fixed]

/-- Existing constructor programs retain the exact original discovered table. -/
theorem checked_program (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Expression Key) :
    checked keys complete (build program) = some (discover keys complete program) :=
  checked_monotone keys complete (build program) (build_monotone program)

/-- Successful source validation preserves the independent least-attained-size theorem. -/
theorem checked_program_minimum (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Expression Key) (result : Table Key)
    (success : checked keys complete (build program) = some result) (key : Key) (size : Nat) :
    result key = some (some size) ↔
      Derives program (program key) size ∧ ∀ other, Derives program (program key) other → size ≤ other := by
  rw [checked_program] at success
  cases Option.some.inj success
  exact discover_minimum keys complete program key size

/-- The reproduced callback changes its finite base after the first key appears. -/
def changing (known : Table Unit) : Table Unit := fun _ =>
  if (known ()).isNone then some (some 0) else some (some 1)

/-- The old loop stops although the final body has minimum one. -/
theorem stale_minimum :
    step changing (fun _ => some (some 0)) = (fun _ => some (some 0)) ∧
      changing (fun _ => some (some 0)) () = some (some 1) := by
  constructor
  · funext key; cases key; rfl
  · rfl

/-- The added source validation rejects this retained false minimum. -/
theorem changing_rejected : checked [()] (fun key => by cases key; simp) changing = none := by
  have stopped : GroupedProbe.converge [()] (fun key => by cases key; simp) changing
      (fun _ => some (some 0)) = (fun _ => some (some 0)) := by
    rw [GroupedProbe.converge.eq_def]
    simp [GroupedProbe.sameTable, step, changing, join, best]
  dsimp only [checked]
  rw [GroupedProbe.converge.eq_def]
  rw [show step changing (fun _ => none) = (fun _ => some (some 0)) from rfl]
  simp [GroupedProbe.sameTable, changing, stopped]

end MicroCFTA.GroupedProbeValidation
