import MicroCFTA.EnumerationUntil
import MicroCFTA.EnumerationCPSChecked

namespace MicroCFTA.EnumerationUntilBridge

open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationUntil
open EnumerationCPSChecked (successes mem_successes)

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
    simp only [List.map_const']
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, pure]
  bind_pure_comp := by intros; simp [bind, pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; exact List.flatMap_assoc

/-- Binding preserves the order and multiplicity of successful rows. -/
theorem successes_bind (action : EnumerateM Symbol Guard α)
    (next : α → EnumerateM Symbol Guard β) (before : State Symbol Guard) :
    successes (ExceptT.run ((action >>= next) before)) =
      (successes (ExceptT.run (action before))).flatMap
        (fun pair => successes (ExceptT.run (next pair.1 pair.2))) := by
  rw [run_bind]
  generalize ExceptT.run (action before) = rows
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [successes] at ih
      cases row <;> simp [successes, ih, List.filterMap_append]

/-- A pure action has one successful row with the original state. -/
theorem successes_pure (value : α) (before : State Symbol Guard) :
    successes (ExceptT.run ((pure value : EnumerateM Symbol Guard α) before)) = [(value, before)] := rfl

/-- Equal continuations on each actual successful branch give equal successful rows. -/
theorem successes_bind_congr (action : EnumerateM Symbol Guard α)
    (left right : α → EnumerateM Symbol Guard β) (before : State Symbol Guard)
    (same : ∀ value after, Success action before value after →
      successes (ExceptT.run (left value after)) = successes (ExceptT.run (right value after))) :
    successes (ExceptT.run ((action >>= left) before)) =
      successes (ExceptT.run ((action >>= right) before)) := by
  rw [successes_bind, successes_bind]
  generalize rowsEq : successes (ExceptT.run (action before)) = rows
  have memberSame : ∀ pair ∈ rows,
      successes (ExceptT.run (left pair.1 pair.2)) = successes (ExceptT.run (right pair.1 pair.2)) := by
    intro pair member
    apply same pair.1 pair.2
    exact (mem_successes _ _ _).mp (rowsEq.symm ▸ member)
  clear rowsEq
  induction rows with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.flatMap_cons]
      rw [memberSame first (by simp), ih (fun pair member => memberSame pair (by simp [member]))]

/-- An action with no successful branch has an empty successful projection. -/
theorem successes_empty (action : EnumerateM Symbol Guard α) (before : State Symbol Guard)
    (absent : ∀ value after, ¬Success action before value after) :
    successes (ExceptT.run (action before)) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro pair member
  exact absent pair.1 pair.2 ((mem_successes _ _ _).mp member)

/-- Consecutive successful representative reads return the same stored value. -/
theorem getValue_repeat_value
    (firstFuel secondFuel uv : Nat)
    (before middle after : State Symbol Guard)
    (first second : UVarValue Symbol)
    (firstRead : Success (getValue firstFuel uv) before first middle)
    (secondRead : Success (getValue secondFuel uv) middle second after) :
    second = first := by
  obtain ⟨firstFound, firstLookup, firstStored, rfl⟩ :=
    (getValue_success firstFuel uv before middle first).mp firstRead
  obtain ⟨secondFound, secondLookup, secondStored, rfl⟩ :=
    (getValue_success secondFuel uv _ after second).mp secondRead
  change UnionFind.findRoot secondFuel firstFound.forest uv = some secondFound at secondLookup
  change before.values[secondFound.representative]? = some second at secondStored
  obtain ⟨path, preserved⟩ :=
    UnionFind.findRoot_correct firstFuel before.representatives uv firstFound firstLookup
  have same := (UnionFind.reaches_unique (preserved path)
    (UnionFind.findRoot_correct secondFuel firstFound.forest uv secondFound secondLookup).1).1
  rw [← same] at secondStored
  exact (Option.some.inj (firstStored.symm.trans secondStored)).symm

/-- An observed empty slot cannot expand successfully after that read. -/
theorem empty_out_after_read
    (graph : Graph Symbol Guard) (firstFuel fuel uv node : Nat)
    (scs : List Suspended) (before readState after : State Symbol Guard)
    (fragment : Fragment Symbol) (empty : graph.node node = .empty)
    (reading : Success (getValue firstFuel uv) before
      (.unenumerated (some node) scs) readState) :
    ¬Success (enumerateOut graph fuel uv) readState fragment after := by
  intro success
  unfold enumerateOut at success
  obtain ⟨value, readAgain, rereading, continued⟩ :=
    (success_bind _ _ _ _ _).mp success
  have same := getValue_repeat_value firstFuel (fuel + 1) uv before readState readAgain
    (.unenumerated (some node) scs) value reading rereading
  subst value
  obtain ⟨root, resolved, _, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨current, currentState, _, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨ignored, started, _, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨produced, expanded, expansion, _⟩ := (success_bind _ _ _ _ _).mp continued
  cases fuel with
  | zero =>
      exact (success_failure .fuelExhausted started expanded produced expansion).elim
  | succ fuel =>
      exact (reject_unsuccessful started expanded produced
        (by simpa only [empty, enumerateNode] using expansion)).elim

/-- A read-only observation cannot make a just-read empty slot expand successfully. -/
private theorem empty_observation (graph : Graph Symbol Guard)
    (oracle : Oracle Symbol Guard OracleState) (observer : ReadOnlyOracle oracle)
    (oracleState : OracleState) (firstFuel fuel uv node : Nat) (scs : List Suspended)
    (before readState : State Symbol Guard) (empty : graph.node node = .empty)
    (reading : Success (getValue firstFuel uv) before (.unenumerated (some node) scs) readState)
    (tail : Fragment Symbol → OracleState → EnumerateM Symbol Guard α) :
    successes (ExceptT.run ((do
      let decision ← oracle oracleState uv (.inr node)
      require (!decision.1)
      let fragment ← enumerateOut graph fuel uv
      tail fragment decision.2) readState)) = [] := by
  apply successes_empty
  intro value after success
  obtain ⟨decision, observed, observing, continued⟩ := (success_bind _ _ _ _ _).mp success
  have unchanged := observer oracleState uv (.inr node) readState decision observed observing
  subst observed
  obtain ⟨ignored, accepted, required, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨_, unchanged⟩ := (require_success _ readState accepted).mp required
  subst accepted
  obtain ⟨fragment, expanded, expansion, _⟩ := (success_bind _ _ _ _ _).mp continued
  exact empty_out_after_read graph firstFuel fuel uv node scs before readState expanded fragment empty reading expansion

/-- The eager specialization preserves every ordered successful continuation. -/
private theorem no_stop_eager_bind_successes (graph : Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (observer : ReadOnlyOracle oracle) (next : Option OracleState → EnumerateM Symbol Guard α)
    (fuel : Nat) (oracleState : OracleState) (before : State Symbol Guard) :
    successes (ExceptT.run ((enumerateUntil graph none (fun _ _ node => node)
      (fun remaining => enumerateNode graph remaining) order oracle fuel oracleState >>= next) before)) =
    successes (ExceptT.run ((enumerateFully graph order oracle fuel oracleState >>= fun _ => next none) before)) := by
  induction fuel generalizing oracleState before with
  | zero =>
      rw [enumerateUntil, enumerateFully, successes_bind, successes_bind]
      rfl
  | succ fuel ih =>
      rw [enumerateUntil, fully_action]
      simp only [bind_assoc]
      apply successes_bind_congr
      intro available scanned _
      cases selected : pickNext (order oracleState) available with
      | done => simp only [pure_bind]
      | stuck => rw [successes_bind, successes_bind]; rfl
      | expand uv =>
          simp only [bind_assoc]
          apply successes_bind_congr
          intro value readState reading
          cases value with
          | eliminated | enumerated _ => rw [successes_bind, successes_bind]; rfl
          | unenumerated node scs =>
              cases node with
              | none => rw [successes_bind, successes_bind]; rfl
              | some node =>
                  simp only [bind_assoc]
                  apply successes_bind_congr
                  intro repeated checked checking
                  cases repeated with
                  | true => simp only [↓reduceIte]; exact ih oracleState checked
                  | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      cases view : graph.node node with
                      | empty =>
                          have same : checked = readState :=
                            ((success_pure false false readState checked).mp
                              (by simpa only [checkRepeated, view] using checking)).2
                          subst checked
                          rw [successes_bind]
                          change [] = _
                          simpa only [bind_assoc] using
                            (empty_observation graph oracle observer oracleState (fuel + 1) (fuel + 1)
                              uv node scs scanned readState view reading
                              (fun fragment beforeState => do
                                let (afterReject, afterState) ← oracle beforeState uv (.inl fragment)
                                require (!afterReject)
                                enumerateFully graph order oracle fuel afterState
                                next none)).symm
                      | alternatives edges | recursive body | unresolved ref =>
                          simp only [enumerateOutWith_eager, bind_assoc]
                          apply successes_bind_congr
                          intro decision observed _
                          rcases decision with ⟨beforeReject, beforeState⟩
                          apply successes_bind_congr
                          intro ignored accepted _
                          cases ignored
                          apply successes_bind_congr
                          intro fragment expanded _
                          apply successes_bind_congr
                          intro decision observedAfter _
                          rcases decision with ⟨afterReject, afterState⟩
                          apply successes_bind_congr
                          intro ignored acceptedAfter _
                          cases ignored
                          exact ih afterState acceptedAfter

/-- With eager expansion, successful rows retain their order and full final states. -/
theorem no_stop_eager_successes (graph : Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (observer : ReadOnlyOracle oracle) (fuel : Nat) (oracleState : OracleState)
    (before : State Symbol Guard) :
    successes (ExceptT.run (enumerateUntil graph none (fun _ _ node => node)
      (fun remaining => enumerateNode graph remaining) order oracle fuel oracleState before)) =
    (successes (ExceptT.run (enumerateFully graph order oracle fuel oracleState before))).map
      (fun pair => ((none : Option OracleState), pair.2)) := by
  have bridge := no_stop_eager_bind_successes graph order oracle observer
    (fun result => pure result) fuel oracleState before
  simpa only [bind_pure, successes_bind, successes_pure,
    List.map_eq_flatMap] using bridge

/-- A successful eager call completes with exactly an old-driver final state. -/
theorem no_stop_eager_success_iff (graph : Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (observer : ReadOnlyOracle oracle) (fuel : Nat) (oracleState : OracleState)
    (before after : State Symbol Guard) (result : Option OracleState) :
    Success (enumerateUntil graph none (fun _ _ node => node)
      (fun remaining => enumerateNode graph remaining) order oracle fuel oracleState) before result after ↔
    result = none ∧ Success (enumerateFully graph order oracle fuel oracleState) before () after := by
  constructor
  · intro success
    have member := (mem_successes _ result after).mpr success
    rw [no_stop_eager_successes graph order oracle observer fuel oracleState before] at member
    obtain ⟨⟨value, final⟩, oldMember, equality⟩ := List.mem_map.mp member
    cases value
    cases equality
    exact ⟨rfl, (mem_successes _ () final).mp oldMember⟩
  · rintro ⟨rfl, success⟩
    apply (mem_successes _ none after).mp
    rw [no_stop_eager_successes graph order oracle observer fuel oracleState before]
    exact List.mem_map.mpr ⟨((), after), (mem_successes _ () after).mpr success, rfl⟩

/-- Completed eager calls retain safety, grow the supply, and finish every candidate. -/
theorem no_stop_eager_outcome (graph : Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (observer : ReadOnlyOracle oracle) (fuel : Nat) (oracleState : OracleState)
    (before after : State Symbol Guard) (result : Option OracleState) (safe : Safe before)
    (success : Success (enumerateUntil graph none (fun _ _ node => node)
      (fun remaining => enumerateNode graph remaining) order oracle fuel oracleState) before result after) :
    Safe after ∧ before.counter ≤ after.counter ∧ Finished graph after := by
  exact enumerateFully_outcome graph order oracle observer fuel oracleState before after safe
    ((no_stop_eager_success_iff graph order oracle observer fuel oracleState before after result).mp success).2

end MicroCFTA.EnumerationUntilBridge
