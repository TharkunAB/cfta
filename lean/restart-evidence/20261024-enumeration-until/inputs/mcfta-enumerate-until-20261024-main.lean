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
