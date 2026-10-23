import MicroCFTA.EnumerationDriver

namespace MicroCFTA.EnumerationUntilBridge

open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule

variable {Symbol Guard : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

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

end MicroCFTA.EnumerationUntilBridge
