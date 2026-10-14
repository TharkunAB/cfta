import MicroCFTA.InternedFreshOrdinaryStoredSubstitution
import MicroCFTA.ConstrainedRecursionGate

/-!
# Ordered constrained-recursion gate with actual returned caches

The worker keeps source dispatch order. Each completed false edge or path
passes its returned cache to the next query. A true result stops the scan.
Missing gate fuel and pending constructor requests remain separate results.
-/
namespace MicroCFTA.InternedFreshOrdinaryStatefulGate
open InternedConstructorTemplates InternedNestedConstruction
open EqualityNormalize

/-- Ordered disjunction threads each returned cache and stops at true or unfinished evaluation. -/
def anyKnown (test : Item → State Symbol Guard → Outcome Symbol Guard (Option Bool)) :
    List Item → State Symbol Guard → Outcome Symbol Guard (Option Bool)
  | [], state => .done (some false) state
  | first :: rest, state => (test first state).bind fun answer after =>
      match answer with
      | some false => anyKnown test rest after
      | _ => .done answer after

/-- A missing child returns false without a cache effect. -/
def child (recur : Path → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Option Bool))
    (values : List (Value Symbol Guard)) (index : Nat) (path : Path) (state : State Symbol Guard) :
    Outcome Symbol Guard (Option Bool) :=
  match values[index]? with
  | none => .done (some false) state
  | some value => recur path value state

/-- One source dispatch preserves tag tests, metadata shortcuts, and same-path unfolding. -/
def dispatch [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (recur : Path → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Option Bool))
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) : Outcome Symbol Guard (Option Bool) :=
  match value with
  | .reference _ | .union .. => .done (some true) state
  | _ =>
      if value.depth == 0 && value.free.isEmpty then .done (some false) state
      else match value with
        | .mu .. =>
            if !unconstrained value then .done (some true) state
            else if value.free.isEmpty then .done (some false) state
            else (InternedFreshOrdinaryStoredSubstitution.unfold value state).bind fun next after =>
              recur path next after
        | _ => match path with
            | [] => .done (some (!value.free.isEmpty)) state
            | index :: rest => match value with
                | .node _ edges _ _ => anyKnown (fun edge current => child recur edge.children index rest current) edges state
                | _ => .done (some false) state

/-- Fuel instruments gate recursion only; each unfolding is the full actual repaired constructor call. -/
def nodeMeets [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :
    Nat → Path → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Option Bool)
  | 0, _, _, state => .done none state
  | fuel + 1, path, value, state => dispatch unconstrained (nodeMeets unconstrained fuel) path value state

/-- A source equality path starts below the constrained edge's root. -/
def meets [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel : Nat) (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard) :
    Outcome Symbol Guard (Option Bool) :=
  match path with
  | [] => .done (some false) state
  | index :: rest => child (nodeMeets unconstrained fuel) values index rest state

/-- A class checks its original ordered paths and retains shared cache effects. -/
def classMeets [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel : Nat) (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard) :
    Outcome Symbol Guard (Option Bool) :=
  anyKnown (fun path current => meets unconstrained fuel values path current) paths state

/-- Progress of every completed test preserves the exact disjunction result and final cache. -/
theorem anyKnown_stable (before after : Item → State Symbol Guard → Outcome Symbol Guard (Option Bool))
    (stable : ∀ item state answer final, before item state = .done (some answer) final →
      after item state = .done (some answer) final)
    (items : List Item) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (done : anyKnown before items state = .done (some answer) final) :
    anyKnown after items state = .done (some answer) final := by
  induction items generalizing state with
  | nil => exact done
  | cons first rest ih =>
      cases found : before first state with
      | pending key current => simp [anyKnown, found, Outcome.bind] at done
      | done result current =>
          cases result with
          | none => simp [anyKnown, found, Outcome.bind] at done
          | some result =>
              rw [anyKnown, stable first state result current found, Outcome.bind]
              cases result with
              | false => apply ih; simpa only [anyKnown, found, Outcome.bind] using done
              | true => simpa only [anyKnown, found, Outcome.bind] using done

/-- Progress of recursive calls preserves the exact completed source dispatch and final cache. -/
theorem dispatch_stable [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (before after : Path → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Option Bool))
    (stable : ∀ path value state answer final, before path value state = .done (some answer) final →
      after path value state = .done (some answer) final)
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (done : dispatch unconstrained before path value state = .done (some answer) final) :
    dispatch unconstrained after path value state = .done (some answer) final := by
  unfold dispatch at done ⊢
  cases value with
  | reference | union => exact done
  | empty => simpa [Value.depth, Value.free] using done
  | mu entry body depth ordinary =>
      simp only at done ⊢
      split at done
      · rename_i shortcut
        simpa only [shortcut, Bool.false_eq_true, ↓reduceIte] using done
      · rename_i shortcut
        simp only [shortcut, Bool.false_eq_true, ↓reduceIte]
        split at done
        · rename_i constrained
          simpa only [constrained, Bool.false_eq_true, ↓reduceIte] using done
        · rename_i constrained
          simp only [constrained, Bool.false_eq_true, ↓reduceIte]
          split at done
          · rename_i closed
            simpa only [closed, Bool.false_eq_true, ↓reduceIte] using done
          · rename_i closed
            simp only [closed, Bool.false_eq_true, ↓reduceIte]
            cases unfolded : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state with
            | pending key current => simp [unfolded, Outcome.bind] at done
            | done next current =>
                simp only [unfolded, Outcome.bind] at done ⊢
                exact stable path next current answer final done
  | node entry edges depth free =>
      simp only at done ⊢
      split at done
      · rename_i shortcut
        simpa only [shortcut, Bool.false_eq_true, ↓reduceIte] using done
      · rename_i shortcut
        simp only [shortcut, Bool.false_eq_true, ↓reduceIte]
        cases path with
        | nil => exact done
        | cons index rest =>
            apply anyKnown_stable _ _ ?_ edges state answer final done
            intro edge current result afterState found
            cases selected : edge.children[index]? with
            | none => simpa [child, selected] using found
            | some next =>
                simpa only [child, selected] using
                  stable rest next current result afterState (by simpa only [child, selected] using found)

/-- More fuel preserves each completed Boolean result and its exact returned cache. -/
theorem fuel_stable [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel extra : Nat) (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : nodeMeets unconstrained fuel path value state = .done (some answer) final) :
    nodeMeets unconstrained (fuel + extra) path value state = .done (some answer) final := by
  induction fuel generalizing path value state answer final with
  | zero => simp [nodeMeets] at done
  | succ fuel ih =>
      rw [Nat.succ_add, nodeMeets]
      exact dispatch_stable unconstrained _ _
        (fun path value state answer final => ih path value state answer final) path value state answer final done

/-- More fuel preserves each completed selected-child result and its final cache. -/
theorem child_fuel_stable [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel extra : Nat) (values : List (Value Symbol Guard)) (index : Nat) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : child (nodeMeets unconstrained fuel) values index path state = .done (some answer) final) :
    child (nodeMeets unconstrained (fuel + extra)) values index path state = .done (some answer) final := by
  cases selected : values[index]? with
  | none => simpa [child, selected] using done
  | some value =>
      simpa only [child, selected] using fuel_stable unconstrained fuel extra path value state answer final
        (by simpa only [child, selected] using done)

/-- More fuel preserves each completed edge-path result and its final cache. -/
theorem meets_fuel_stable [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel extra : Nat) (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : meets unconstrained fuel values path state = .done (some answer) final) :
    meets unconstrained (fuel + extra) values path state = .done (some answer) final := by
  cases path with
  | nil => exact done
  | cons index rest =>
      cases selected : values[index]? with
      | none => simpa [meets, child, selected] using done
      | some value =>
          simpa only [meets, child, selected] using
            fuel_stable unconstrained fuel extra rest value state answer final (by simpa only [meets, child, selected] using done)

/-- More fuel preserves a completed class decision and every cache effect of its ordered path scan. -/
theorem class_fuel_stable [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel extra : Nat) (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : classMeets unconstrained fuel values paths state = .done (some answer) final) :
    classMeets unconstrained (fuel + extra) values paths state = .done (some answer) final :=
  anyKnown_stable _ _ (fun path current result after found =>
    meets_fuel_stable unconstrained fuel extra values path current result after found) paths state answer final done

end MicroCFTA.InternedFreshOrdinaryStatefulGate
