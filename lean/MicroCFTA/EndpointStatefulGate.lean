import MicroCFTA.InternedFreshOrdinaryStatefulGate

/-!
# Endpoint-aware constrained-recursion gate

The worker retains the source order at 24a710a3. Ordinary endpoints read
both free names and constrained recursion below the endpoint. The two node
predicates are pure inputs here. Their global memo tables require a separate
source adapter. Same-path unfolding retains the full stored constructor call
and its actual returned heap. Missing fuel and pending construction remain
separate outcomes.
-/
namespace MicroCFTA.EndpointStatefulGate
open InternedConstructorTemplates InternedNestedConstruction EqualityNormalize
open InternedFreshOrdinaryStatefulGate (anyKnown child anyKnown_stable)

/-- Preserve source tag tests, metadata shortcuts, endpoint reads, and unfolding order. -/
def dispatch [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
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
            | [] => .done (some (!value.free.isEmpty || reaches value)) state
            | index :: rest => match value with
                | .node _ edges _ _ => anyKnown (fun edge current => child recur edge.children index rest current) edges state
                | _ => .done (some false) state

/-- Fuel bounds gate recursion; each unfolding executes the actual stored constructor call. -/
def nodeMeets [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool) :
    Nat → Path → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Option Bool)
  | 0, _, _, state => .done none state
  | fuel + 1, path, value, state => dispatch unconstrained reaches (nodeMeets unconstrained reaches fuel) path value state

/-- A source equality path starts below its constrained edge. -/
def meets [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (fuel : Nat) (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard) :
    Outcome Symbol Guard (Option Bool) :=
  match path with
  | [] => .done (some false) state
  | index :: rest => child (nodeMeets unconstrained reaches fuel) values index rest state

/-- Scan original class paths in order and pass each returned heap to the next path. -/
def classMeets [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (fuel : Nat) (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard) :
    Outcome Symbol Guard (Option Bool) :=
  anyKnown (fun path current => meets unconstrained reaches fuel values path current) paths state

/-- Stable recursive calls retain each completed dispatch answer and its exact returned heap. -/
theorem dispatch_stable [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (before after : Path → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Option Bool))
    (stable : ∀ path value state answer final, before path value state = .done (some answer) final →
      after path value state = .done (some answer) final)
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (done : dispatch unconstrained reaches before path value state = .done (some answer) final) :
    dispatch unconstrained reaches after path value state = .done (some answer) final := by
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

/-- More fuel retains each completed node answer and its exact returned heap. -/
theorem fuel_stable [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (fuel extra : Nat) (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : nodeMeets unconstrained reaches fuel path value state = .done (some answer) final) :
    nodeMeets unconstrained reaches (fuel + extra) path value state = .done (some answer) final := by
  induction fuel generalizing path value state answer final with
  | zero => simp [nodeMeets] at done
  | succ fuel ih =>
      rw [Nat.succ_add, nodeMeets]
      exact dispatch_stable unconstrained reaches _ _
        (fun path value state answer final => ih path value state answer final) path value state answer final done

/-- More fuel retains each completed selected-child answer and its returned heap. -/
theorem child_fuel_stable [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (fuel extra : Nat) (values : List (Value Symbol Guard)) (index : Nat) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : child (nodeMeets unconstrained reaches fuel) values index path state = .done (some answer) final) :
    child (nodeMeets unconstrained reaches (fuel + extra)) values index path state = .done (some answer) final := by
  cases selected : values[index]? with
  | none => simpa [child, selected] using done
  | some value =>
      simpa only [child, selected] using fuel_stable unconstrained reaches fuel extra path value state answer final
        (by simpa only [child, selected] using done)

/-- More fuel retains each completed edge-path answer and its returned heap. -/
theorem meets_fuel_stable [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (fuel extra : Nat) (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : meets unconstrained reaches fuel values path state = .done (some answer) final) :
    meets unconstrained reaches (fuel + extra) values path state = .done (some answer) final := by
  cases path with
  | nil => exact done
  | cons index rest =>
      cases selected : values[index]? with
      | none => simpa [meets, child, selected] using done
      | some value =>
          simpa only [meets, child, selected] using fuel_stable unconstrained reaches fuel extra rest value state answer final
            (by simpa only [meets, child, selected] using done)

/-- More fuel retains a completed class decision and all ordered path-scan effects. -/
theorem class_fuel_stable [DecidableEq (EdgeKey Symbol Guard)] (unconstrained reaches : Value Symbol Guard → Bool)
    (fuel extra : Nat) (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : classMeets unconstrained reaches fuel values paths state = .done (some answer) final) :
    classMeets unconstrained reaches (fuel + extra) values paths state = .done (some answer) final :=
  anyKnown_stable _ _ (fun path current result after found =>
    meets_fuel_stable unconstrained reaches fuel extra values path current result after found) paths state answer final done

end MicroCFTA.EndpointStatefulGate
