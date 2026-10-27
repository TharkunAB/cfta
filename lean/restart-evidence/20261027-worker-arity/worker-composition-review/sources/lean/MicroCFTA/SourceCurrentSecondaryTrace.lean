import MicroCFTA.SourceCurrentMuEndpoint

/-!
# Complete execution graphs for the current secondary policy

The graph retains actual same-path unfolding and every returned heap.
A constrained Mu endpoint returns whether it is open. Interior constrained
Mu values refuse the path. True results omit the remaining source suffix.
The secondary mode never reads its descendant predicate argument.
-/
namespace MicroCFTA.SourceCurrentSecondaryTrace
open InternedConstructorTemplates InternedNestedConstruction EqualityNormalize
open InternedFreshOrdinaryStatefulGate (anyKnown child anyKnown_stable)

/-- The current secondary dispatch has no descendant-predicate read. -/
abbrev dispatch [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :=
  SourceCurrentMuEndpoint.dispatch false unconstrained (fun _ => false)

/-- The current secondary worker retains the full source constructor schedule. -/
abbrev nodeMeets [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :=
  SourceCurrentMuEndpoint.nodeMeets false unconstrained (fun _ => false)

/-- Forest paths retain the exact current selected-child worker. -/
abbrev meets [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :=
  SourceCurrentMuEndpoint.meets false unconstrained (fun _ => false)

/-- Ordered classes use the actual current secondary worker. -/
abbrev classMeets [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :=
  SourceCurrentMuEndpoint.classMeets false unconstrained (fun _ => false)

mutual
/-- The source gate's logical graph retains its decision and complete cache trace. -/
inductive NodeTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :
    Path → Value Symbol Guard → State Symbol Guard → Bool → State Symbol Guard → Prop where
  | empty : NodeTrace unconstrained path .empty state false state
  | reference : NodeTrace unconstrained path (.reference name) state true state
  | union (members : List (Value Symbol Guard)) : NodeTrace unconstrained path (.union entry members depth free) state true state
  | finite (fast : (depth == 0 && free.isEmpty) = true) :
      NodeTrace unconstrained path (.node entry edges depth free) state false state
  | endpoint (slow : (depth == 0 && free.isEmpty) = false) :
      NodeTrace unconstrained [] (.node entry edges depth free) state (!free.isEmpty) state
  | branches (slow : (depth == 0 && free.isEmpty) = false)
      (trace : EdgesTrace unconstrained index rest edges state answer final) :
      NodeTrace unconstrained (index :: rest) (.node entry edges depth free) state answer final
  | constrained (blocked : unconstrained (.mu entry body depth ordinary) = false) :
      NodeTrace unconstrained path (.mu entry body depth ordinary) state
        (match path with | [] => !(Value.mu entry body depth ordinary).free.isEmpty | _ :: _ => true) state
  | closed (plain : unconstrained (.mu entry body depth ordinary) = true)
      (closed : (Value.mu entry body depth ordinary).free.isEmpty = true) :
      NodeTrace unconstrained path (.mu entry body depth ordinary) state false state
  | unfold (plain : unconstrained (.mu entry body depth ordinary) = true)
      (opened : (Value.mu entry body depth ordinary).free.isEmpty = false)
      (actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done next after)
      (trace : NodeTrace unconstrained path next after answer final) :
      NodeTrace unconstrained path (.mu entry body depth ordinary) state answer final

/-- A child lookup either returns false immediately or follows the exact selected source child. -/
inductive ChildTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :
    List (Value Symbol Guard) → Nat → Path → State Symbol Guard → Bool → State Symbol Guard → Prop where
  | missing (absent : values[index]? = none) : ChildTrace unconstrained values index path state false state
  | present (found : values[index]? = some value) (trace : NodeTrace unconstrained path value state answer final) :
      ChildTrace unconstrained values index path state answer final

/-- Ordered edge disjunction threads false results and stops at its first true result. -/
inductive EdgesTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :
    Nat → Path → List (EdgeValue Symbol Guard) → State Symbol Guard → Bool → State Symbol Guard → Prop where
  | nil : EdgesTrace unconstrained index path [] state false state
  | stop (head : ChildTrace unconstrained edge.children index path state true final) :
      EdgesTrace unconstrained index path (edge :: rest) state true final
  | next (head : ChildTrace unconstrained edge.children index path state false middle)
      (tail : EdgesTrace unconstrained index path rest middle answer final) :
      EdgesTrace unconstrained index path (edge :: rest) state answer final
end

/-- An edge path starts below its root and follows its exact selected child. -/
inductive PathTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) : Path → State Symbol Guard → Bool → State Symbol Guard → Prop where
  | empty : PathTrace unconstrained values [] state false state
  | child (trace : ChildTrace unconstrained values index rest state answer final) :
      PathTrace unconstrained values (index :: rest) state answer final

/-- A class follows original path order and stops at the first true decision. -/
inductive ClassTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) : Class → State Symbol Guard → Bool → State Symbol Guard → Prop where
  | nil : ClassTrace unconstrained values [] state false state
  | stop (head : PathTrace unconstrained values path state true final) :
      ClassTrace unconstrained values (path :: rest) state true final
  | next (head : PathTrace unconstrained values path state false middle)
      (tail : ClassTrace unconstrained values rest middle answer final) :
      ClassTrace unconstrained values (path :: rest) state answer final


/-- Progress of recursive calls preserves the exact completed source dispatch and final cache. -/
theorem dispatch_stable [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (before after : Path → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Option Bool))
    (stable : ∀ path value state answer final, before path value state = .done (some answer) final →
      after path value state = .done (some answer) final)
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (done : dispatch unconstrained before path value state = .done (some answer) final) :
    dispatch unconstrained after path value state = .done (some answer) final := by
  unfold dispatch SourceCurrentMuEndpoint.dispatch at done ⊢
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
        | nil => simpa using done
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
  | zero => simp [nodeMeets, SourceCurrentMuEndpoint.nodeMeets] at done
  | succ fuel ih =>
      rw [Nat.succ_add]
      simp only [SourceCurrentMuEndpoint.nodeMeets]
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
      | none => simpa [meets, SourceCurrentMuEndpoint.meets, child, selected] using done
      | some value =>
          simpa only [meets, SourceCurrentMuEndpoint.meets, child, selected] using
            fuel_stable unconstrained fuel extra rest value state answer final (by simpa only [meets, SourceCurrentMuEndpoint.meets, child, selected] using done)

/-- More fuel preserves a completed class decision and every cache effect of its ordered path scan. -/
theorem class_fuel_stable [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel extra : Nat) (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : classMeets unconstrained fuel values paths state = .done (some answer) final) :
    classMeets unconstrained (fuel + extra) values paths state = .done (some answer) final :=
  anyKnown_stable _ _ (fun path current result after found =>
    meets_fuel_stable unconstrained fuel extra values path current result after found) paths state answer final done

/-- The constrained branch retains the exact endpoint openness test and complete heap. -/
theorem constrained_result [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel : Nat) (path : Path) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (blocked : unconstrained (.mu entry body depth ordinary) = false) :
    nodeMeets unconstrained (fuel + 1) path (.mu entry body depth ordinary) state =
      .done (some (match path with | [] => !(Value.mu entry body depth ordinary).free.isEmpty | _ :: _ => true)) state := by
  cases path <;> cases opened : (Value.mu entry body depth ordinary).free.isEmpty <;>
    simp [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, blocked, opened]

/-- A completed child worker follows the corresponding logical lookup and source query. -/
theorem child_trace_of_done [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel : Nat) (sound : ∀ path value state answer final,
      nodeMeets unconstrained fuel path value state = .done (some answer) final →
      NodeTrace unconstrained path value state answer final)
    (values : List (Value Symbol Guard)) (index : Nat) (path : Path)
    (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (done : child (nodeMeets unconstrained fuel) values index path state = .done (some answer) final) :
    ChildTrace unconstrained values index path state answer final := by
  cases found : values[index]? with
  | none =>
      simp only [child, found, Outcome.done.injEq, Option.some.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact .missing found
  | some value => exact .present found (sound path value state answer final (by simpa only [child, found] using done))

/-- A completed edge scan has the same ordered logical trace and exact intermediate caches. -/
theorem edges_trace_of_done [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel : Nat) (sound : ∀ path value state answer final,
      nodeMeets unconstrained fuel path value state = .done (some answer) final →
      NodeTrace unconstrained path value state answer final)
    (edges : List (EdgeValue Symbol Guard)) (index : Nat) (path : Path)
    (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (done : anyKnown (fun edge current => child (nodeMeets unconstrained fuel) edge.children index path current)
      edges state = .done (some answer) final) : EdgesTrace unconstrained index path edges state answer final := by
  induction edges generalizing state with
  | nil =>
      simp only [anyKnown, Outcome.done.injEq, Option.some.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact .nil
  | cons first rest ih =>
      cases found : child (nodeMeets unconstrained fuel) first.children index path state with
      | pending key after => simp [anyKnown, found, Outcome.bind] at done
      | done result after =>
          cases result with
          | none => simp [anyKnown, found, Outcome.bind] at done
          | some result =>
              have head := child_trace_of_done unconstrained fuel sound first.children index path state result after found
              cases result with
              | false => exact .next head (ih after (by simpa only [anyKnown, found, Outcome.bind] using done))
              | true =>
                  simp only [anyKnown, found, Outcome.bind, Outcome.done.injEq, Option.some.injEq] at done
                  rcases done with ⟨rfl, rfl⟩
                  exact .stop head

/-- Every completed instrumented gate query has an unbounded source execution graph. -/
theorem node_trace_of_done [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel : Nat) (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : nodeMeets unconstrained fuel path value state = .done (some answer) final) :
    NodeTrace unconstrained path value state answer final := by
  induction fuel generalizing path value state answer final with
  | zero => simp [nodeMeets, SourceCurrentMuEndpoint.nodeMeets] at done
  | succ fuel ih =>
      cases value with
      | empty =>
          simp [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, Value.free] at done
          rcases done with ⟨rfl, rfl⟩
          exact .empty
      | reference name =>
          simp only [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Outcome.done.injEq, Option.some.injEq] at done
          rcases done with ⟨rfl, rfl⟩
          exact .reference
      | union entry members depth free =>
          simp only [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Outcome.done.injEq, Option.some.injEq] at done
          rcases done with ⟨rfl, rfl⟩
          exact .union members
      | mu entry body depth ordinary =>
          cases plain : unconstrained (.mu entry body depth ordinary) with
          | false =>
              rw [constrained_result unconstrained fuel path entry body depth ordinary state plain] at done
              have same := Outcome.done.inj done
              have answerEq := Option.some.inj same.1
              cases answerEq
              cases same.2
              exact .constrained plain
          | true =>
              cases closed : (Value.mu entry body depth ordinary).free.isEmpty with
              | true =>
                  simp [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, plain, closed] at done
                  rcases done with ⟨rfl, rfl⟩
                  exact .closed plain closed
              | false =>
                  simp [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, plain, closed] at done
                  cases actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state with
                  | pending key after => simp [actual, Outcome.bind] at done
                  | done next after =>
                      exact .unfold plain closed actual (ih path next after answer final (by simpa only [actual, Outcome.bind] using done))
      | node entry edges depth free =>
          cases fast : depth == 0 && free.isEmpty with
          | true =>
              simp [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, Value.free, fast] at done
              rcases done with ⟨rfl, rfl⟩
              exact .finite fast
          | false =>
              cases path with
              | nil =>
                  simp only [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, Value.free, fast, Bool.false_and, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                    Outcome.done.injEq, Option.some.injEq] at done
                  rcases done with ⟨rfl, rfl⟩
                  exact .endpoint fast
              | cons index rest =>
                  apply NodeTrace.branches fast
                  apply edges_trace_of_done unconstrained fuel ih edges index rest state answer final
                  simpa only [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, Value.free, fast, Bool.false_eq_true, ↓reduceIte] using done

/-- A logical node trace has a finite execution with the exact result and final cache. -/
theorem node_trace_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (trace : NodeTrace unconstrained path value state answer final) :
    ∃ fuel, nodeMeets unconstrained fuel path value state = .done (some answer) final := by
  induction trace using NodeTrace.rec
      (motive_2 := fun values index path state answer final _ =>
        ∃ fuel, child (nodeMeets unconstrained fuel) values index path state = .done (some answer) final)
      (motive_3 := fun index path edges state answer final _ =>
        ∃ fuel, anyKnown (fun edge current => child (nodeMeets unconstrained fuel) edge.children index path current)
          edges state = .done (some answer) final) with
  | empty => exact ⟨1, by simp [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, Value.free]⟩
  | reference => exact ⟨1, by simp [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch]⟩
  | union => exact ⟨1, by simp [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch]⟩
  | finite fast => exact ⟨1, by simp only [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, Value.free, fast, ↓reduceIte]⟩
  | endpoint slow => exact ⟨1, by simp only [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, Value.free, slow, Bool.false_and, Bool.or_false, Bool.false_eq_true, ↓reduceIte]⟩
  | branches slow trace ih =>
      obtain ⟨fuel, done⟩ := ih
      exact ⟨fuel + 1, by simpa only [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, Value.free, slow, Bool.false_eq_true, ↓reduceIte] using done⟩
  | constrained blocked => exact ⟨1, constrained_result _ _ _ _ _ _ _ _ blocked⟩
  | closed plain closed => exact ⟨1, by simp [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, plain, closed]⟩
  | unfold plain opened actual trace ih =>
      obtain ⟨fuel, done⟩ := ih
      exact ⟨fuel + 1, by simpa [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, plain, opened, actual, Outcome.bind] using done⟩
  | missing absent => exact ⟨0, by simp [child, absent]⟩
  | present found trace ih =>
      obtain ⟨fuel, done⟩ := ih
      exact ⟨fuel, by simpa only [child, found] using done⟩
  | nil => exact ⟨0, rfl⟩
  | stop head ih =>
      obtain ⟨fuel, done⟩ := ih
      exact ⟨fuel, by simp only [anyKnown, done, Outcome.bind]⟩
  | next head tail headIH tailIH =>
      obtain ⟨headFuel, headDone⟩ := headIH
      obtain ⟨tailFuel, tailDone⟩ := tailIH
      have headMore := child_fuel_stable unconstrained headFuel tailFuel _ _ _ _ _ _ headDone
      have tailMore := anyKnown_stable _ _
        (fun edge current answer final done => child_fuel_stable unconstrained tailFuel headFuel
          edge.children _ _ current answer final done) _ _ _ _ tailDone
      refine ⟨headFuel + tailFuel, ?_⟩
      simpa only [anyKnown, headMore, Outcome.bind, Nat.add_comm] using tailMore

/-- A logical child trace has finite execution at its exact selected source slot. -/
theorem child_trace_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (index : Nat) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard) (trace : ChildTrace unconstrained values index path state answer final) :
    ∃ fuel, child (nodeMeets unconstrained fuel) values index path state = .done (some answer) final := by
  cases trace with
  | missing absent => exact ⟨0, by simp [child, absent]⟩
  | present found trace =>
      obtain ⟨fuel, done⟩ := node_trace_complete _ _ _ _ _ _ trace
      exact ⟨fuel, by simpa only [child, found] using done⟩

/-- The source graph is equivalent to finite actual instrumented execution. -/
theorem node_trace_iff [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard) :
    NodeTrace unconstrained path value state answer final ↔
      ∃ fuel, nodeMeets unconstrained fuel path value state = .done (some answer) final := by
  constructor
  · exact node_trace_complete unconstrained path value state answer final
  · rintro ⟨fuel, done⟩
    exact node_trace_of_done unconstrained fuel path value state answer final done

/-- Logical source traces are functional in both Boolean output and complete final cache. -/
theorem node_trace_unique [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard)
    (first second : Bool) (firstState secondState : State Symbol Guard)
    (left : NodeTrace unconstrained path value state first firstState)
    (right : NodeTrace unconstrained path value state second secondState) : first = second ∧ firstState = secondState := by
  obtain ⟨leftFuel, leftDone⟩ := node_trace_complete unconstrained path value state first firstState left
  obtain ⟨rightFuel, rightDone⟩ := node_trace_complete unconstrained path value state second secondState right
  have leftMore := fuel_stable unconstrained leftFuel rightFuel path value state first firstState leftDone
  have rightMore := fuel_stable unconstrained rightFuel leftFuel path value state second secondState rightDone
  have equal := leftMore.symm.trans (by simpa only [Nat.add_comm] using rightMore)
  simpa only [Outcome.done.injEq, Option.some.injEq] using equal

/-- Every completed path worker follows its logical source graph. -/
theorem path_trace_of_done [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel : Nat) (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : meets unconstrained fuel values path state = .done (some answer) final) :
    PathTrace unconstrained values path state answer final := by
  cases path with
  | nil =>
      simp only [meets, SourceCurrentMuEndpoint.meets, Outcome.done.injEq, Option.some.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact .empty
  | cons index rest =>
      exact .child (child_trace_of_done unconstrained fuel (node_trace_of_done unconstrained fuel) values index rest state answer final done)

/-- Every logical path graph has a finite execution with the exact final cache. -/
theorem path_trace_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard) (trace : PathTrace unconstrained values path state answer final) :
    ∃ fuel, meets unconstrained fuel values path state = .done (some answer) final := by
  cases trace with
  | empty => exact ⟨0, rfl⟩
  | child trace => exact child_trace_complete _ _ _ _ _ _ _ trace

/-- A completed class worker retains the exact logical ordered path trace. -/
theorem class_trace_of_done [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel : Nat) (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (done : classMeets unconstrained fuel values paths state = .done (some answer) final) :
    ClassTrace unconstrained values paths state answer final := by
  induction paths generalizing state with
  | nil =>
      simp only [classMeets, SourceCurrentMuEndpoint.classMeets, anyKnown, Outcome.done.injEq, Option.some.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact .nil
  | cons first rest ih =>
      cases found : meets unconstrained fuel values first state with
      | pending key after => simp [classMeets, SourceCurrentMuEndpoint.classMeets, anyKnown, found, Outcome.bind] at done
      | done result after =>
          cases result with
          | none => simp [classMeets, SourceCurrentMuEndpoint.classMeets, anyKnown, found, Outcome.bind] at done
          | some result =>
              have head := path_trace_of_done unconstrained fuel values first state result after found
              cases result with
              | false => exact .next head (ih after (by simpa only [classMeets, SourceCurrentMuEndpoint.classMeets, anyKnown, found, Outcome.bind] using done))
              | true =>
                  simp only [classMeets, SourceCurrentMuEndpoint.classMeets, anyKnown, found, Outcome.bind, Outcome.done.injEq, Option.some.injEq] at done
                  rcases done with ⟨rfl, rfl⟩
                  exact .stop head

/-- Every logical class graph has finite execution with the same ordered cache effects. -/
theorem class_trace_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard) (trace : ClassTrace unconstrained values paths state answer final) :
    ∃ fuel, classMeets unconstrained fuel values paths state = .done (some answer) final := by
  induction trace with
  | nil => exact ⟨0, rfl⟩
  | stop head =>
      obtain ⟨fuel, done⟩ := path_trace_complete _ _ _ _ _ _ head
      exact ⟨fuel, by simp only [classMeets, SourceCurrentMuEndpoint.classMeets, anyKnown, done, Outcome.bind]⟩
  | next head tail ih =>
      obtain ⟨headFuel, headDone⟩ := path_trace_complete _ _ _ _ _ _ head
      obtain ⟨tailFuel, tailDone⟩ := ih
      have headMore := meets_fuel_stable unconstrained headFuel tailFuel _ _ _ _ _ headDone
      have tailMore := class_fuel_stable unconstrained tailFuel headFuel _ _ _ _ _ tailDone
      refine ⟨headFuel + tailFuel, ?_⟩
      simpa only [classMeets, SourceCurrentMuEndpoint.classMeets, anyKnown, headMore, Outcome.bind, Nat.add_comm] using tailMore

/-- The logical class graph is exactly finite actual stateful class execution. -/
theorem class_trace_iff [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard) :
    ClassTrace unconstrained values paths state answer final ↔
      ∃ fuel, classMeets unconstrained fuel values paths state = .done (some answer) final := by
  constructor
  · exact class_trace_complete unconstrained values paths state answer final
  · rintro ⟨fuel, done⟩
    exact class_trace_of_done unconstrained fuel values paths state answer final done

/-- Class traces are functional in the Boolean decision and the complete final shared cache. -/
theorem class_trace_unique [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (first second : Bool) (firstState secondState : State Symbol Guard)
    (left : ClassTrace unconstrained values paths state first firstState)
    (right : ClassTrace unconstrained values paths state second secondState) : first = second ∧ firstState = secondState := by
  obtain ⟨leftFuel, leftDone⟩ := class_trace_complete unconstrained values paths state first firstState left
  obtain ⟨rightFuel, rightDone⟩ := class_trace_complete unconstrained values paths state second secondState right
  have leftMore := class_fuel_stable unconstrained leftFuel rightFuel values paths state first firstState leftDone
  have rightMore := class_fuel_stable unconstrained rightFuel leftFuel values paths state second secondState rightDone
  have equal := leftMore.symm.trans (by simpa only [Nat.add_comm] using rightMore)
  simpa only [Outcome.done.injEq, Option.some.injEq] using equal


/-- Every ordered edge graph has finite execution with its complete actual returned heap. -/
theorem edges_trace_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (index : Nat) (path : Path) (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard) (trace : EdgesTrace unconstrained index path edges state answer final) :
    ∃ fuel, anyKnown (fun edge current => child (nodeMeets unconstrained fuel) edge.children index path current)
      edges state = .done (some answer) final := by
  induction edges generalizing state answer final with
  | nil => cases trace; exact ⟨0, rfl⟩
  | cons edge rest ih =>
      cases trace with
      | stop head =>
          obtain ⟨fuel, done⟩ := child_trace_complete _ _ _ _ _ _ _ head
          exact ⟨fuel, by simp only [anyKnown, done, Outcome.bind]⟩
      | next head tail =>
          obtain ⟨headFuel, headDone⟩ := child_trace_complete _ _ _ _ _ _ _ head
          obtain ⟨tailFuel, tailDone⟩ := ih _ _ _ tail
          have headMore := child_fuel_stable unconstrained headFuel tailFuel _ _ _ _ _ _ headDone
          have tailMore := anyKnown_stable _ _
            (fun edge current result after done => child_fuel_stable unconstrained tailFuel headFuel
              edge.children index path current result after done) rest _ _ _ tailDone
          exact ⟨headFuel + tailFuel, by simpa only [anyKnown, headMore, Outcome.bind, Nat.add_comm] using tailMore⟩

/-- The disabled endpoint mode omits the descendant predicate in every source dispatch. -/
theorem actual_current_dispatch_eq [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    (recur : Path → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Option Bool))
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) :
    SourceCurrentMuEndpoint.dispatch false unconstrained reaches recur path value state =
      dispatch unconstrained recur path value state := by
  rfl

/-- The current secondary worker is independent of its disabled descendant argument at every fuel. -/
theorem actual_current_node_eq [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat) (path : Path)
    (value : Value Symbol Guard) (state : State Symbol Guard) :
    SourceCurrentMuEndpoint.nodeMeets false unconstrained reaches fuel path value state =
      nodeMeets unconstrained fuel path value state := by
  induction fuel generalizing path value state with
  | zero => rfl
  | succ fuel ih =>
      change SourceCurrentMuEndpoint.dispatch false unconstrained reaches
        (SourceCurrentMuEndpoint.nodeMeets false unconstrained reaches fuel) path value state =
        dispatch unconstrained (nodeMeets unconstrained fuel) path value state
      rw [actual_current_dispatch_eq]
      have same : SourceCurrentMuEndpoint.nodeMeets false unconstrained reaches fuel = nodeMeets unconstrained fuel :=
        funext fun path => funext fun value => funext fun state => ih path value state
      rw [same]

/-- Every current forest-path outcome retains the exact source-selected heap. -/
theorem actual_current_meets_eq [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard) :
    SourceCurrentMuEndpoint.meets false unconstrained reaches fuel values path state =
      meets unconstrained fuel values path state := by
  cases path with
  | nil => rfl
  | cons index rest =>
      simp only [SourceCurrentMuEndpoint.meets, meets, child]
      split <;> simp only [actual_current_node_eq]

/-- Every current ordered class outcome has the exact same short circuit and returned heap. -/
theorem actual_current_class_eq [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard) :
    SourceCurrentMuEndpoint.classMeets false unconstrained reaches fuel values paths state =
      classMeets unconstrained fuel values paths state := by
  simp only [SourceCurrentMuEndpoint.classMeets, classMeets, actual_current_meets_eq]

/-- An actual bounded current node completion derives its graph without a graph premise. -/
theorem actual_current_node_trace_of_done [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat) (path : Path)
    (value : Value Symbol Guard) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (actual : SourceCurrentMuEndpoint.nodeMeets false unconstrained reaches fuel path value state = .done (some answer) final) :
    NodeTrace unconstrained path value state answer final := by
  rw [actual_current_node_eq] at actual
  exact node_trace_of_done unconstrained fuel path value state answer final actual

/-- An actual current child completion derives its selected-child graph directly. -/
theorem actual_current_child_trace_of_done [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (values : List (Value Symbol Guard)) (index : Nat) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (actual : child (SourceCurrentMuEndpoint.nodeMeets false unconstrained reaches fuel)
      values index path state = .done (some answer) final) :
    ChildTrace unconstrained values index path state answer final := by
  have same : SourceCurrentMuEndpoint.nodeMeets false unconstrained reaches fuel = nodeMeets unconstrained fuel :=
    funext fun path => funext fun value => funext fun state => actual_current_node_eq unconstrained reaches fuel path value state
  rw [same] at actual
  exact child_trace_of_done unconstrained fuel (node_trace_of_done unconstrained fuel) values index path state answer final actual

/-- An actual current ordered edge completion derives its full reached edge graph. -/
theorem actual_current_edges_trace_of_done [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (edges : List (EdgeValue Symbol Guard)) (index : Nat) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (actual : anyKnown (fun edge current => child (SourceCurrentMuEndpoint.nodeMeets false unconstrained reaches fuel)
      edge.children index path current) edges state = .done (some answer) final) :
    EdgesTrace unconstrained index path edges state answer final := by
  have same : SourceCurrentMuEndpoint.nodeMeets false unconstrained reaches fuel = nodeMeets unconstrained fuel :=
    funext fun path => funext fun value => funext fun state => actual_current_node_eq unconstrained reaches fuel path value state
  rw [same] at actual
  exact edges_trace_of_done unconstrained fuel (node_trace_of_done unconstrained fuel) edges index path state answer final actual

/-- An actual bounded current path completion derives its graph at the same physical cache. -/
theorem actual_current_path_trace_of_done [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (actual : SourceCurrentMuEndpoint.meets false unconstrained reaches fuel values path state = .done (some answer) final) :
    PathTrace unconstrained values path state answer final := by
  rw [actual_current_meets_eq] at actual
  exact path_trace_of_done unconstrained fuel values path state answer final actual

/-- An actual bounded current class completion derives every reached ordered path and exact returned heap. -/
theorem actual_current_class_trace_of_done [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (actual : SourceCurrentMuEndpoint.classMeets false unconstrained reaches fuel values paths state = .done (some answer) final) :
    ClassTrace unconstrained values paths state answer final := by
  rw [actual_current_class_eq] at actual
  exact class_trace_of_done unconstrained fuel values paths state answer final actual

/-- A node graph constructs finite execution of the actual current worker for any descendant argument. -/
theorem actual_current_node_trace_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (path : Path)
    (value : Value Symbol Guard) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (trace : NodeTrace unconstrained path value state answer final) :
    ∃ fuel, SourceCurrentMuEndpoint.nodeMeets false unconstrained reaches fuel path value state = .done (some answer) final := by
  obtain ⟨fuel, done⟩ := node_trace_complete unconstrained path value state answer final trace
  exact ⟨fuel, by rw [actual_current_node_eq]; exact done⟩

/-- A class graph constructs finite execution of the actual current ordered worker. -/
theorem actual_current_class_trace_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard) (trace : ClassTrace unconstrained values paths state answer final) :
    ∃ fuel, SourceCurrentMuEndpoint.classMeets false unconstrained reaches fuel values paths state = .done (some answer) final := by
  obtain ⟨fuel, done⟩ := class_trace_complete unconstrained values paths state answer final trace
  exact ⟨fuel, by rw [actual_current_class_eq]; exact done⟩

end MicroCFTA.SourceCurrentSecondaryTrace
