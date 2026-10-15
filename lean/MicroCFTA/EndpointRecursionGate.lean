import MicroCFTA.ConstrainedRecursionGate

/-!
# Equality gate with endpoint descendant checks

This is the policy from main 24a710a3. Earlier gate modules retain the
previous policy. The new endpoint read is explicit. Source record traversal
and the global predicate memo require their own correspondence proofs.
-/
namespace MicroCFTA.EndpointRecursionGate
open Language EqualityNormalize EqualityReduction
open RecursiveReductionBarrier (View finite)
open ConstrainedRecursionGate (anyKnown child anyKnown_false anyKnown_stable)

/-- The current gate adds a descendant predicate to the previous source reads. -/
structure Read (Node : Type) extends previous : ConstrainedRecursionGate.Read Node where
  reaches : Node → Bool

/-- Preserve the source tag order, finite shortcut, and same-path unfolding. -/
def dispatch (read : Read Node) (recur : Path → Node → Option Bool)
    (path : Path) (node : Node) : Option Bool :=
  match read.view node with
  | .reference | .union => some true
  | _ =>
      if finite read.toRead node then some false
      else match read.view node with
        | .binder =>
            if !read.unconstrained node then some true
            else if (read.free node).isEmpty then some false
            else recur path (read.unfold node)
        | _ => match path with
            | [] => some (!(read.free node).isEmpty || read.reaches node)
            | index :: rest => match read.view node with
                | .branches edges => anyKnown (fun nodes => child recur nodes index rest) edges
                | _ => some false

/-- Fuel records unfinished evaluation and never treats it as a clear path. -/
def nodeMeets (read : Read Node) : Nat → Path → Node → Option Bool
  | 0, _, _ => none
  | fuel + 1, path, node => dispatch read (nodeMeets read fuel) path node

/-- Equality paths start below their edge root. A missing child is clear. -/
def meets (read : Read Node) (fuel : Nat) (nodes : List Node) : Path → Option Bool
  | [] => some false
  | index :: rest => child (nodeMeets read fuel) nodes index rest

/-- Class paths retain source order and stop at true or unfinished evaluation. -/
def classMeets (read : Read Node) (fuel : Nat) (nodes : List Node) (paths : Class) : Option Bool :=
  anyKnown (meets read fuel nodes) paths

/-- The bounded pass retains a class when its check is unfinished. -/
def blocked (read : Read Node) (fuel : Nat) (nodes : List Node) (paths : Class) : Bool :=
  (classMeets read fuel nodes paths).getD true

/-- Install the current gate without changing narrowing primitives or constraints. -/
def guarded (read : Read Node) (fuel : Nat) (ops : Operations Node Symbol) : Operations Node Symbol :=
  { ops with blocked := blocked read fuel }

/-- Progress of recursive calls preserves each completed dispatch. -/
theorem dispatch_stable (read : Read Node) (before after : Path → Node → Option Bool)
    (stable : ∀ path node result, before path node = some result → after path node = some result)
    (path : Path) (node : Node) (result : Bool)
    (completed : dispatch read before path node = some result) :
    dispatch read after path node = some result := by
  unfold dispatch at completed ⊢
  cases view : read.view node <;> simp only [view] at completed ⊢
  all_goals try exact completed
  all_goals by_cases closed : finite read.toRead node = true
  all_goals simp only [closed, ↓reduceIte] at completed ⊢
  all_goals try exact completed
  · cases plain : read.unconstrained node <;> simp only [plain] at completed ⊢
    · exact completed
    · by_cases free : (read.free node).isEmpty = true
      · simpa only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, free] using completed
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, free] at completed ⊢
        exact stable path _ result completed
  · cases path with
    | nil => exact completed
    | cons index rest =>
        apply anyKnown_stable _ _ ?_ _ result completed
        intro nodes value found
        cases present : nodes[index]? with
        | none => simpa [child, present] using found
        | some next =>
            simpa only [child, present] using stable rest next value (by simpa [child, present] using found)

/-- Additional fuel preserves each completed Boolean result. -/
theorem fuel_stable (read : Read Node) (fuel extra : Nat) (path : Path) (node : Node)
    (result : Bool) (completed : nodeMeets read fuel path node = some result) :
    nodeMeets read (fuel + extra) path node = some result := by
  induction fuel generalizing path node result with
  | zero => simp [nodeMeets] at completed
  | succ fuel ih =>
      simp only [nodeMeets] at completed
      rw [Nat.succ_add]
      exact dispatch_stable read _ _ (fun path node result => ih path node result) path node result completed

/-- A clear current dispatch is also clear under the previous endpoint policy. -/
theorem dispatch_clear (read : Read Node) (current previous : Path → Node → Option Bool)
    (clear : ∀ path node, current path node = some false → previous path node = some false)
    (path : Path) (node : Node) (done : dispatch read current path node = some false) :
    ConstrainedRecursionGate.dispatch read.previous previous path node = some false := by
  unfold dispatch at done
  unfold ConstrainedRecursionGate.dispatch
  cases view : read.view node <;> simp only [view] at done ⊢
  all_goals try contradiction
  all_goals by_cases shortcut : finite read.toRead node = true
  all_goals simp only [shortcut, ↓reduceIte] at done ⊢
  all_goals try rfl
  · cases path with
    | nil => simpa using (Bool.or_eq_false_iff.mp (Option.some.inj done)).1
    | cons index rest => exact done
  · cases plain : read.unconstrained node <;> simp only [plain] at done ⊢
    · exact done
    · by_cases closed : (read.free node).isEmpty = true
      · simp [closed]
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, closed] at done ⊢
        exact clear path _ done
  · cases path with
    | nil => exact congrArg some (Bool.or_eq_false_iff.mp (Option.some.inj done)).1
    | cons index rest =>
        apply (anyKnown_false _ _).mpr
        intro nodes member
        have result := (anyKnown_false _ _).mp done nodes member
        cases selected : nodes[index]? with
        | none => simp [child, selected]
        | some next => simpa only [child, selected] using clear rest next (by simpa [child, selected] using result)

/-- The stronger gate can only remove completed clear decisions at a fixed fuel amount. -/
theorem clear_previous (read : Read Node) (fuel : Nat) (path : Path) (node : Node)
    (done : nodeMeets read fuel path node = some false) :
    ConstrainedRecursionGate.nodeMeets read.previous fuel path node = some false := by
  induction fuel generalizing path node with
  | zero => simp [nodeMeets] at done
  | succ fuel ih => exact dispatch_clear read _ _ ih path node done

/-- The finite shortcut precedes the new endpoint predicate. -/
theorem finite_clear (read : Read Node) (fuel : Nat) (path : Path) (node : Node)
    (ordinary : read.view node = .branches edges) (closed : finite read.toRead node = true) :
    nodeMeets read (fuel + 1) path node = some false := by
  simp [nodeMeets, dispatch, ordinary, closed]

/-- An ordinary endpoint now checks free references and constrained descendants. -/
theorem endpoint (read : Read Node) (fuel : Nat) (node : Node) (edges : List (List Node))
    (view : read.view node = .branches edges)
    (zero_clear : read.nested node = 0 → read.reaches node = false) :
    nodeMeets read (fuel + 1) [] node = some (!(read.free node).isEmpty || read.reaches node) := by
  by_cases shortcut : finite read.toRead node = true
  · obtain ⟨zero, closed⟩ := (RecursiveReductionBarrier.finite_iff _ _).mp shortcut
    simp [nodeMeets, dispatch, view, shortcut, closed, zero_clear zero]
  · simp [nodeMeets, dispatch, view, shortcut]

/-- A closed constrained descendant blocks a class even when the endpoint is ordinary. -/
theorem endpoint_blocked (read : Read Node) (fuel : Nat) (node : Node) (edges : List (List Node))
    (view : read.view node = .branches edges) (nested : read.nested node ≠ 0)
    (descendant : read.reaches node = true) : nodeMeets read (fuel + 1) [] node = some true := by
  simp [nodeMeets, dispatch, view, finite, nested, descendant]

/-- References and stored unions remain barriers before all metadata checks. -/
theorem opaque_blocked (read : Read Node) (fuel : Nat) (path : Path) (node : Node)
    (barrier : read.view node = .reference ∨ read.view node = .union) :
    nodeMeets read (fuel + 1) path node = some true := by
  rcases barrier with reference | union
  · simp [nodeMeets, dispatch, reference]
  · simp [nodeMeets, dispatch, union]

/-- Closed unconstrained Mu nodes remain clear without invoking the endpoint read. -/
theorem closed_binder_clear (read : Read Node) (fuel : Nat) (path : Path) (node : Node)
    (view : read.view node = .binder) (plain : read.unconstrained node = true)
    (closed : read.free node = []) : nodeMeets read (fuel + 1) path node = some false := by
  simp [nodeMeets, dispatch, view, plain, closed]

/-- A selected class has completed false checks for every original path. -/
theorem selected_iff (read : Read Node) (fuel : Nat) (ops : Operations Node Symbol)
    (classes : Constraints) (nodes : List Node) (paths : Class) :
    paths ∈ selectedClasses (guarded read fuel ops) classes nodes ↔
      paths ∈ classes ∧ ∀ path ∈ paths, meets read fuel nodes path = some false := by
  simp only [selectedClasses, guarded, List.mem_filter]
  have gate : (!(blocked read fuel nodes paths)) = true ↔ classMeets read fuel nodes paths = some false := by
    unfold blocked
    cases classMeets read fuel nodes paths with
    | none => simp
    | some value => cases value <;> simp
  rw [gate]
  exact and_congr_right (fun _ => anyKnown_false _ _)

/-- Every class selected by the stronger gate was also selected by the previous policy. -/
theorem selected_subset (read : Read Node) (fuel : Nat) (ops : Operations Node Symbol)
    (classes : Constraints) (nodes : List Node) (paths : Class)
    (selected : paths ∈ selectedClasses (guarded read fuel ops) classes nodes) :
    paths ∈ selectedClasses (ConstrainedRecursionGate.guarded read.previous fuel ops) classes nodes := by
  obtain ⟨member, clear⟩ := (selected_iff read fuel ops classes nodes paths).mp selected
  apply (ConstrainedRecursionGate.selected_iff read.previous fuel ops classes nodes paths).mpr
  refine ⟨member, ?_⟩
  intro path present
  have completed := clear path present
  cases path with
  | nil => rfl
  | cons index rest =>
      cases found : nodes[index]? with
      | none => simp [ConstrainedRecursionGate.meets, child, found]
      | some node => simpa only [ConstrainedRecursionGate.meets, child, found] using
          clear_previous read fuel rest node (by simpa [meets, child, found] using completed)

/-- Retaining more classes does not change any primitive graph law. -/
theorem guarded_laws (read : Read Node) (fuel : Nat) (ops : Operations Node Symbol)
    (laws : Laws ops) : Laws (guarded read fuel ops) where
  empty := laws.empty
  intersect := laws.intersect
  project := laws.project
  require_narrow := laws.require_narrow
  require_keep := laws.require_keep
  edit_narrow := laws.edit_narrow
  edit_keep := laws.edit_keep
  contradiction := laws.contradiction

/-- A completed bounded pass preserves the original constrained language under the primitive laws. -/
theorem pass_exact [DecidableEq Node] (read : Read Node) (fuel : Nat)
    (ops : Operations Node Symbol) (laws : Laws ops) (localClasses inherited : Constraints)
    (active : Active localClasses) (nodes : List Node) (term : Term Symbol) :
    (Forest ops (pass (guarded read fuel ops) localClasses inherited nodes) term ∧
      Satisfies term localClasses ∧ Satisfies term inherited) ↔
    Forest ops nodes term ∧ Satisfies term localClasses ∧ Satisfies term inherited :=
  constrained_pass_exact (guarded read fuel ops) (guarded_laws read fuel ops laws)
    localClasses inherited active nodes term

end MicroCFTA.EndpointRecursionGate
