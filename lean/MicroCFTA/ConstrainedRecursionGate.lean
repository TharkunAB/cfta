import MicroCFTA.RecursiveReductionBarrier

/-!
# Current equality gate for constrained recursion

The current source permits closed unconstrained binders. An open
unconstrained binder unfolds without consuming a path index. This worker
therefore uses explicit fuel. `none` means unfinished evaluation. It does
not mean that a class is clear. The previous path-only barrier remains in
`RecursiveReductionBarrier` for comparison.
-/
namespace MicroCFTA.ConstrainedRecursionGate
open Language EqualityNormalize EqualityReduction
open RecursiveReductionBarrier (View finite)

/-- Cached metadata and the two additional source operations. -/
structure Read (Node : Type) extends RecursiveReductionBarrier.Read Node where
  unconstrained : Node → Bool
  unfold : Node → Node

/-- Ordered Boolean disjunction with an explicit unfinished result. -/
def anyKnown (test : Item → Option Bool) : List Item → Option Bool
  | [] => some false
  | item :: rest => match test item with
      | none => none
      | some true => some true
      | some false => anyKnown test rest

/-- A missing child is clear. A present child uses the supplied worker. -/
def child (recur : Path → Node → Option Bool) (nodes : List Node)
    (index : Nat) (rest : Path) : Option Bool :=
  match nodes[index]? with
  | none => some false
  | some node => recur rest node

/-- One source dispatch. The order of the metadata and node tests is retained. -/
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
            | [] => some (!(read.free node).isEmpty)
            | index :: rest => match read.view node with
                | .branches edges => anyKnown (fun nodes => child recur nodes index rest) edges
                | _ => some false

/-- Instrument the recursive source worker without guessing a termination bound. -/
def nodeMeets (read : Read Node) : Nat → Path → Node → Option Bool
  | 0, _, _ => none
  | fuel + 1, path, node => dispatch read (nodeMeets read fuel) path node

/-- Only same-path unfolding needs an extra decrease. Child traversal already
decreases path length. Supplying this rank for actual interned nodes remains
a representation obligation. -/
structure UnfoldingRank (read : Read Node) where
  rank : Node → Nat
  decreases : ∀ node, read.view node = .binder → read.unconstrained node = true →
    (read.free node).isEmpty = false → rank (read.unfold node) < rank node

/-- The unbounded source worker terminates when open unconstrained unfoldings
have a decreasing rank. No path-length bound alone is assumed. -/
def total (read : Read Node) (ranking : UnfoldingRank read) (path : Path) (node : Node) : Bool :=
  match _view : read.view node with
  | .reference | .union => true
  | _ =>
      if finite read.toRead node then false
      else match _binder : read.view node with
        | .binder =>
            if _plain : read.unconstrained node then
              if _closed : (read.free node).isEmpty then false
              else total read ranking path (read.unfold node)
            else true
        | _ => match path with
            | [] => !(read.free node).isEmpty
            | index :: rest => match read.view node with
                | .branches edges => edges.any (fun nodes =>
                    match nodes[index]? with
                    | none => false
                    | some next => total read ranking rest next)
                | _ => false
termination_by (path.length, ranking.rank node)
decreasing_by
  · apply Prod.Lex.right
    exact ranking.decreases node _binder _plain (Bool.eq_false_iff.mpr _closed)
  · apply Prod.Lex.left
    simp

/-- The constrained edge starts traversal below its own root. -/
def meets (read : Read Node) (fuel : Nat) (nodes : List Node) : Path → Option Bool
  | [] => some false
  | index :: rest => child (nodeMeets read fuel) nodes index rest

/-- The complete class gate preserves the source's ordered short circuit. -/
def classMeets (read : Read Node) (fuel : Nat) (nodes : List Node) (paths : Class) : Option Bool :=
  anyKnown (meets read fuel nodes) paths

/-- This bounded adapter skips an unfinished class. The Haskell worker has no fuel limit. -/
def blocked (read : Read Node) (fuel : Nat) (nodes : List Node) (paths : Class) : Bool :=
  (classMeets read fuel nodes paths).getD true

/-- Install the current gate in the existing reduction schedule. -/
def guarded (read : Read Node) (fuel : Nat) (ops : Operations Node Symbol) : Operations Node Symbol :=
  { ops with blocked := blocked read fuel }

/-- Successful disjunction results remain unchanged when its tests make progress. -/
theorem anyKnown_stable (before after : Item → Option Bool)
    (stable : ∀ item result, before item = some result → after item = some result)
    (items : List Item) (result : Bool) (completed : anyKnown before items = some result) :
    anyKnown after items = some result := by
  induction items with
  | nil => exact completed
  | cons item rest ih =>
      cases found : before item with
      | none => simp [anyKnown, found] at completed
      | some value =>
          cases value <;> simp only [anyKnown, found] at completed <;>
            simp only [anyKnown, stable item _ found]
          · exact ih completed
          · exact completed

/-- False disjunction means that every path check completed and returned false. -/
theorem anyKnown_false (test : Item → Option Bool) (items : List Item) :
    anyKnown test items = some false ↔ ∀ item ∈ items, test item = some false := by
  induction items with
  | nil => simp [anyKnown]
  | cons item rest ih =>
      cases found : test item with
      | none => simp [anyKnown, found]
      | some value => cases value <;> simp [anyKnown, found, ih]

/-- A completed instrumented disjunction agrees with a total decision for
every completed child request. Unvisited alternatives need no premise. -/
theorem anyKnown_agrees (partialTest : Item → Option Bool) (totalTest : Item → Bool)
    (same : ∀ item result, partialTest item = some result → totalTest item = result)
    (items : List Item) (result : Bool) (completed : anyKnown partialTest items = some result) :
    items.any totalTest = result := by
  induction items with
  | nil => simpa [anyKnown] using completed
  | cons item rest ih =>
      cases found : partialTest item with
      | none => simp [anyKnown, found] at completed
      | some value =>
          cases value <;> simp only [anyKnown, found] at completed <;>
            simp only [List.any_cons, same item _ found]
          · simpa using ih completed
          · simpa using completed

/-- Progress of child checks preserves every completed source dispatch. -/
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
        | some next => simpa only [child, present] using stable rest next value (by simpa [child, present] using found)

/-- Additional fuel cannot change a completed decision. -/
theorem fuel_stable (read : Read Node) (fuel extra : Nat) (path : Path) (node : Node)
    (result : Bool) (completed : nodeMeets read fuel path node = some result) :
    nodeMeets read (fuel + extra) path node = some result := by
  induction fuel generalizing path node result with
  | zero => simp [nodeMeets] at completed
  | succ fuel ih =>
      simp only [nodeMeets] at completed
      rw [Nat.succ_add]
      exact dispatch_stable read _ _ (fun path node result => ih path node result) path node result completed

/-- Every completed bounded evaluation is the total source decision under
the unfolding-rank premise. Fuel cannot introduce a different result. -/
theorem completed_agrees (read : Read Node) (ranking : UnfoldingRank read)
    (fuel : Nat) (path : Path) (node : Node) (result : Bool)
    (completed : nodeMeets read fuel path node = some result) :
    total read ranking path node = result := by
  induction fuel generalizing path node result with
  | zero => simp [nodeMeets] at completed
  | succ fuel ih =>
      simp only [nodeMeets, dispatch] at completed
      rw [total.eq_def]
      cases view : read.view node with
      | reference | union => simpa [view] using completed
      | empty =>
          cases path <;> cases finiteNode : finite read.toRead node <;> simpa [view, finiteNode] using completed
      | binder =>
          by_cases finiteNode : finite read.toRead node = true
          · simpa [view, finiteNode] using completed
          · cases plain : read.unconstrained node
            · simpa [view, finiteNode, plain] using completed
            · by_cases free : (read.free node).isEmpty = true
              · simpa [view, finiteNode, plain, free] using completed
              · simp only [view, finiteNode, plain, free, Bool.not_true,
                  Bool.false_eq_true, ↓reduceIte, ↓reduceDIte] at completed ⊢
                exact ih path _ result completed
      | branches edges =>
          by_cases finiteNode : finite read.toRead node = true
          · simpa [view, finiteNode] using completed
          · cases path with
            | nil => simpa [view, finiteNode] using completed
            | cons index rest =>
                simp only [view, finiteNode] at completed ⊢
                apply anyKnown_agrees _ _ ?_ _ result completed
                intro nodes value found
                cases present : nodes[index]? with
                | none => simpa [child, present] using found
                | some next => simpa only [present] using ih rest next value (by simpa [child, present] using found)

/-- Explicit recursive references remain barriers even if metadata is inaccurate. -/
theorem reference_blocked (read : Read Node) (fuel : Nat) (path : Path) (node : Node)
    (view : read.view node = .reference) : nodeMeets read (fuel + 1) path node = some true := by
  simp [nodeMeets, dispatch, view]

/-- Explicit interned union nodes remain barriers before every metadata shortcut. -/
theorem union_blocked (read : Read Node) (fuel : Nat) (path : Path) (node : Node)
    (view : read.view node = .union) : nodeMeets read (fuel + 1) path node = some true := by
  simp [nodeMeets, dispatch, view]

/-- A closed unconstrained binder now permits every equality path. -/
theorem closed_unconstrained_clear (read : Read Node) (fuel : Nat) (path : Path) (node : Node)
    (view : read.view node = .binder) (plain : read.unconstrained node = true)
    (closed : read.free node = []) : nodeMeets read (fuel + 1) path node = some false := by
  simp [nodeMeets, dispatch, view, plain, closed]

/-- A constrained binder with nonfinite metadata remains blocked. -/
theorem constrained_blocked (read : Read Node) (fuel : Nat) (path : Path) (node : Node)
    (view : read.view node = .binder) (constrained : read.unconstrained node = false)
    (recursive : finite read.toRead node = false) :
    nodeMeets read (fuel + 1) path node = some true := by
  simp [nodeMeets, dispatch, view, constrained, recursive]

/-- An open unconstrained binder follows its unfolding at the same path. -/
theorem open_unfold (read : Read Node) (fuel : Nat) (path : Path) (node : Node)
    (view : read.view node = .binder) (plain : read.unconstrained node = true)
    (opened : (read.free node).isEmpty = false) :
    nodeMeets read (fuel + 1) path node = nodeMeets read fuel path (read.unfold node) := by
  simp [nodeMeets, dispatch, view, plain, opened, finite]

/-- An ordinary endpoint depends only on its free references, not nested binders. -/
theorem endpoint (read : Read Node) (fuel : Nat) (node : Node) (edges : List (List Node))
    (view : read.view node = .branches edges) :
    nodeMeets read (fuel + 1) [] node = some (!(read.free node).isEmpty) := by
  by_cases closed : (read.free node).isEmpty = true
  · simp [nodeMeets, dispatch, view, closed]
  · have opened : (read.free node).isEmpty = false := Bool.eq_false_iff.mpr closed
    simp [nodeMeets, dispatch, view, opened, finite]

/-- A selected class contains only completed clear path checks. -/
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

/-- A gate change leaves the local graph laws unchanged. -/
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

/-- Each bounded pass retains exactly the terms satisfying the original
constraints. This also covers classes skipped for unfinished evaluation. -/
theorem pass_exact [DecidableEq Node] (read : Read Node) (fuel : Nat)
    (ops : Operations Node Symbol) (laws : Laws ops) (localClasses inherited : Constraints)
    (active : Active localClasses) (nodes : List Node) (term : Term Symbol) :
    (Forest ops (pass (guarded read fuel ops) localClasses inherited nodes) term ∧
      Satisfies term localClasses ∧ Satisfies term inherited) ↔
    Forest ops nodes term ∧ Satisfies term localClasses ∧ Satisfies term inherited :=
  constrained_pass_exact (guarded read fuel ops) (guarded_laws read fuel ops laws)
    localClasses inherited active nodes term

/-- Install the unbounded source decisions when an unfolding rank is available. -/
def guardedTotal (read : Read Node) (ranking : UnfoldingRank read)
    (ops : Operations Node Symbol) : Operations Node Symbol :=
  { ops with blocked := fun nodes paths => paths.any fun path =>
      match path with
      | [] => false
      | index :: rest => ((nodes[index]?).map (total read ranking rest)).getD false }

/-- The ranked unbounded source pass preserves the constrained language under
the same primitive graph laws as the instrumented pass. -/
theorem total_pass_exact [DecidableEq Node] (read : Read Node) (ranking : UnfoldingRank read)
    (ops : Operations Node Symbol) (laws : Laws ops) (localClasses inherited : Constraints)
    (active : Active localClasses) (nodes : List Node) (term : Term Symbol) :
    (Forest ops (pass (guardedTotal read ranking ops) localClasses inherited nodes) term ∧
      Satisfies term localClasses ∧ Satisfies term inherited) ↔
    Forest ops nodes term ∧ Satisfies term localClasses ∧ Satisfies term inherited := by
  have retained : Laws (guardedTotal read ranking ops) :=
    { empty := laws.empty, intersect := laws.intersect, project := laws.project,
      require_narrow := laws.require_narrow, require_keep := laws.require_keep,
      edit_narrow := laws.edit_narrow, edit_keep := laws.edit_keep,
      contradiction := laws.contradiction }
  exact constrained_pass_exact (guardedTotal read ranking ops) retained
    localClasses inherited active nodes term

/-- The fixture separates closed recursion, constrained recursion, free
references, and a same-path unfolding. -/
def fixture : Read Nat where
  view
    | 0 | 1 | 4 => .binder
    | 2 => .branches [[0]]
    | 3 => .reference
    | _ => .union
  nested _ := 1
  free
    | 3 | 4 => [7]
    | _ => []
  unconstrained node := node != 1
  unfold _ := 3

/-- The current gate clears cases that the previous barrier blocked. Open
unfolding can require more than one step even at an empty path. -/
theorem fixture_cases :
    nodeMeets fixture 1 [] 0 = some false ∧
    nodeMeets fixture 1 [9] 0 = some false ∧
    nodeMeets fixture 1 [] 1 = some true ∧
    nodeMeets fixture 1 [] 2 = some false ∧
    nodeMeets fixture 1 [] 4 = none ∧
    nodeMeets fixture 2 [] 4 = some true ∧
    RecursiveReductionBarrier.nodeMeets fixture.toRead [] 0 = true ∧
    RecursiveReductionBarrier.nodeMeets fixture.toRead [] 2 = true := by decide +kernel

end MicroCFTA.ConstrainedRecursionGate
