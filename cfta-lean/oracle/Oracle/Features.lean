import Lean
import Oracle.Erase
import Oracle.Walk
import Oracle.States

/-!
# Features of a query, read before the search

Three features of a query predict which mode solves it; the GHC host reads
the same three, so that the two hosts' results line up:

* **a higher-kinded variable**: the query, or a leaf that fits the goal,
  binds a variable whose type is a type former, as `m : Type → Type` or the
  `f` of `Functor.map`. Erasure gives such a leaf no first-order type.
* **a class over a type constructor**: the query, or a leaf that fits the
  goal, has an instance binder whose class is applied to a type former, as
  `[Monad m]` or the `[Functor f]` of `Functor.map`.
* **child goals that stay open**: a leaf that fits the goal leaves a child
  goal whose type is a bare metavariable, as `Ord.compare` at `Ordering` or
  `HAdd.hAdd` at `α`. Such a child is a state of every type in the search
  over states.

A leaf fits the goal when its refinement step on a fresh goal of the goal
type succeeds, for a number of children below the bound; the candidates come
from the index of the leaves (`Oracle.States`). The features also count the
leaves that fit, and those of them that have no erased type, which mode (a)
cannot propose.
-/

namespace Oracle

open Lean Meta

/-- The features of a query. -/
structure Features where
  /-- The query or a leaf that fits binds a higher-kinded variable. -/
  higherKinded : Bool := false
  /-- The query or a leaf that fits has an instance of a class over a type constructor. -/
  classOverConstructor : Bool := false
  /-- The leaves that fit and leave a child goal of a bare metavariable. -/
  openChildren : Nat := 0
  /-- The leaves that fit the goal, with a number of children. -/
  fitting : Nat := 0
  /-- The leaves that fit and have no erased type. -/
  withoutErasure : Nat := 0

/-- Whether a type is a type former: a universe after one or more binders. -/
def isTypeFormer (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun binders body => return !binders.isEmpty && (← isUniverse body)

/-- Whether a type binds a higher-kinded variable among its binders. -/
def bindsHigherKinded (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun binders _ => binders.anyM fun binder => do isTypeFormer (← inferType binder)

/-- Whether an instance binder of a type has a class applied to a type former. -/
def bindsClassOverConstructor (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun binders _ => binders.anyM fun binder => do
    let decl ← binder.fvarId!.getDecl
    if !decl.binderInfo.isInstImplicit then return false
    decl.type.getAppArgs.anyM fun argument => do isTypeFormer (← inferType argument)

/-- The features of the walk's goal in the local context of the query, for
programs up to the bound. No assignment stays. -/
def features (bound : Nat) : WalkM Features := do
  let w ← get
  let saved ← Meta.saveState
  -- The query: its locals, as `m : Type → Type` and `[Monad m]`.
  let mut result : Features := {}
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if ← isTypeFormer decl.type then result := { result with higherKinded := true }
    if (← isClass? decl.type).isSome then
      if ← decl.type.getAppArgs.anyM fun argument => do isTypeFormer (← inferType argument) then
        result := { result with classOverConstructor := true }
  let (trees, _) ← buildIndex w.stateLeaves bound
  let erased : NameSet := w.leaves.foldl (fun names leaf => names.insert leaf.name) {}
  for children in [0:bound] do
    let some tree := trees[children]? | continue
    for index in ← tree.getUnify w.goalType do
      let some leaf := w.stateLeaves[index]? | continue
      let before ← Meta.saveState
      let goal ← mkFreshExprMVar w.goalType
      let stepped ← tryCatch (step { goals := [goal.mvarId!], pending := [] } leaf children) fun _ => pure none
      if let some walker := stepped then
        let type ← inferType (← leaf.instantiate)
        let higher ← bindsHigherKinded type
        let classOver ← bindsClassOverConstructor type
        let bare ← walker.goals.anyM fun child => do return (← instantiateMVars (← child.getType)).isMVar
        result := { result with
          fitting := result.fitting + 1,
          higherKinded := result.higherKinded || higher,
          classOverConstructor := result.classOverConstructor || classOver,
          openChildren := result.openChildren + (if bare then 1 else 0),
          withoutErasure := result.withoutErasure + (if erased.contains leaf.name then 0 else 1) }
      before.restore
  saved.restore
  return result

end Oracle
