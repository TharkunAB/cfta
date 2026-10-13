import MicroCFTA.EqualityLeafProjectionRuntimeForest

/-!
# Exact source setChildren shortcut for equality workers

The source directly interns replacements with unchanged child arity. The
checked constructor runs only when arity changes. Actual edit and require
child traces preserve arity, so their ancestor requests use the direct
branch and retain the original full constraint.
-/
namespace MicroCFTA.EqualityLeafProjectionSetChildren
open InternedConstructorTemplates
open EqualityLeafProjectionSyntax (Path)
open EqualityLeafProjectionWorkers EqualityLeafProjectionPhysical

/-- Copy the source equal-arity shortcut while leaving the unused checked branch explicit. -/
def setChildren (checked : Symbol → List (Value Symbol Guard) → Guard → Work Symbol Guard (EdgeValue Symbol Guard))
    (edge : EdgeValue Symbol Guard) (children : List (Value Symbol Guard)) : Work Symbol Guard (EdgeValue Symbol Guard) :=
  if children.length = edge.children.length then
    makeEdge edge.entry.key.symbol edge.entry.key.constraint children
  else checked edge.entry.key.symbol children edge.entry.key.constraint

/-- The direct source branch retains the exact symbol and full constraint without normalization. -/
theorem same_arity
    (checked : Symbol → List (Value Symbol Guard) → Guard → Work Symbol Guard (EdgeValue Symbol Guard))
    (edge : EdgeValue Symbol Guard) (children : List (Value Symbol Guard)) (same : children.length = edge.children.length) :
    setChildren checked edge children = makeEdge edge.entry.key.symbol edge.entry.key.constraint children := by
  simp only [setChildren, same, ↓reduceIte]

/-- Every successful actual ordinary child-edit trace retains the original arity. -/
theorem editChildren_length [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edits : List (Path × Target)) (index : Nat) (children results : List (Value Symbol Guard))
    (ordinary : OrdinaryChildren children) (state : State Symbol Guard) (valid : Valid state)
    (returned : (run (editChildren meet edits index children) state).1 = some results) : results.length = children.length := by
  have readback := EqualityLeafProjectionWorkerReadback.editChildren_readback meet edits index children ordinary
    state (run (editChildren meet edits index children) state).2 valid (grows_refl _)
  have same := Option.some.inj (returned.symm.trans readback)
  rw [same, mapChildren_length]

/-- Required-path child traversal also retains positions; parent filtering removes whole rows. -/
theorem requireChildren_length [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (index : Nat) (children results : List (Value Symbol Guard))
    (ordinary : OrdinaryChildren children) (state : State Symbol Guard) (valid : Valid state)
    (returned : (run (requireChildren paths index children) state).1 = some results) : results.length = children.length := by
  have readback := EqualityLeafProjectionWorkerReadback.requireChildren_readback paths index children ordinary
    state (run (requireChildren paths index children) state).2 valid (grows_refl _)
  have same := Option.some.inj (returned.symm.trans readback)
  rw [same, mapChildren_length]

/-- The actual selected edit continuation equals source setChildren for every checked fallback. -/
theorem edited_constructor [DecidableEq (EdgeKey Symbol Guard)]
    (checked : Symbol → List (Value Symbol Guard) → Guard → Work Symbol Guard (EdgeValue Symbol Guard))
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edits : List (Path × Target)) (edge : EdgeValue Symbol Guard) (results : List (Value Symbol Guard))
    (ordinary : OrdinaryChildren edge.children) (state : State Symbol Guard) (valid : Valid state)
    (returned : (run (editChildren meet edits 0 edge.children) state).1 = some results) :
    setChildren checked edge results = makeEdge edge.entry.key.symbol edge.entry.key.constraint results :=
  same_arity checked edge results (editChildren_length meet edits 0 edge.children results ordinary state valid returned)

/-- The actual surviving require continuation equals source setChildren for every checked fallback. -/
theorem required_constructor [DecidableEq (EdgeKey Symbol Guard)]
    (checked : Symbol → List (Value Symbol Guard) → Guard → Work Symbol Guard (EdgeValue Symbol Guard))
    (paths : List Path) (edge : EdgeValue Symbol Guard) (results : List (Value Symbol Guard))
    (ordinary : OrdinaryChildren edge.children) (state : State Symbol Guard) (valid : Valid state)
    (returned : (run (requireChildren paths 0 edge.children) state).1 = some results) :
    setChildren checked edge results = makeEdge edge.entry.key.symbol edge.entry.key.constraint results :=
  same_arity checked edge results (requireChildren_length paths 0 edge.children results ordinary state valid returned)

end MicroCFTA.EqualityLeafProjectionSetChildren
