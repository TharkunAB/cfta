import MicroCFTA.InternedNestedConstruction

/-!
# Cleanup of a recursive ordinary body

This draft proves only the final cleanup equation. The actual labeled
callback shape must be derived from the same source build separately.
-/
namespace MicroCFTA.CurrentUniverseShapeReview
open Cache InternedConstructorTemplates
open InternedNestedConstruction (finish)
open InternedBinderProtocol (NodeKey)

set_option autoImplicit false

/-- A recursive ordinary body retains its Mu record during cleanup. -/
private theorem finish_recursive_node {Symbol Guard : Type}
    (entry bodyEntry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) :
    finish true (.mu entry (.node bodyEntry edges 0 [.interned entry.identity]) depth ordinary) =
      .mu entry (.node bodyEntry edges 0 [.interned entry.identity]) depth ordinary := by
  simp [finish, cleanup, Value.free, Value.referenceOf]

#print axioms finish_recursive_node

end MicroCFTA.CurrentUniverseShapeReview
