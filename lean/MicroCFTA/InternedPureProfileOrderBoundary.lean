import MicroCFTA.InternedPureProfileIdentity
import MicroCFTA.InternedProfileSemantics

/-!
# Two probe aliases prevent exact ordered syntax profiles

Both captured names can equal the source probe sentinels. Reversing
their order then leaves the normalized probe pair unchanged. A cache
hit returns the order from the first completed body. Thus the pure
syntax interpreter describes reference membership, not exact order.
-/
namespace MicroCFTA.InternedPureProfileOrderBoundary
open InternedConstructorTemplates InternedNestedConstruction InternedRootProfile
open InternedBinderProtocol (Reference)

/-- A warm source hit retains the first body's order when both captured probe aliases are reversed. -/
theorem warm_cache_retains_first_order :
    let first : Syntax Unit Unit := .binder true (.union [.var 1, .var 2])
    let second : Syntax Unit Unit := .binder true (.union [.var 2, .var 1])
    let environment : List (Value Unit Unit) := [.reference .depth, .reference (.uninterned 0)]
    match build first environment empty with
    | .pending _ _ => False
    | .done initial state =>
        match build second environment state with
        | .pending _ _ => False
        | .done actual _ =>
            profile initial = some [.depth, .uninterned 0] ∧
            profile actual = some [.depth, .uninterned 0] ∧
            initial.referenceOf = actual.referenceOf ∧
            InternedProfileSemantics.evaluate second (environment.map profile) = some [.uninterned 0, .depth] := by
  cbv

end MicroCFTA.InternedPureProfileOrderBoundary
