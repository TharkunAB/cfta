# Target and shared initial forecast monotonicity review

Reviewed on 2026-10-17 at 11:11 CEST. TargetMonotone is frozen at `34b08b43d798acfdcf53f89b2ccc56a9feeac771a751aea59e6fd6e6357a34dc`. SharedMonotone is frozen at `e3ea3a012020de1d082b1b959372294de1808677818b4d63ff875a03fbb8e569`. Both final strict logs are empty. Their canonical targets passed 1515 and 1517 jobs.

The raw Merge bound was monotone in its scalar argument but lacked a height comparison. The new proof first shows bound(height,value) <= bound(height+1,value). At height zero, the existing bound_ge proves this. At positive height, pointwise larger child bounds retain each literal iteration. Existing step_mono and iterate_compare justify that comparison. Induction then proves arbitrary height monotonicity. Combining height and scalar comparisons gives the diagonal scalar-only workFuel monotonicity.

The Merge selection comparison uses the existing monotone heap ceiling and diagonal row-read fuel. It then compares the finite pair term and sum directly. Projection scalar monotonicity follows the literal forestBound branches: root unions use unionGrowth_mono; proper paths use the fixed tail-length bound_mono. Thus Operand work, read, and selection allowances increase with the initial scalar.

The Target proofs retain the source schedule. An Operand preserves its domain component and increases its three constructor components. A Fold applies its head Operand before the tail and its final native forecast step. The recursive monotonicity proof follows this order. Whole Target includes the unchanged empty branch. The fuel proofs use the same profiles and maxima as the original functions.

Reservation weakening has the downward direction: reservations for a larger initial profile imply reservations for a smaller initial profile. Every reached query-entry profile is ordered by the Fold proof. Existing Room.mono transfers the larger room test to the smaller entry. No actual execution, reached state, profile agreement, or future result is assumed.

The Shared module proves both fixed-branch monotonicity and domination by an all-miss schedule. A Force hit keeps the original profile and uses zero fuel. The miss forecast retains its initial profile. Thus either found value fits the miss forecast. A Leaf then applies the existing monotone query forecast. Force and Leaf fuel and reservation comparisons follow these same branch cases. The found argument is an arbitrary initial Boolean, not an assumed future warm-slot outcome.

forceReserved_of_final_room derives every Target reservation from room at the all-miss Force return. leafReserved_of_final_room moves a room test at the all-miss final Leaf profile back to the Force return, then supplies both the earlier Target schedule and the final query. These helpers are arithmetic sufficient conditions. They introduce no completed-call or callback oracle.

The forest count and signed path schedule remain fixed in these statements. Initial profile components may all increase. No theorem here asserts monotonicity under an arbitrary change of path schedule or count. The actual editor producer must use the same captured count or prove a separate count comparison if it changes that parameter.

Imported validation has 26 full axiom/signature pairs: 12 Target and 14 Shared. The two pure schedule kernels keep every large bound symbolic. three_leaf_schedule composes three arbitrary hit/miss choices, proves their complete profile and fuel bounds, and derives every initial Leaf reservation from one final all-miss room test. rotated_target uses literal paths [[1],[2],[0]] and explicit small component profiles. It checks profile and fuel order and reservation weakening. Only the four small input comparisons are computed; no huge forecast is evaluated.

All final probe logs have no diagnostics and use only standard axioms. All failed source attempts and raw logs are retained. These pure prerequisites do not claim actual editor execution, general selected recursive convergence, or host forcing correspondence. No older production source or evidence was edited.
