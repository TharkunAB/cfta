# Actual recursive reader control

Validated on 2026-10-17T08:54:47+02:00 with Lean 4.34.1. Production SHA: `11b325bf91fd152ac65c6c3d7dab35ffbd5cb4d44e54551dc1cc750795e15d39`.

`Config` retains the complete constructor heap, visited identities, and literal pending values. The six `Step` constructors match the repaired collector successors. Fresh unions prepend their actual members. Fresh Mu steps require the exact successful repaired unfold and prepend that result. Visited branches keep the complete heap. Empty pending lists have no successor. This relation does not record emitted rows; the separate consumed-reader graph carries that output.

`Good` retains semantic and physical readback, the fixed Mu-degree bound, and availability and closedness for every pending value. `Step.good` derives these facts after actual unfolding. It uses the same unfold result to derive lower allocation degrees, closed output, and availability of the original suffix in the returned heap. It does not take a future store or successful enclosing collector as an input.

`Fits q` bounds stored payload mass, both current supplies, and pending structural work. `initial_fits` derives it from the literal pending length and initial causal payload store. `Step.fits` derives the next envelope `g q = q + charge q + ceiling q + 1`. Only fresh Mu unfolding can change the heap. Its numeric bound comes from the actual all-outcome unfold resource theorem. `g_strict` and `g_mono` provide controlled growth.

`measure_le` bounds every current degree-vector coordinate by `q`. The Mu coordinates count issued node identities, so the proof needs no identity injectivity. `Step.decreases` proves strict vector decrease for each literal successor. Fresh Mu uses its actual body degree and lower-allocation theorem. Union and ordinary branches decrease structural work or retain the appropriate higher coordinates.

The imported public probe checks 23 complete axiom/signature pairs: 17 primary declarations and six literal constructors. The two imported kernels construct their own productive recursive Mu and union from empty. The Mu kernel proves actual fresh unfolding increases both supplies, then follows an ordinary pop and a visited Mu skip through the exact returned heap. The union kernel checks fresh member expansion and visited replay. Both derive initial physical facts and resource envelopes from the construction, without completed collector or desired final resource premises.

Validation: strict production attempt 4 is empty; canonical target passed 1212 jobs, with only the inherited closed-completion warning. Public probe 1 and kernel probe 4 pass without diagnostics or nonstandard axioms. Earlier failed sources and raw logs remain separate.

Scope: this component proves local successor control and decrease. It does not by itself produce an initial sufficient collector fuel. The controlled-vector path theorem and exact consumed-step graph provide the remaining composition. It introduces no support restriction to the full closed Mu/union reader and makes no new Haskell behavior claim.
