# Current Region input validation

Validated at 2026-10-16 15:28 CEST with pinned Lean `leanprover/lean4:v4.34.1`.

Source: `lean/MicroCFTA/SourceCurrentAllocatedPartialPlainInputs.lean`, 150 lines.

SHA256: `d9b94b6cea1374c82b2b65bb4efad01328cd85106bec80e16a3db3da01917065`.

## Derived input facts

`own_empty` inverts the literal physical reader and `recordsOf`. A successful empty physical own payload implies an empty effective source equality list. It needs no normalization, model, execution, or cache premise. A nonempty input class list either fails physical construction or constructs a nonempty record list.

`rows_member` and `children_member` read the pure structural Region predicate. Each selected original row has an empty effective accessor and its exact child Regions. No historical execution theorem is used.

`node_evaluate` and `edge_evaluate` consume the actual current begin/evaluate observation. Initial `Sound`, canonical heap coherence, candidate inherited readiness, and candidate availability or edge residency derive the exact stored owner's input facts. Publication retains the checked state. Equal actual keys and coherent resident readback identify the complete immutable owner value with the candidate value. This transfers the Region or row facts.

These conclusions identify values, not complete requests. They do not assert equality of inherited payload metadata. The actual key and existing allocated readiness continue to govern inherited identity transport.

`edge_ready_shape` reconstructs the actual returned owner from the initial table and ready observation. The initial structural key link and resident edge identity identify the owner's value with the candidate's value. The initial `ReturnedDomain.Stored` invariant then supplies the shape for that exact existing returned cell. The entire reached caller equals the initial caller. No future body result or final-cache invariant is supplied.

The warm structural `Stored` invariant remains explicit. This module does not derive it for arbitrary constrained result histories. The separate returned-domain lifecycle and concrete empty-own parent proof supply that obligation in the intended Region completion.

## Checks

- `inputs-direct-2.log`: exit 0, no warnings or errors.
- `inputs-build-1.log`: root-managed canonical success, 1404 jobs. Only the historical unused `inputs` dependency warning remains.
- `inputs-probes-1.log`: external imported-olean check, exit 0, no warnings or errors.
- Six public theorem axiom reports and full signatures pass.
- Five integration kernel axiom reports and full signatures pass.
- All eleven final reports contain no `sorryAx`. Their axiom union is the standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

The first direct log records a dependent case simplification error, a shape transport error, and three unused section-instance warnings. These were corrected before the source freeze. That failed log remains available.

## Integration kernels

1. Empty physical own readback is equivalent to an empty effective source equality list.
2. An original Region row and initial current residency derive full parent finite ranges and every original child Region, without a supplied range plan.
3. An actual node begin/evaluate transfers the candidate Region and the exact node rank to the stored owner.
4. An actual edge begin/evaluate transfers row equality freedom, child Regions, and the exact edge rank to the stored owner.
5. An actual ready edge hit retains the entire caller. Each returned child has a Region and a node rank strictly below the candidate edge rank, derived from its actual stored shape.

## Scope

All source model inputs are initial facts or actual prefix observations. There is no assumed same-parent semantic law, completed recursive callback, future Region, future cache validity, or completed caller in these proofs. Original guards and ordered child values are retained by complete value equality.

This module supplies inputs for the pending finite current Region induction. It does not prove general outer progress, constrained returned-domain preservation, GHC demand order, process-global CAF initialization, or runtime publication. No Haskell source, older proof, Audit, restart authority, or Git state was edited. No Haskell run or network request occurred.
