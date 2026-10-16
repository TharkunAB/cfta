# Independent constructed-root review

Reviewed at 2026-10-16 15:06 CEST. No material defect found.

The reviewed initialization source has SHA256 `83bae4390352d9a40cc16c3258d63d0443c161e85177f026ed480c2443652eff`.
The reviewed root source has SHA256 `0038bc1a619bbcd4288b689b598091669514ded818f5bd58805d5dddb4aafd39`.

## Source entry and physical initialization

`cfta/src/Data/CFTA/Equality/Operations.hs:68–70` starts `reducePartially` with `EmptyConstraints`. This is an equality value. `Equality/Constraint.hs:273–286,313–314` constructs it with the equality interner and an empty class list. It is distinct from `Constraint.hs:205`, where `noConstraint` is a full guard with empty equalities and `Top`.

`PartialInitialization.emptyValue/operations/checked/caller` at lines 28–42 retain the actual result of interning the empty equality key. An existing canonical identity can be nonzero. The checked heap stays equal to the constructed heap. The equality cache uses the returned interner. This allocation does not construct a full guard or execute an edge constructor. Initial loaded original fields grow through this allocation at lines 119–124. The initialization checks owned by required_memos include an actual valid warm cache whose empty key has identity 37.

The initial context at lines 128–137 derives all eight fields: `ready`, `admitted`, `sound`, `stored`, `covered`, `correct`, `globals`, and `probes`. `inventory` at lines 65–87 computes the source facts and roots `[value]` from the actual completed closed build. It does not assume a semantic model or cache admission oracle. The native node/edge tables, native domain cache, equality operation tables, outer node/edge result tables, merge-result memo, fourth emptiness memo, and three global memo families keep their separate types and state locations.

These definitions select a logical cold state after construction. They do not prove that Haskell clears any process-global cache. Haskell's equality interner and outer reduction memo are global values (`Equality/Constraint.hs:280–286`, `Equality/Operations.hs:72–81`). Construction history and guard coverage remain explicit. The proofs do not equate their serial preparation order with GHC field forcing or publication.

## Root endpoints

`PartialConstructedRoot.constructed_root` at lines 31–60 derives the context, canonical empty inherited value, and root availability from covered construction. Its public premises contain no supplied `Context`, `At`, semantic model, cache soundness law, completed caller graph, strict-read certificate, or final state invariant. It still requires an actual completed fresh build, legitimate allocation history and initial cache validity, reached machine checks, and literal worker success. These are not general caller termination premises disguised as finite completion.

The exact supplied `result` and whole returned `after` appear in the constructed graph, strict reads, physical `Post`, availability, and language equivalence. The proof substitutes only the derived empty-equality readback. It does not replace the caller return with another existential execution.

`prepared_root` at lines 63–102 runs actual `prepare` on the expression's guard occurrences. Its literal ranges and success use `prepare(...).2`. It derives the preparation receipt and history, then uses that same cache in the root endpoint. `Cached` on original fields remains an explicit domain condition. The theorem does not replace normalization or construction with the desired language result.

General constrained termination, exclusion of busy observations for arbitrary callers, source host-container correspondence, native machine identities, GHC demand order, global memo initialization, and frontend coverage remain separate obligations. The zero-bound empty-root check below proves one concrete terminal case only.

## Independent imported checks

Both public endpoints passed full explicit signature and axiom checks. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Four imported integration kernels passed with no warnings:

1. Covered construction plus supplied literal success derives its own strict reads, checks, full same-return `Post`, computed admission, probe heap, final global/fourth validity, merge/fourth retention, and language equivalence.
2. Actual preparation retains all prior canonical entries and returns its own receipt at the exact cache used by the root call.
3. A second literal root call consumes the first computed inventory and full warm context. Only its own reached ranges and success are additional inputs. The physical histories and language equivalences compose.
4. A literal empty root completes with every execution bound and the conjunction budget equal to zero. The only initialization input is a valid equality cache, which can be warm. This kernel supplies no success or completed graph premise. It derives the exact returned cell and `Post`, unchanged checked/merge/fourth state, and the empty result language.

Exact commands and exit codes are in `root-review-validation.md` and `root-review-results.json`. Earlier failed kernel logs remain as drafts. The final imported logs contain no errors, warnings, or `sorryAx`.
