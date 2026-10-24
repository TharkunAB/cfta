# Primitive observer source review

Reviewed at 2026-10-24 02:15 CEST. Status: SOURCE CLEAR for the first compiler check. No concrete type or proof error was found. This is not a compiler result.

The entire candidate `/tmp/mcfta-observer-frame-20261024-primitives.lean.txt` was read. Its SHA256 is `ebc891e8461c7b545d55f6823322789f19635e2d1c58a5551307b621079ba0ab`. The actual file has 105 LF lines, including blank lines; the task's 111-line description does not match this count.

All five interfaces have the intended premises. They require one input frame and left totality. Right totality follows from `frame.total total`. No `Safe`, `Ready`, allocation-bound, desired-root, desired-payload, or successful-right-read premise is added to either transport theorem.

`Frame.symm` reverses all five nonforest field equalities and the complete root/size-path equivalence. Both comparison proofs compose the full after-state frame as `leftFrame.symm.trans (frame.trans rightFrame)`. Neither replaces the frame by class equivalence alone.

Representative comparison moves the actual right path into the left forest with `frame.reaches.mp`. Path uniqueness gives `leftFound.representative = rightFound.representative`. The final chain `leftRootEq.trans (same.trans rightRootEq.symm)` has the correct direction. Representative transport uses the existing actual termination theorem on the related input. Its `same.symm ▸ rightRead` converts the returned right root to the observed left root in the correct direction.

Value comparison uses the actual slot witnesses from both reads. Rewriting the right stored read by `frame.values` and `← same` puts it at the observed left slot. The `Option.some.inj` chain proves left payload equals right payload. No equality instance on `Symbol` is required.

Value transport obtains readability from the actual successful left read. It transfers that read's path with `frame.reaches.mpr`, constructs an actual finite right lookup with `findRoot_terminates`, and identifies its root with `reaches_unique`. The right slot rewrite uses `frame.values` and `same` in the correct direction. The constructed `rightAfter` is the exact right state with only the observed forest replaced. `getValue_success.mpr` establishes the right read before the paired comparison supplies the final frame. Independent finite fuel is produced; equal fuel is not claimed.

The exact live APIs were reread: `Frame`/`Frame.trans`/`Frame.total`, `representative_frame`, `getValue_frame`, `representative_success`, `representative_terminates`, `getValue_success`, `reaches_unique`, and `findRoot_terminates`. Their source identities remain:

- `EnumerationCompressionFrame.lean`: `5b6e6a4b11c21b949874db500e23aa074fcdd4e0de683f46f33863113dc91375`.
- `EnumerationExecution.lean`: `b81e03600e03085ec32fc8c85026ca4af562593764b28d6f8dd776eb3ac98346`.
- `EnumerationSchedule.lean`: `3e84f2059725b3c0392d4df005574fde2918290cb393c4be0d549a62ad4a4e45`.
- `EnumerationCorrectness.lean`: `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d`.
- `UnionFind.lean`: `3668867a41890e4721c301092a06c48d3bd757a8eede4b92340fe5db80119a14`.

These theorems compare the two modeled primitive reads and construct matching finite successes. They do not claim congruence of arbitrary callbacks or equal raw representative forests. Root authored the candidate. The reviewer authored only the preceding route proposal and this review. No compiler, prepared tool, Git mutation, network operation, or repository edit was performed.
