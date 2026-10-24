# Root-read and partial-render composition review

Reviewed at 2026-10-24 02:33 CEST. Status: SOURCE CLEAR for the first compiler check. No concrete signature, proof, state-correlation, or fuel error was found. The entire 78-line Root-authored candidate was read: `/tmp/mcfta-partial-congruence-20261024-root-render.lean.txt`, SHA256 `c9e3221bfb1d3793c3dfef427468809f440239c5be0bfdd4ebfe3b306d77bd3d`.

All four public statements use the literal existing sequence `rootFragment fuel >>= expandPartial graph fuel`. No new action or alternative renderer is defined. Within each execution the root read and renderer receive the same outer bound. The two compared executions can have different bounds. The underlying root action retains its existing `fuel + 1` value-read convention.

Frame preservation decomposes the actual bind at its actual intermediate state. It transports left totality through the root-read frame before using the partial-render frame. Paired agreement first derives equality of the two actual root fragments and their intermediate frame. It then applies partial-render agreement to that same derived fragment and the two actual render continuations. No fragment-equality, desired-term, successful alternative execution, `Safe`, or extra readability premise is assumed.

`rootPartial_moreFuel` uses `retains_bind` with the existing root-read and partial-render extensions. Both actions retain the exact successful intermediate and final states. This is successful-branch inclusion, not equality of all errors or equal-bound behavior across different forests.

Finite transport first constructs an actual right root observation at `rootFuel`, ending at `rightMiddle`, with the same fragment and a frame from `leftMiddle`. The pinned `expandPartial_transport` then constructs an actual render at `renderFuel`, starting at that exact `rightMiddle` and ending at `rightAfter`, with the observed term and final frame. Its graph, fuel, fragment, input-state, final-state, term, frame, totality, and observed-success argument order matches the invocation.

The chosen common right bound is `rootFuel + renderFuel`. `rootFragment_moreFuel rootFuel renderFuel` retains the exact right root observation and `rightMiddle`. `expandPartial_moreFuel graph renderFuel rootFuel` retains the exact render and `rightAfter`; commutativity puts its bound in the chosen order. `success_bind.mpr` composes these two supplied transitions through that same `rightMiddle`. No second unrelated execution or hypothetical intermediate-state equality is used.

The final relation is the complete installed `Frame`, not raw-forest equality or class equivalence alone. Finite one-sided root/render transport is now part of this proposed result. It still does not prove arbitrary callback congruence, transport of the preceding enumeration driver, native container/representation correspondence, unconditional rendering termination, or a resource bound.

Exact component identities checked:

- `EnumerationRootObservation.lean`: `b07912ebad2d4d12e7f540a32519b1aff7d3bd387e98db2745a5f00bc8a0c25c`.
- `EnumerationPartialCongruence.lean`: `7452999a98756fdb92be845b4eb52f08926c5a12ce9c42752df1333d457bcb60`.
- `EnumerationPartialObservation.lean`: `e407fa36087e6f5521dbd2da098aa49d1fe37817f16a2c9d32227d56153e67bc`.
- `EnumerationPartialTransport.lean`: `cfb86bcdf59c125625bb78f0fea7da467789adc162f27c4f1a4e45f630b5674c`. Installed bytes equal candidate 3 and `transport-check-3/checked.lean`. The inspected strict report records exit zero and a literal-empty log.
- `EnumerationExecution.lean`: `b81e03600e03085ec32fc8c85026ca4af562593764b28d6f8dd776eb3ac98346`.

This pass read the whole new root-composition candidate, the exact component statements and `retains_bind`, and correlated the installed transport with its checked candidate 3. It does not claim an independent read of the entire transport proof body. A reviewer-only metadata helper initially expected a `target` field absent from the actual install record; checking the explicit installed path corrected that helper without any candidate or repository change. No compiler, prepared program, Git mutation, network operation, or repository edit was performed.
