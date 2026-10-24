# Root-fragment observer source review

Reviewed at 2026-10-24 02:29 CEST. Status: SOURCE CLEAR for the first compiler check. No concrete type, proof, fuel, or projection error was found. The complete 93-line Root-authored candidate was read: `/tmp/mcfta-partial-congruence-20261024-root-read.lean.txt`, SHA256 `b07912ebad2d4d12e7f540a32519b1aff7d3bd387e98db2745a5f00bc8a0c25c`.

The candidate uses the existing `EnumerationUntil.rootFragment`; it introduces no alternative worker. That action reads variable zero through `getValue (fuel + 1) 0`, returns the exact stored fragment when enumerated, and otherwise returns the original `.hole 0`. This matches the branch structure of Haskell `rootTermFrag` at `Enumeration.hs:1018–1026`. It does not replace the original root hole with the current representative ID. The eager truncated, stop-aware partial, and ordered partial routes all use `rootTermFrag >>= expandPartialTermFrag`; those actual call sites were read at lines 1080–1093, 1180–1193, and 1478–1480.

`rootFragment_success` correctly inverts the value read and pure continuation. Every branch retains the same final state, and its equality direction is `fragment = projectedValue`. Both directions use the existing `success_bind` and `success_pure` interfaces correctly. The frame theorem reuses the actual read frame at `fuel + 1`. The paired theorem allows independent root fuels and supplies those two incremented bounds to `getValue_agrees`, preserving the complete final frame.

Finite transport has the required offset. `getValue_transport` constructs an actual right value read at `readFuel`. The candidate extends that exact read by one with `getValue_moreFuel readFuel 1 0`, retains its exact final state, and chooses the root action's fuel to be `readFuel`. The resulting root action therefore reads at `readFuel + 1`, exactly as `rootFragment_success` requires. It does not subtract fuel or assume an unavailable same-bound read.

Readability comes from the supplied successful left observation. No `Safe`, `Ready`, target slot, desired fragment, or successful-right-observation premise is introduced. Right totality is inherited through the existing value transport. `rootFragment_moreFuel` rearranges `(fuel + 1) + extra` to `(fuel + extra) + 1` and retains both the exact projected fragment and the exact final state. The explicitly named local instance `rootObservationMonadList` is distinct from the installed node and partial observer instance names.

This is a modeled root-read result. It does not prove partial-render transport, arbitrary callback congruence, a shared-driver simulation, native node/container representation correspondence, or equality of native errors. It makes no equal-fuel claim across different forests and does not equate raw representative forests.

Live definitions and API cuts reread for this review: `EnumerationUntil.lean:135–152`, Haskell routes listed above, `EnumerationExecution.lean:99–111`, and the exact `success_bind`/`success_pure` signatures. The previously reviewed primitive observer source remains byte-identical. Input identities:

- `EnumerationObservations.lean`: `ebc891e8461c7b545d55f6823322789f19635e2d1c58a5551307b621079ba0ab`.
- `EnumerationUntil.lean`: `3d54b3a6ca3db0c668f6b8910c62adcae099f3eae79cfb6d82ee9176710fd137`.
- `EnumerationExecution.lean`: `b81e03600e03085ec32fc8c85026ca4af562593764b28d6f8dd776eb3ac98346`.
- `EnumerationCorrectness.lean`: `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d`.
- `cfta/src/Data/CFTA/Enumeration.hs`: `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07`.

Only this review was written. No compiler, prepared program, Git mutation, network operation, or repository edit was performed.
