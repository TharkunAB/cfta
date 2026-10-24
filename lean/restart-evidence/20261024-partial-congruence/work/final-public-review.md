# Final partial-observation public review

Reviewed at 2026-10-24 02:35 CEST. Status: CLEAR. No concrete public-statement, installed-source, or axiom mismatch was found. The entire 125-line, 9,229-byte public output was read without truncation, together with its complete command input and report.

`public-1/raw.log` SHA256 is `95358c4e54a5c874a9331c506c95b263879a206d9b8892145a7f6985864b4820`. All 11 checked signatures match the command input in order. All 11 printed axiom sets match those theorem names and contain exactly `propext` and `Quot.sound` after universe-suffix normalization. No additional axiom occurs. The public run has exit zero with strict warning and linter flags.

All four final installed modules are byte-identical to their successful strict inputs. Each strict report records exit zero and a literal-empty log under `warningAsError=true` and `linter.all=true`:

| Module | Lines | SHA256 | Strict input |
| --- | ---: | --- | --- |
| `EnumerationRootObservation` | 93 | `b07912ebad2d4d12e7f540a32519b1aff7d3bd387e98db2745a5f00bc8a0c25c` | `root-read-check-1/checked.lean` |
| `EnumerationPartialCongruence` | 141 | `7452999a98756fdb92be845b4eb52f08926c5a12ce9c42752df1333d457bcb60` | `paired-check-2/checked.lean` |
| `EnumerationPartialTransport` | 155 | `cfb86bcdf59c125625bb78f0fea7da467789adc162f27c4f1a4e45f630b5674c` | `transport-check-3/checked.lean` |
| `EnumerationPartialRoot` | 78 | `c9e3221bfb1d3793c3dfef427468809f440239c5be0bfdd4ebfe3b306d77bd3d` | `root-render-check-1/checked.lean` |

The checked root inversion uses `getValue (fuel + 1) 0`, returns the exact enumerated stored fragment, and otherwise retains the original `.hole 0`. Paired root and partial comparison statements permit independent fuels and require the input frame, left totality, and the two actual observations. They return actual output equality and the complete final frame.

All three transport statements require only one actual successful left observation, the input frame, and left totality. They construct finite right observations and their final frames. No desired-right-success, desired-output, extra readable-slot, `Safe`, `Ready`, completed-state, or semantic-oracle premise occurs. The actual left observation supplies the required readability.

The root/render conclusions use the literal existing bind, not a new worker: `rootFragment fuel >>= expandPartial graph fuel`. Within each execution both components receive the same outer bound; left and right executions can have independent bounds. The root-read convention still adds one internally. The transport proof's common right bound is `rootFuel + renderFuel`. Existing fuel-extension results preserve its exact constructed root-read intermediate state and render final state before those actions are bound together.

Every final relation remains the complete installed frame, including both ancestry fields and every root/size-path equivalence. Hole labels remain the original queried IDs. Truncation remains restricted to the recursive view with empty suspended constraints. These statements do not claim equal forests, equal-bound behavior across different forests, error-list equality, unconditional rendering termination, arbitrary callback congruence, a complete shared-driver simulation, native representation correspondence, or resource bounds.

Three actual failed attempts remain retained and were correlated with their checked source/report/raw hashes:

- `paired-check-1`, exit 1: the local `LawfulMonad List` instance was missing for `List.mapM_cons`. Raw SHA256 `2f2c385cfd4524e73519837a23d14dd307a5388b5eb0ca18156eb1940d285c6a`. The successful second input adds only the previously reviewed 17-line existing law proof.
- `transport-check-1`, exit 1: two state names had already been eliminated by actual pure-success equalities, and two dotted `node` constructors were ambiguous. Raw SHA256 `cbfd5964c6373878802d06cef2aff05e1773edb3133c51557e3e4091aba8c47e`.
- `transport-check-2`, exit 1: only the two dotted-constructor ambiguities remained. Raw SHA256 `76e01cab7cb7acde105ab8b1a8370a4845a71bd7aa113c74ce9072e473c565de`. Version 3 qualifies the constructors and passes. The repair changes no theorem premise, state transition, bound, or branch.

The complete actual `audit-1` log and report were read. Exit is zero, with 3,671 jobs and 75,775 checked theorem dependencies. Its 679-byte log SHA256 is `dcf57b8c3eefb0a71d643985dee8fb269b7e27f35012a7d09b4f4537611b41c6`. Its only warning is the known older unused-`inputs` warning at `InternedFreshOrdinaryClosedCompletion.lean:24:5`; no new module warning appears.

Additional exact input identities:

- `public-1/checked.lean`: `03637f00f4094f233299ade6127c0e8a0802dfd77596a9d3f65413e8bd1bc8f0`.
- `public-1/report.json`: `829dadab0c6903744ab7f47121a0beb92d77fcfefe755ee09973c25839c9a2ae`.
- `audit-1/report.json`: `e8bf453c61ff5ccc0d08e89d080e6ca505f5c1e033f858b836b0aff21e8a4254`.
- Independent full transport review `transport-review-3.md`: `80ec4d65df4489431158a3f15ae9c118c65d5c97385fe5abcfa9e749eb785718`.

This reviewer previously read the complete root-read, paired, and root/render composition sources and their exact dependencies. Their identities are unchanged. For transport, this pass read its complete independent review, exact public signature, both failed logs, successful record, and installed/checked identity; it does not claim another independent manual read of its entire 155-line body. All public output and the actual Audit were read in full. No compiler, prepared program, Git mutation, network operation, or repository edit was performed.
