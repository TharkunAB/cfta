# Installed observer source review

Reviewed at 2026-10-24 02:19 CEST. Status: SOURCE CLEAR. The entire three installed modules were read. Each is byte-identical to its retained successful strict compiler input:

| Module | Lines | Source SHA256 | Successful input |
| --- | ---: | --- | --- |
| `EnumerationObservations` | 105 | `ebc891e8461c7b545d55f6823322789f19635e2d1c58a5551307b621079ba0ab` | `primitive-check-1/checked.lean` |
| `EnumerationNodeObservation` | 78 | `e1b3bad8507467a7928940ac59412275599c3ae3321313f5839c5278c95fb47e` | `node-check-1/checked.lean` |
| `EnumerationPartialObservation` | 87 | `a59184eea5e21214ab912d77a5d75d014f60f72aa0d83a6c6dac0ea072e76640` | `partial-frame-check-2/checked.lean` |

All three retained strict reports have exit zero, literal-empty logs, `warningAsError=true`, and `linter.all=true`. Their recorded source/raw hashes match the files. The focused observer build report and complete 169-byte log record exit zero and 23 jobs. These are inspected existing receipts, not jobs run by the reviewer.

The primitive and node conclusions remain those of `primitive-review-1.md` and corrected `node-review-2.md`. The latter changes only the author attribution sentence; `node-review-1.md` remains unchanged. Arity authored the node candidate; Root read and installed the exact checked bytes.

The partial module proves two facts: an actual successful partial render preserves the complete compression frame under input totality, and larger fuel retains its exact successful term and final state. The node branch threads the actual ordered child traversal through `mapM_invariant`, carrying totality with each frame. The hole branch uses the actual value read; it recurses only into an enumerated payload. Pending recursive nodes truncate only when their suspended list is empty. Other pending and eliminated slots retain the original queried hole ID. Both ancestry fields remain in the frame. The fuel proof uses the existing value-read extension and ordered `retains_mapM`; it does not replace the partial renderer with the completed renderer.

The actual `EnumerationState.expandPartial` definition and Haskell `expandPartialTermFrag` branch structure were reread. The current module does not yet prove equal partial outputs from independently framed inputs or construct a finite counterpart partial render. Those results remain proposed work. It also does not prove arbitrary callback congruence or native representation/error equivalence. The earlier `partial-frame-check-1` syntax/application failure remains retained; check 2 succeeds without a semantic premise change.

Compiled public readback is pending at this review cut. No public-type or Audit result is claimed here. No compiler, selected program, Git mutation, network operation, or repository edit was performed.
