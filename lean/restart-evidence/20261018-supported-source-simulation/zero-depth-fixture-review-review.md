# Independent review of the zero-depth reader fixture

Reviewed at 2026-10-18 14:05 CEST. This review uses existing checked receipts. It runs no Lean job and adds no proof pair.

## Result

No material issue was found. The fixture proves actual source construction, an initially cold closed Mu, two retained open zero-depth values, and actual preparation at a different heap. The final reader supports both open values and settles their closed recursive child.

## Exact source and receipts

- Fixture: `zero-depth-support-kernels.lean`, SHA256 `99cd60b84777683b4deaca8864e8f08543a46593baea34cd73bfdb799b0c1ee3`.
- Production dependency: `SourceCurrentZeroDepthReaderSupport.lean`, SHA256 `5f09e107b1d1acb269e72a4fb3c5456145cc8dfe0454fa2b2236591df00cff7f`.
- Reused strict receipt: `zero-depth-support-kernels-3`. Its exit code is zero. Its log has zero bytes. Its frozen source matches the fixture.
- Reused full printer receipt: `zero-depth-support-kernels-public-2`. Its source SHA256 is `05d815cd8947e81fbed0d4b66f2ca10bcef86ff4a951a276a221e89e7b61ea47`. It prints the exact public witness statement, proof and axioms with all eight required options. Only the three standard axioms occur.
- Both recorded inner cgroups have MemoryMax and MemoryHigh of 4294967296 bytes and MemorySwapMax of zero. Both commands use Lean 4.34.1 under the recorded 4 GiB, five-minute wrapper.

## Mathematical checks

The initial value comes from an exact `build source [] empty = .done root before` equation. The source has an outer raw binder. Its stored node body contains a union of an inner productive used binder and the outer self reference. The inner binder has a nullary row and a recursive unary row. The source therefore provides the closed recursive Mu together with an open ordinary body and an open union.

Initial Ready comes from the actual constructed-source theorem. `build_verified` supplies root availability. Exact child lookups and Available.children then supply body, union and recursive-child availability. Pattern-match defaults do not enter as assumed source data. The concrete source and the checked computations determine these values.

The witness proves that the body and union each have nonempty free-name lists and stored-plan binder depth zero. It separately proves that the recursive child is closed. Initial coldness is an execution fact: an assumed effect-free unfold would keep the node allocation counter unchanged, whereas the actual computed unfold changes that counter. The proof does not use an observation difference to infer allocation.

`SourceCurrentZeroDepthReaderSupport.prepare before ready` constructs the actual Preparation and Keeps receipts. Its final WarmSupport settles the retained recursive child at exactly the final heap. Keeps retains both open values there. If the two heaps were equal, the final settled call would contradict established initial coldness. The final heap difference is thus derived.

The public witness is an exact statement alias to the checked private witness. The full printer snapshot includes the complete fixture before the printer directives. The verifier checks this exact prefix relation and checks every printed declaration and axiom report.

## Scope

This is one reused constructed pair. This review owns zero public or constructed pairs and runs zero new Lean checks. It does not claim that every open Mu has zero-depth support. It does not compare observations at the cold and prepared readers. It does not prove retained-used-Mu callback correspondence or general outer completion. Existing reader-zero-review files remain unchanged.
