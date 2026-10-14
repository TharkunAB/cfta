# Successful first native recursive intersection

Later extension: general stored support and individual unfolding now have
checked completion and closedness without preparation. See
[stored support and unfolding](notes-stored-free-unfold.md), `2ac3ca41`.
Native output closedness, repeated cold-reader termination, and physical
product rows remain open.


Updated: 2026-10-14 12:05 CEST. Proof checkpoint: `f7b842e4`.

## Semantic heaps and compiled source effects

`SourceRecursiveIntersectionSemanticHeap.SemanticHeap` retains complete source
normalization, decoded profiles, decoded free names, and decoded depths and
deep names. The actual emitted edge, node, and union operations preserve it
from available children or resident edges. Actual optional binders preserve
it from an available stored body. `constructed` derives it from an actual
repaired closed source construction. Arbitrary `Work` has no preservation law.

`SourceRecursiveIntersectionCodeSemantic.Semantic` retains primitive semantic
heap preservation and available optional-binder bodies at exact source sites.
Recursive continuations accept available returned values after valid source
growth. `semantic_bind` and `semantic_walk` use the existing physical safety
proof to retain these conditions through ordered source continuations.
`CompileSemanticCalls` and `CompileSemantic` derive the certificate for every
actual source branch, including domain entry, original binding lookup,
ordered child/row requests, unions, and optional binders.

## Actual completed native bodies

`SourceRecursiveIntersectionNativeSemantic.Bounds.semantic_heap` follows the
actual nested evaluation with checked memo keys. It uses the existing
physical correctness proof for available returned values, exact growth,
strong memo provenance, and the original completion frames. All completed
native bodies retain the semantic heap before their later continuations.
No prepared-body condition is used.

## Actual unfinished native runs

`NativeConstructorSplit.constructor_bind_cases` derives two alternatives
from an actual bounded constructor block in appended code. The body itself
blocks at a no-larger bound, or an actual completed body reaches its original
continuation, which blocks. The statement retains exact shared states,
remaining code, and finite counts.

`NativeNoConstructor.no_constructor` uses strong induction on the actual
finite native bound. Primitive operations retain the semantic heap. An
optional-binder site supplies its actual available body, complete semantic
heap, and payload coverage to the general repaired source completion proof.
Memoized starts split their actual compiled body and original completion
frame. Completed bodies derive physical provenance and retain semantic heaps
and coverage. The remaining continuation uses its actual returned value.

The theorem requires `BodyCode`, physical `Safe`, native `Valid`, compiled
`Semantic`, `SemanticHeap`, complete payload coverage, and `WordRanges` at
the initial code. The actual source compiler derives both code certificates.
The proof excludes pending constructors at every bound. It does not assume a
successful run or a supplied no-pending callback. A generic semantic invariant
for arbitrary native prefixes is not required.

## Successful finite first execution

`NativeSuccessful.cold_node_complete` combines pending-constructor exclusion
with the existing derived finite return-or-pending bound. Closed Original
available roots now have successful finite native execution in complete
semantic caches under explicit `WordRanges`. The actual returned state has
strong memo provenance, exact guarded kernel meaning, an available result,
semantic heaps, and complete payload coverage. Every larger execution bound
returns the identical value and exact caches.

`constructed_node_complete` derives the initial semantic heaps and coverage
from an actual repaired closed source construction. Original payload syntax,
root availability and closedness, valid domain caches, and actual-prefix word
ranges remain explicit. The constructed cache need not satisfy universal
`PreparedWithoutMu` at its reached bodies.

## Remaining obligations

Derive output closedness and preparation, or a broader cold-reader invariant.
The successful native theorem does not prove a finite final cold table or
physical product language. Derive `ProductReadback.members` and `.rejected`
from actual physical rows, then apply `product_exact`. Universal preparation
preservation at all reached bodies remains refuted. Preserve that actual
native counterexample and the separate producer-history work.

Concrete machine-range justification, Haskell runtime correspondence, native
SCC/split readback, custom decoder order, and general equality propagation
remain separate obligations. The source models are handwritten.

## Validation

Lean 4.34.1 passes 1,348 aggregate jobs and 42,439 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-native-successful-20261014-audit.log`.
No Haskell source changed. The prior 641 passing Nix examples and active
package formatter checks remain the source validation checkpoint.
