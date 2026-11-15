# One assignment for the entire removed arrow-child bucket

Recorded: 2026-11-15 03:25 CET.
Status: UNCOMPILED CANDIDATE. Root owns validation and publication.

Replace only SourcePruningEnumerationSharedProperPathWitness.lean with this
candidate after review. candidate.patch records the exact change against the
published source SHA256 b8d066ac5587518a7b4615f41f4ee5efc1eb0b39c2447d1ebd1e1847ab3eb5e4.
No live source was changed here.

## Exact statement and restriction

New public declaration:
MicroCFTA.SourcePruningEnumerationSharedProperPathWitness.selected_parked_arrow_bucket_assignment.

The explicit shape input is:

```lean
(arrowPaths : ∀ sc ∈ bucket, ∀ path ∈ EqualityTrie.fromPathTrie sc.trie,
  path = [1] ∨ path = [2])
```

EVERY represented path must satisfy this condition. It excludes [] and deeper
paths. No source lemma says that every actual removed bucket has this shape.
Do not infer this condition from canonical waiting counts or source acceptance.

The theorem keeps actual CacheValid/Safe, actual restart selection, the exact
original full selected slot and bucket, and the literal actual shared parked
prefix at the original supplied workFuel/depth and endpoints. There is no
model, alias-separation, finite-productivity, future callback or compatibility
provider premise.

Its existential rho precedes BOTH universal bucket conclusions:

```lean
(∀ sc ∈ bucket, Suspended.Holds rho (rho uv) sc) ∧
(∀ (occurrence : Nat) (sc : Suspended), bucket[occurrence]? = some sc →
  Suspended.Holds rho (rho uv) sc)
```

The same rho also satisfies ALL original/checked/parked/restarted UF aliases.
The exact stored full bucket and actual Success clear are retained. No list is
filtered, sorted, or deduplicated. Every duplicate occurrence and raw target
remains in the indexed conclusion.

The assignment remains explicit: selected UF class maps to arrow(var1,var1),
and all other classes map to var1. Actual IncomingAvoid separates every stored
raw target from the selected class. Both arrow children are var1. This proves
all bucket equations simultaneously, without combining separate witnesses.

## Factoring and compatibility

There is one long constructive proof, in the private helper
selected_parked_arrow_child_paths_assignment. It obtains the actual parked clear
and compression frames, then returns indexed equations for all [1]/[2] paths
under ONE rho. The old one-path theorem is now a short compatibility wrapper.
Its complete explicit header is BYTE-IDENTICAL to the published theorem.
ORIGINAL-ONE-PATH-HEADER.lean.txt preserves those original statement bytes.

The new whole-bucket theorem is another short wrapper. It applies the explicit
shape condition to the helper's common assignment and proves full Holds for
all represented paths of every original bucket occurrence. The original
144-line proof body is not duplicated.

Existing TypeIn.leaf/arrow/member still prove finite original-universe SYNTAX
membership of every assigned term. This result does not identify a native
handle with U or prove satisfaction of another narrowed native domain.

## Full objective remains open

This result does not establish EnumerationCorrectness.Satisfies, stored parent
fragment equations, residual guards, other native domains, other historical
buckets, or accepted completion of the original root. It cannot supply separate
assignments to those obligations and then combine them without proof.

The original full SAME-root one-assignment specification remains unchanged at
../20261115-joint-finite-witness-semantic-audit/ORIGINAL-RELATION-TARGET.md,
SHA256 27f43faf2d8ad79d05aea36c72dca159118629f63b75736795abab41d0125183.
All supported paths/domains/aliases/residuals, readback, parked backward
recompletion and ALL historical removed obligations remain required under ONE
final rho. Preserve original budgets/fuels/noStop and earlier outputs after a
later stop. This restricted bucket case is an intermediate construction only.

No Haskell source, FINDINGS, Git state, board, /tmp, compiler, or live Lean source
was changed. This packet alone contains the draft.
