# Related physical product rows and native Sized composition

Updated: 2026-10-14 19:20 CEST.
Proofs: `f04b8261`, `4d80735a`, and `ddef16e6`.

## Exact language from local rows

`RelatedRows.Match` retains a complete symbol, guard, and ordered list of
related children. `RelatedRows.Readback` gives local row soundness and
completeness. A deleted row has a false guard or a chosen related child with
no rows. One input state can have several physical representatives.

`RelatedRows.language_exact` proves exact least finite-run languages by
finite-term induction. It permits arbitrary cyclic graphs. No state
finiteness, functional representative, or language contract is supplied.
`of_normalized` derives this interface from the existing normalized rows.

`DiagonalProduct.graph` copies original rows on diagonal input pairs. Other
pairs have the ordinary synchronous rows. `language_exact` proves the full
intersection language. It permits ambiguous source rows. Diagonal reuse does
not require retention of every cross-product row at a self intersection.
`related_product_exact` composes both proofs.

`SourceCyclicRowsNativeGate.functional_related` derives the new interface
from the existing functional product contract. The older proofs retain
their stated scope and remain unchanged.

## Actual ordinary calls

`SourceRecursiveIntersectionKernel.edge_related_product` derives a matched
row from an actual completed equal-arity edge call. Its relation uses actual
successful child calls in the retained source domain and final cache. It
retains the complete conjoined guard and ordered children. No default child
value or language contract is used.

`node_related_product_rows` derives soundness and completeness for an actual
ordinary parent. Rejected source rows have an actual related empty child.
`SourceRecursiveIntersectionNative.native_ordinary_related_rows` derives
these laws from actual checked native execution. They hold at every larger
kernel bound and every later valid cache. Checked `WordRanges`, exact
original domains, source availability, and guard interpretation remain
explicit. This is a local ordinary case. It does not assert closure of the
relation through arbitrary Mu and union calls.

## Actual callback and Sized compiler

`related_callback_eq` identifies the actual finite minimum-row callback with
the explicit synchronous-product reference callback. It uses related rows,
related result roots, and completed `toRows` extraction. It does not require
a single physical representative for each source pair.

`related_scan_eq` proves equality of the complete ordered ambiguity scan.
`SourceCyclicRowsNativeGate.Relational.compile_eq` retains every compiler
outcome and error. `compile_finite` proves a finite result. `class_correct`
proves exact distinct guarded node-count classes, finite count and decoder
evaluation, exact counts, and decoder order. `query_inverses` proves both
rank inverses, valid rank coverage, and exact rejection. All use the existing
reference compiler through literal result equality. The physical relation
and completed extraction remain explicit premises.

## Complete language of the retained finite transcript

The live smart-Mu witness has original source identities 7, 11, and 12 and
additional product identities 18, 19, and 21 in this process. Each has an `a`
leaf and an `f` successor. The successor index lists are `[2, 2, 1]` and
`[0, 0, 1]`. All guards are `noConstraint`. Identities can change in another
process.

`NativeProductRowCycleReadout` defines exactly these finite graphs, including
the retained source copy. `full_product_language` proves the complete input
intersection language for each physical representative. `representatives_equal`
proves full language equality of the actual root and rebuilt parent.
`literal_rows_differ` proves their physical row lists differ.
`no_functional_readback` proves that the observed parent and child results
exclude the proposed general functional product-row adapter. No other meet
answer is fixed by that obstruction theorem.

This unbounded theorem concerns the explicit transcript. The current Haskell
row dump and a focused Python comparison validate the table, guards, arities,
closure, and index maps. They are not verified Haskell extraction. The earlier
checks through unary depth 24 remain finite validation only. The identity
difference does not establish a semantic runtime defect. Keep the optimized
interned core unchanged.

## Next proof target

Derive a relation between actual native physical records and original input
pairs through Mu construction, stored substitution, union normalization,
exact domains, and repaired final row exposure. Prove its local row closure
and related roots. Use the completed generic product, callback, and compiler
results above. Do not repeat those proofs or supply language equivalence as
a premise. Do not try to derive the refuted general functional child map.

The complete native two-input language theorem and verified runtime
correspondence remain open. The primary finite-map reference, solver-decided,
and optimized Sized route remains proved with its explicit synchronous
product. Preserve all earlier constructor and equality work as secondary
results.

## Validation and preservation

Pinned Lean 4.34.1 passes all seven focused modules and the aggregate audit:
1,470 jobs and 43,899 theorem dependency checks. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. All new modules are imported
by `MicroCFTA/Audit.lean`.

Audit: `/tmp/mcfta-relational-product-rows-20261014-audit.log`.
Readout: `/tmp/mcfta-product-related-readout-20261014.log`.
Comparison: `/tmp/mcfta-product-related-readout-validation-20261014.log`.
The readout source and comparison script remain in `/tmp`. The checkpoint
snapshot saves their exact bytes and focused build logs.

No production Haskell source or committed test changed. Prior Nix and
formatter evidence remains applicable. Both untracked reproduction fixtures,
all marked drafts, backups, stashes, and worktrees remain. All work stays local.
