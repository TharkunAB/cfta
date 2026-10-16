# Independent current Scan-to-class-pass review

Date: 2026-10-16 09:49 CEST.
Reviewed final source: `SourceCurrentConjunctionScanClassPass.lean`.
SHA256: `ecd400e64907f293687810bdc3cf86f1302a82ab6a8c20d422331118daa4715d`.

No material proof or model defect found. No source changed. No canonical
Lake build ran for this review.

The source branch at `Equality/Operations.hs:208-226` returns the original
forest for two empty equality payloads, erases every child on combined
contradiction or a true refused-class emptiness result, and otherwise starts
required execution before the right class fold and final empty propagation.
This new module starts at the current Scan stage. The preceding two precheck
branches and raw constructor contradiction handling remain separate.

`Reduction` stores one literal actual Scan. Its stopped constructor erases
only the original child slots, keeps the exact Scan-returned checked state
and fourth memo, and retains the unchanged merge memo. Its completed
constructor retains that same successful Scan, an occurrence-sensitive
`Retained` proof, the actual required-worker result at the returned heap,
and the actual class pass at that exact advanced checked state.

`Reads.completed` threads the literal global bundles in source stage order:
initial to Scan return, then required return, then class-pass return. The
successful proof calls logical helper theorems more than once for the same
Scan. This does not introduce another Scan into the operational graph. The
returned read witness comes from one consistent chain; no equality between
independently chosen intermediate witnesses is asserted or needed.

Stopped erasure is sound for zero children. `erase [] = []`, which still
accepts the empty ordered forest. The theorem does not falsely claim that
erasure alone rejects a zero-arity parent. Instead, conditional exactness
uses the derived rejection of an original class to rule out original
acceptance together with satisfaction of every original class. The separate
independent kernel probe checks the zero-child read receipt and this empty
forest language boundary.

The successful branch uses the exact positional selected record relation.
It preserves original order, multiplicity, and metadata even if records have
equal path lists. The original-class premise in final conditional exactness
covers all original records. `kept.Sublist records` restricts that premise
only when invoking the actual class-pass law; it does not replace it with a
selected-only assumption at the public endpoint.

The output arity proof composes actual required-worker length preservation
with the aligned class-pass transport length. It does not assume a future
arity result or generic native edge admissibility. Loaded fields, operation
validity/growth, scopes, idle state, and physical cache validity survive in
final `Ready`. Final `At` is derived at the actual computed inventory. The
actual returned checked state remains indexed in the reduction and reads.
No unconditional fixed-domain extension is claimed across native Scan work.

`Ranges.pass` asks for class word checks only after a raw actual successful
Scan, its positional retention proof, and an actual required-worker return.
It supplies no future `Ready`, admission, language result, or successful class
callback. `finite` constructs the actual Scan from initial invariants and
ranges, then derives its required/class continuation. Initial fourth-memo
correctness, global validity, warm merge residency/language coverage, proper
paths, coherent nontrivial records, and reached ranges remain legitimate
explicit premises.

The final receipt exposes global validity; exact global effects remain in
`Reads`, rather than an unproved blanket unchanged-query or extension claim.
Its fourth correctness and retention pass through both source outcomes and
post-Scan class heap growth. No native or equality table reset occurs.

This is finite completed relational execution with independent conditional
language bounds. It does not establish GHC partition/list forcing, published
thunk interleaving, selection CAF allocation, native container ordering, or
the full constrained outer reduction loop. The preceding warm allocated
precheck and final checked edge construction need their own composition.

Validation: direct pinned Lean passed with exit code 0. The external probe
checks two public axioms, two public signatures, and three integration
kernels. Raw log: `scan-class-pass-independent-probes-1.log`. It contains no
warning, error, or `sorryAx`; allowed axioms only.
