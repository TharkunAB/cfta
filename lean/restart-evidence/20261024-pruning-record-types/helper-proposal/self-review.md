# Author source review

Status: SOURCE_ONLY_UNCOMPILED_PROPOSAL. This is an author self-review.
I read the complete 188-line candidate and the native/helper source scopes in
source-index.json. Root requested these three functions and owns future checks.
I did not run Lean, a compiler, a test or a prepared program. I did not change
repository files. The only new files are in this proposal package.

The native typePositions applies IntSet.insert only at a raw type-position hole.
The model uses canonicalIds (uv :: types) at that exact branch. A program hole
returns the original types list. Generic type nodes use foldr at all children.
Ordinary app/4 keeps the source's annotation/marker fold around the nested
function/argument fold. Ordinary filter/2 processes its program result as the
annotation accumulator. Other concrete shapes treat every child as a type.
This retains the source expression structure. It is not an eager evaluation-order
claim about Haskell's pure lazy calls. Native canonical-list extraction is separate.

programHoles returns no result below an incoming type position. A raw program
hole contributes its singleton ID. Ordinary applications concatenate function
holes before argument holes. Filters select the second child. Other nodes yield
no program holes. The repeated-hole theorem retains two equal occurrences.
These lists must not be canonicalized, deduplicated or mapped to representatives.

openProgram ignores children on hole/truncated symbols, as the source does.
It renders type holes as (?, Top), program holes as (?program# ++ toString rawNat,
Top), and truncation as (Mu, Top). Concrete full labels remain exact. Ordinary
application/filter shape tests use full labels, not just text. Concrete nodes
below type positions and fallback shapes recursively render every child as type.
The nonordinary four-child equations make the refined-label distinction explicit.

The type-hole membership, sorted and Nodup proofs reuse existing canonicalIds
contracts. The app membership proof uses actual list append. Other theorems are
literal positional/rendering equations. Every public declaration has a doc string.
No proof-limit/linter override, axiom or new typeclass instance is introduced;
the existing Formula equality instance is enabled locally.

The optional global theorem that typePositions preserves a canonical input list
is not part of this candidate. Its absence does not weaken the exact function or
paired exact-output callback observations. A native IntSet extraction bridge must
retain the input canonicality condition and separately prove preservation.

Raw native UVar storage is Int, and intToUVar accepts arbitrary signed values.
The Nat model therefore covers only a nonnegative, representable native ID range.
Decimal formatting agrees only under an explicit Int/Nat/format extraction bridge.
There is no machine-overflow, complete Haskell extraction or semantic typing proof.
This proposal does not model openTypes, recordTypes, typedTypes, nodeEdges, narrowing
or stopping. Those use these helpers in separate future source models.

I found no concrete source-contract mismatch after the full reread. Termination,
elaboration and all-linter acceptance remain unverified until Root compiles.
