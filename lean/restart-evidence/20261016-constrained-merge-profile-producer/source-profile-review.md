# Source comparison for the ordinary Merge profile proof

Audited main is c0cc8a05. The source refresh is unchanged. This checkpoint
contains no Haskell patch and establishes no new Haskell behavior defect.
Root FINDINGS retains the existing external repair handoff first.

Data.CFTA.Interned.Operations.mergeAlternatives groups ordinary closed rows
by symbol and child count. Its threshold is four. Small groups keep their
full original constraints and recursively process their children. A large
group transposes the original children and builds one unconstrained row.
Its column path filters against original closed Mu covers, removes repeated
identities, returns a singleton directly, keeps recursive boundaries as a
union, and otherwise merges the ordinary union recursively.

The current MemoGraph retains that threshold, full small-row guards,
source-order columns, selected singleton, ordinary union, and recursive
requests. Finite ordinary profiles exclude Mu, references, and explicit
unions. The new exact selection proof derives the absence of recursive
cover comparisons in that domain. It does not assert that absence for
general library inputs. Column unions can have a squared descendant row
limit. The new body and actual producer derive that larger profile.

The completed MemoGraph is a sequential projection. Haskell Memo installs
a lazy result thunk before forcing its computation. The graph runs a body
before completed insertion and rereads the keep-first winner. The new
profile proof verifies that exact graph and winner. It does not prove early
publication, pending-ancestor, concurrent forcing, or GHC correspondence.

Haskell uses HashMap.elems for outer group order. The modeled grouping uses
an executable ordered partition. Existing grouping_permutation retains the
semantic grouping contract under outer bucket permutations. It does not
identify complete constructor heaps from different traversal orders. A
concrete host grouping and allocation-order adapter remains open.

Merge remains an over-approximation. The full caller endpoint retains its
existing language inclusion and Post. It does not claim Merge language
equality. Exact size queries and ranks still use original sorted graph rows.

No source test is rerun because all Haskell bytes remain unchanged. Reuse
the recorded strict Nix all-component validation, 798 examples plus golden,
six-file Fourmolu, and four-package Cabal-gild/metadata checks. The original
recursive field-pool reproducer already returns FieldAtomOnDatatype under
repair b9219b9e from PR #65. Every later repair must be recorded in FINDINGS
with failure, reproducer, affected paths, commit, checks, and upstream status.
