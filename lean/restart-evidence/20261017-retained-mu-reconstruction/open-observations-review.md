# Open observations review

Final source: `lean/MicroCFTA/SourceCurrentOpenObservations.lean`.
SHA-256: `2507913caa52802712e98a0126e27b446665a9130ae013cbfdc759f5da332522`.

`ReferenceOrigin` is actual epsilon reachability to a literal reference.
`Same` compares two seed lists in one fixed physical view heap. Depth zero
retains reference names. A successor depth also matches each constructor row
in both directions. Matching rows retain the exact symbol and full guard.
Their children satisfy an ordered `All₂` relation at the previous depth.
Rows match by occurrence. The relation does not preserve row count, row order,
or identity. Node and union normalization can remove or reorder rows.

The proof establishes reflexivity, symmetry, transitivity, and depth lowering.
Exact reference and physical row origins give `Same` at every depth. Seed
splitting and nonreference expansion derive reference exposure laws directly
from actual reachability. A bare reference exposes exactly its literal name.
Literal unions relate to their member seeds. A completed actual repaired Mu
unfolding relates the Mu seed to the exact returned value in that view.

`unfold_complete` starts from SemanticHeap, complete payload coverage, and
availability of the actual Mu. It constructs its own completed unfolding.
It retains SemanticHeap, coverage, output availability, heap growth, and
issued-reference history. It also derives `Same` at every depth. It has no
closed-value, finite-Cap, future-callback, or supplied-completion premise.

The relation uses the fixed `MergedFreshOrdinaryGraph.successors view` model.
The completion producer uses its original entry heap as that view. It does
not identify an evolving operational reader with this fixed-view graph. It
does not transport observations to another view without a separate replay
argument. These laws do not prove reconstruction fusion, substitution
congruence, physical equality, or whole outer completion. In particular,
row-only erasure laws cannot discard a reference under `Same`.

Validation:

- Production direct3 executed its immutable absolute snapshot with all
  linters. Its exit status is zero and its raw log is empty.
- Canonical1 built the one source target successfully (545 jobs).
- Public1 contains 14 complete `#check @`, `#print`, and axiom-print groups.
  It sets every requested printer option and contains no printer omissions.
- Kernel2 has an empty strict log. One integration builds a closed productive
  raw Mu from empty tables. Its local is used. Its own unfolding returns a
  positive literal leaf row and supplies observations at every depth.
- The second integration proves that a bare Depth reference and Empty have
  equal constructor row origins but different depth-zero open observations.
- Kernels-public1 contains both complete signatures and axiom reports.
  All selected proofs use only propext, Classical.choice, and Quot.sound.
- Effective memory.max and memory.high are 4294967296. Effective
  memory.swap.max is 0. The largest observed peak is 192 MiB.

Direct attempt1 contains elaboration errors in indexed reachability induction
and relation orientation. Direct2 passed. Direct3 removes an unused private
helper. Kernel attempt1 contains one proof-equation elaboration error. All
attempts and raw diagnostics remain unchanged in this component. No old
source, Audit file, Haskell file, or frozen evidence file was changed.
