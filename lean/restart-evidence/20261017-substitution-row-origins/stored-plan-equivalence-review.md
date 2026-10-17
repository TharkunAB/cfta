# Stored plan equivalence review

Final source: `lean/MicroCFTA/SourceCurrentStoredPlanEquivalence.lean`.
SHA-256: `d2fe4986b0484c641b7ad140a032e2d5547592761f8bbfb054e972dd6ecd8211`.

The three mutual plan laws allow different capture contexts, local-name lists,
local-value lists, and replacement environments. Both capture contexts belong
to one coherent source heap. Each covers the source leaves. Local list lengths
match. The two lexical resolvers agree for every name. The proof covers all
value constructors, ordered child lists, and ordered edge lists. The Mu case
extends both lexical environments with the same new reference. This preserves
nearest-binding shadowing, including duplicate local names.

`build_execute` identifies the full repaired execution under the totalized
lexical resolver. `recapture` instead retains the original environment exactly.
It uses the source value's own leaves for the second plan. Both laws hold at
any current heap. They compare full outcomes, including pending results and
all cache effects. They require no current coherence, growth, callback result,
completion, finite Cap, or `PreparedWithoutMu` premise. The source availability
premise supplies leaf availability. The current heap can differ from the source.

These laws transfer an actual shared child plan to its own stored execution.
They do not prove a source/output row relation, callback completion, native
compiler closure, or whole outer termination. Those obligations remain separate.

Validation:

- Production direct1 executed its immutable absolute source snapshot with all
  linters. Its exit status is zero and its raw log is empty.
- Canonical1 built the one production target successfully (174 jobs).
- Public1 checks all five public declarations with explicit signatures, full
  proof printing, and axiom printing. The raw log has no printer omissions.
- Kernels2 is an empty-log proof check. The first integration constructs an open
  node from empty tables with a retained nested raw Mu. It derives availability
  and coherence from that actual construction, then recaptures a shifted and
  duplicated leaf context at every current heap. The second integration changes
  capture layout and local representation. Duplicate local names select the
  first local value. Both actual executions agree with the same replacement map.
- Kernels-public1 checks both complete integration signatures and their axioms.
  All selected proofs use only `propext`, `Classical.choice`, and `Quot.sound`.
- Every command reads effective cgroup memory.max and memory.high as 4294967296
  and memory.swap.max as 0. The largest observed peak is 224 MiB.

Kernel attempt1 failed on a qualified helper name and list-membership proof
syntax, with unused simp arguments. Its source and raw diagnostics remain in
this component. The corrected kernel does not change the production source.
No old source, Audit file, Haskell file, or frozen evidence file was changed.
