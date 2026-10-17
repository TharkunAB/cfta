# Closed captures and empty-child filtering

The two selected theorems use one actual source-built fixture. The source
contains two ordinary nodes with the same full false guard. The first node
contains a closed raw unused Mu with body EmptyNode. The second contains
an open raw unused Mu with a captured reference. Both source records and
the replacement map are available in the returned Ready heap.

The replacement maps the captured reference to EmptyNode. The first
schedule makes the ordinary union and then reconstructs it. The second
schedule reconstructs each original value and then makes their union.
Both actual calls stop. Their full heaps retain Keeps. Both results are
the identical closed ordinary node. The open Mu rebuild uses the existing
empty-probe winner and smart cleanup returns EmptyNode. The closed raw Mu
stays captured and keeps its physical child row alive.

The second theorem proves Same at every finite depth and every view
between this actual closed raw Mu and EmptyNode. The Mu remains physically
different from EmptyNode. Thus even all-depth Same does not imply physical
empty agreement. The general fusion claim is not refuted by this fixture.
The fixture does not prove that claim either.

The existing empty tests are InternedEmptyNormalization.reference_empty,
makeNode_empty_iff, and makeUnion_empty_iff. The coherent node_free and
childFree_member equations show why a closed ordinary capture cannot hide
an environment-dependent child. SourceCurrentStoredSubstitutionOrigins
node_complete and union_complete separate exact closed captures from
actual open child/member call sequences. The repaired executor's closed
shortcut must be used; the older Scope.execute_closed statement names the
older executor.

A proposed proof can carry full atomic-child replay, exact physical empty
agreement, and root observations together. Prior makeUnion changes only
root flattening, duplicate removal, and ordinary-row aggregation. Actual
child replay can align unchanged payload calls in a common final heap.
Closed node and union capture readback still need explicit proofs. No
future successful callback or desired output relation can replace them.

Selected kernel attempt 3 has two signature and axiom pairs. Printer-free
strict attempt 1 has an empty log. Both verify 4 GiB maximum and high limits
with swap disabled. Attempt 1 could not access the systemd user bus.
Attempt 2 retains elaboration failures and sorryAx output. Neither failed
attempt is selected. The focused results establish no Haskell defect,
no universal fusion theorem, and no outer progress theorem.
