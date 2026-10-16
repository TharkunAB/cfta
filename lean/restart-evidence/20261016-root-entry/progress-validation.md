# Current outer active-owner order

Frozen source: `SourceCurrentAllocatedPartialActiveOrder.lean`, 367 lines.
SHA256: `b315bfdf95cc9fdd61bf072f2ce69d7a72ed68ae151e8267a36d3f109a3ad628`.

The concrete ranks are `nodeRank request = 2 * height request.value + 1`
and `edgeRank request = 2 * (edgeHeight request.value + 1)`. Their combined
strict order is well founded. Actual ordinary row membership and actual
child membership derive strict descent. Equal current physical keys have
equal ranks only through coherent resident node or edge records.

`ActiveAbove bound state` checks every evaluating cell in both outer result
families. `ActiveExcept` permits one selected handle per family while an
ancestor bound is retained. Empty outer tables derive the invariant for
every bound and preserve all supplied lower warm state. Actual checked
advancement and indexed inherited allocation retain both result tables.

`node_begin_safe` and `edge_begin_safe` exclude busy and absent observations
from initial sound current cells, coherent input residency, and an active
bound at the candidate rank. `node_owner_rank` and `edge_owner_rank` read
the exact first stored owner of an actual evaluate observation. `node_push`
and `edge_push` derive the active invariant at any strictly smaller child
bound. Actual begin changes no other active owner. Literal finish removes
its own active phase and restores the ancestor bound from `ActiveExcept`.

`ReturnedBounds` is a separate structural invariant of actual returned edge
cells. `original_or_erased_bound` derives its pointwise height requirement
from an exact child-list equation. `returned_child_lt` gives next-node rank
descent from an actual returned cell. Empty tables, checked advancement,
and actual finish with the independently proved pointwise bound preserve
this invariant. No theorem derives the pointwise bound from semantic
`EdgeLaw` or from arbitrary constrained local reduction.

Direct pinned source elaboration returned exit 0 with no warnings in
`progress-direct-2.log`. Root's focused canonical build returned exit 0,
1397 jobs, in `progress-build-1.log`. Its only warning is the historical
unused `inputs` binding in `InternedFreshOrdinaryClosedCompletion`.

External canonical-import checks returned exit 0:

- `progress-public-1.log`: all 29 public declaration axiom/signature pairs.
- `progress-integration-1.log`: ten kernel integration examples. They cover
  retained warm lower state, an actual ordinary-node start admitting its
  original edge, indexed inherited allocation, begin/finish restoration in
  both result families, stored returned-edge descent, inherited-independent
  child rank, coherent node and edge key aliases, and accessibility without
  a finite key carrier.

Both final logs have no warnings, errors, or sorryAx. They use only standard
Lean foundations. The first source log retains corrected elaboration
attempts. No production source other than this new module was edited. This
owner ran no Lake, Haskell, or Git command.

The next independent obligations are actual local returned-child structural
bounds, their causal warm-cache preservation, reverse active restoration
through completed child graphs, and complete outer graph construction. The
root owns the reverse-running graph layer. This module proves no general
constrained completion, finite future-key inventory, fixpoint convergence,
or host scheduling claim.
