# Recursive source compiler certificate

Checked on 2026-10-17 at 00:51 CEST.

Production file: `lean/MicroCFTA/SourceCurrentAllocatedRecursiveDomainCode.lean`.
Final SHA256: `a87444fcab499c4c549a6c280d992797f82880ff100204e37b444f7862cea6c6`.
The file has 458 lines. All older proof files remain unchanged by this component.

The component proves local compiler closure. `Closed source inventory` contains
the empty key and the actual extended keys of original available operands.
`source_closed` derives this predicate for the computed initial source inventory.
`Certified` retains fixed-source node and edge scope, current domain inventory
membership, and exact enter-key membership. Primitive and binder continuations
use actual returned machines. `reference_certified` uses actual later readback.
`node_certified` covers every source dispatcher branch. `body_certified` covers
only the code emitted by the supplied actual checked edge-body yield.

The public signatures contain no word range, completed recursive call, future
result language, or desired structural result premise. The certificate uses
physical availability and residency as intermediate posts. The proof derives
these posts from constructors. It does not establish physical input checks for
an arbitrary finish instruction. It also does not establish raw-prefix
preservation, `DomainTrace.Prefixes`, or full `WordRanges`.

Validation:

- `recursive-prefix-code-strict-2.log`: pinned direct Lean, all linters, exit 0,
  no diagnostics. The output olean is under `/tmp`.
- `recursive-prefix-code-public-2.log`: 17 imported public declaration pairs,
  each with `#print axioms` and explicit `#check @`, exit 0, no diagnostics.
- `recursive-prefix-code-kernels-3.log`: three imported integration pairs,
  exit 0, no diagnostics. Each pair prints axioms and its complete signature.
- `recursive-prefix-code-canonical-final.log`: root-owned canonical build, exit 0, 2699 jobs and
  61547 dependency checks. It includes the exact final source. The only warning
  is the historical unused `inputs` binder in
  `InternedFreshOrdinaryClosedCompletion.lean`.

The integration kernels derive the actual entered key, recorded seen pair,
original body scope, and following body-request certificate. They resolve a Mu
from the actual grown heap before certifying the literal next request. They also
certify actual emitted checked code and its syntactically appended finish frame
at the exact returned machine. The last kernel does not claim that an arbitrary
handle has a running cell. Physical finish ownership is a separate obligation.

Raw failures and earlier green logs remain available. Direct attempts 1 and 2
have matching source snapshots. The earlier source with hash
`454911a84897df00970687dbc1c6b98a43e4ba989d773112d44fdf626005e24d` is retained
at `recursive-prefix-code-pre-linter.source.lean`. Strict cleanup added two field
docstrings and removed an unused symbol-equality premise from `body_certified`.
The final public and kernel checks use the final canonical import.

The canonical log is an owned copy of `lean-audit-before-prefix-split.log`.
The initial manifest and sums remain as `recursive-prefix-code-before-log-pin.*-history.txt`.
They captured the shared final log after the later 2700-job prefix-split build.
This corrected manifest pins the 2699-job log described above.
