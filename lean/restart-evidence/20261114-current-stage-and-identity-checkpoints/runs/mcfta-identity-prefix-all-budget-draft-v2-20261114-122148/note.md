Status: UNCOMPILED v2. No new theorem credit.

Input is Root check2, including its confirmed namespace opens and axiom prints.
The complete check2 diagnostics are frozen as diagnostics.txt. Exact source
and log paths/hashes are in capture-checks.json. The earlier packets are intact.

The patch makes three scoped corrections. It adds SourcePruningEnumerationNodes
to the first namespace open so lookupNode resolves. It adds DecidableEq Node
only in the private consumer namespace, as literal resumeWithNarrow requires.
It moves the existing DecidableEq EdgeKey variable below the private replay
law and before the final public resource law. The private replay does not
need that section variable. The public theorem keeps its original instance
and exact original header. This scope correction does not suppress a linter.

All proof bodies, including the raw replay and final transport, are unchanged
from check2. In that log, lookupNode and the missing consumer instance cause
cascading diagnostics. The only further diagnostic for the new whole-prefix
replay is its unused automatic EdgeKey section variable, addressed by the
scope move. No separate diagnostic identifies a defect in its raw operational
case analysis or the final equality transport. That observation does not
credit either theorem: check2 reports sorryAx through failed prerequisites.
Root must compile the corrected complete file and inspect every axiom report.

check2-to-v2.patch gives the exact corrections. The inverse checks recover
the original check2 input bytes. The complete original target-header file is
byte-identical. All twenty live source pins were rechecked. No compilers,
live source, Haskell, Git, or board actions were performed. No Haskell fix
was identified. No artifacts or build caches are included.
