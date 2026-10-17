# Required worker depth from the original trie

SourceCurrentRequiredWorkerNumeric.workFuel is 2 * sizeOf needed + 1.
It is a logical bound. The derived Needed sizeOf instance is noncomputable
in this Lean build. This definition is not an executable Haskell budget.

Each ordinary node spends one worker step. Each recursive head spends
one step, then its ordinary result spends the next step. Available cached
node reconstruction returns an ordinary or empty head. Each selected child
has a strictly smaller Needed trie. Ordered child and row scans share the
same worker fuel; they do not charge one recursive step per list entry.
This bound depends on no returned heap, graph size, or observed result.

The generic node, children, and requireAll endpoints verify actual graphs
with semantic heaps, cost heaps, and available inputs. They need no global
closedness. Their reader bound remains existential and comes from the
actual graph. These generic endpoints do not assert initial completion.

SourceCurrentConstrainedCapSelectedRequiredWorker.complete and caller
start from the original false primary certificates and the prior initial
selected-Required support. They construct their own successful execution.
The numeric verifier then gives stable replay at every worker fuel above
the initial trie bound. The same returned value and heap retain the full
Required receipt, global reads, Frame, effects, output caps, and forest
length. The caller retains the full Post and both outer tables, fourth
memo, and Merge table exactly. No future worker or graph is an input.

The initial wrapper constructs its reader bound existentially. It does
not provide an initial numeric reader forecast, complete Required Profile,
or forecasted Fits. The separate WarmHead and pure profile work must still
be composed through actual selected child and row execution.

Final strict snapshots are worker-numeric-direct-5.source.lean and
worker-initial-direct-1.source.lean. Both final logs are empty. Their
canonical builds pass. worker-public-1 checks all six public declarations.
worker-contract-1 constructs exact language and selected returned domains
from its own initial completion with the same numeric worker replay.
Every failed source snapshot and raw log remains preserved. The third
numeric attempt deliberately printed the failing termination context.
