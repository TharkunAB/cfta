# Independent review of row-occurrence progress

Reviewed on 2026-10-17 at source checkpoint 5286227c.
This is a read-only source review. It adds no theorem or example.
It does not treat a proposed order as an established invariant.

The missing bridge is an occurrence-labelled relation through the complete
actual Parent return, followed by a separate compatibility invariant for
physical memo keys. A relation on complete returned values is too strong.
A decreasing relation on causal labels alone does not exclude a busy key.

The checked OriginalRepeat theorem gives a precise boundary.
SourceCurrentOuterOriginalRepeat.original_reappears_with_new_inherited proves
that the next reached request contains the exact original input value.
The original root owner is still evaluating. The inherited payload changes
from empty to [[[0],[1]]], so the physical key differs. The repeated local
precheck returns empty children. Both complete calls return Empty.
Thus whole-value strict descent fails. The same root row payload also
repeats because the complete value repeats. A rank of physical row identity
alone therefore fails too. This does not refute a different proper
contributing row occurrence, such as an occurrence in the original C child.
It does not exhibit a busy-key recurrence or divergence.

Several checked components already provide parts of the required relation:

- NativeRowOrigins.rows retains indexed paired input rows, exact call states,
  and ordered child requests through ordinary compilation. Its union theorem
  retains actual member calls. Normalization can remove or reorder rows.
- NativeEdgeWriterGrowth.History.writers retains the exact captured native
  handle, its actual earlier body and finish, and growth of both writer heaps
  into the current reader heap. History.warm identifies the complete request
  at an actual ready demand. Writer.live gives the literal full joined guard
  and ordered actual child Walk. These are past-execution facts.
- RequiredRowOrigins.node/children/rows produce an occurrence map from the
  initial ExposureSafe condition. Origin.nonplain and physical_positive
  recover a source RowAt occurrence. RowAt records row and child indices,
  union-member indices, and semantic Mu-body positions. It excludes probes.
- GatePlainRegion.annotations and reached_empty give a zero-own region from
  the actual available gate-accepted value. They need no global plain heap.
- LiteralUnionFusion.initial and StoredFilterReconstruction.complete derive
  actual calls with the same literal root atoms and ordinary rows. Bare self
  remains. Only a literal self alternative at a union root is removed.

These facts do not yet compose to a complete Parent output-origin law.
The required route passes through actual selected projection, native query,
Target/Force/Leaf, Edit, ClassPass, Merge, and constructor receipts.
A warm result must use its captured writer request, not the current numeric
key as a replacement for that request. The captured operands can themselves
be generated outputs. Their occurrence labels must be transported from the
states where those operands were actually produced. One fixed original
carrier for every later adaptive query is not justified.

The exact retained-Mu gap remains important at this composition boundary.
StoredReconstruction.mu and StoredReconstructionReplay.mu construct both
actual body and ordinary-probe reconstruction schedules, including common
final replays and causal writers. They do not compare the returned results.
StoredFilterReconstruction compares a filtered value with its own retained
original alternatives. It does not align two different callback writers.
Literal root predicates keep an entire Mu opaque. Exact Mu atoms from union
fusion therefore do not identify different body/probe Mu results or supply
origins for their recursively exposed rows. The needed alignment must come
from actual publication callbacks and earlier winners. It must preserve the
occurrence relation needed by the parent proof; an assumed final relation
would not close this gap.

Literal joined guards are useful but positive accessor origins need care.
NativeOwnOriginBoundary.accepted_join already rejects the unqualified claim
that a nonempty joined accessor implies a nonempty accessor in an operand.
That example concerns the actual field/arity acceptance check, not semantic
nonemptiness. Raw stored classes and residual guards remain separate inputs.
Normalization can also merge several constituent classes into one returned
class. A returned class need not equal one input class. A class-origin law
must retain constituents or a derivation, not select an equal input class.

Inherited progress is checked only for the appropriate local transition.
OuterInheritedDescent.descend_lt lowers the height of a ready nonempty
payload under actual indexed descent. NormalizedInheritedPrefix.plain and
descend extend this result across an empty-own prefix when the inherited
payload is fixed. EqualityOperationFixed.inherited_prefix and prefix_descend
derive fixedness from actual operations. They do not assert that adding a
nonempty local own field decreases the previous inherited height.
EqualityDependencyDescent.retained and subsumes_iff preserve strict-prefix
dependencies between retained classes of one fixed payload. They do not
compare arbitrary earlier and later payloads after new local combination.
The frozen InheritedGrowthBoundary rejects a bound by the one local maximum
path length for repeated combine/descent algebra. That algebraic boundary
is not an actual reached outer loop.

A useful next general target has three separate obligations:

1. Produce labelled occurrences through each actual Parent return. For every
   positive returned row reached through an actual selected child, retain
   contributing input occurrences, ordered query-child lineage, and the
   normalized inherited/own class constituents. Derive these facts from
   actual callbacks and memo histories. Keep occurrence indices when equal
   guards or complete values share physical records.
2. Prove a well-founded transition on this labelled state. A candidate split
   is proper contributing-source progress, or progress in a normalized
   class dependency while the source occurrence remains fixed. Prove the
   split through copying, duplication, retained Mu results, and warm Merge
   winners. It is not established merely by giving the split a name. A finite
   multiset order could allow several lower-origin copies; a simple count
   need not decrease. Writer publication time is not such an order: a fresh
   child query can publish after the outer owner has started.
3. Prove compatibility with every active physical owner. For an actual next
   node dispatch and every evaluating node cell, derive a different complete
   request key. A smaller causal label is insufficient when distinct labels
   can denote the same physical value and inherited key. The missing class
   dependency invariant must prevent that alias, or show that the live
   dispatch cannot occur because the prefix already erased its children.

The key families must remain distinct in these obligations.
AllocatedPartialState.NodeRequest.key is inherited.identity paired with the
tagged value.referenceOf. EdgeRequest.key is inherited.identity paired with
the physical edge identity. Native query tables have separate request keys
and handle spaces. A captured native writer handle is not an outer active
owner handle. Heap growth also does not order either family of handles.
Canonical identity equality must use the actual stored/readback invariants.
It cannot be inferred from path height or semantic equivalence alone.

Immediate node_key_ne does not discharge obligation 3. It separates the
input of one nonempty inherited descent from its output. Intermediate own
combination can reset that comparison, and a more distant active owner may
have a different earlier inherited payload. An invariant must quantify over
all such owners and survive every intermediate Parent and child step.
OuterBusyOwners.node_busy/edge_busy only identify the evaluating owner when
a busy result occurs. They do not exclude it.

The edge-family phase discipline offers a smaller separate obligation.
AllocatedPartialWorker.edgeBody calls Parent and advances checked state and
warm memos without changing either outer table. edgeCall finishes before
rows enters descendants. Thus an initially idle outer edge family has no
recursive outer edge dispatch inside that active edge body. This source
observation suggests a direct edge-idleness invariant. It does not justify
assuming arbitrary supplied outer tables are idle. Recursive node owners
still require the full ancestor argument above.

The strongest defensible next claim is therefore an actual Parent occurrence
producer plus inherited-class lineage, with all-active key compatibility as
an explicit subsequent theorem. Existing results do not yet prove either a
complete global rank or general outer completion. No new Haskell defect or
runtime divergence follows from this review.
