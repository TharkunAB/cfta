# Supported source simulation and reader requirements

Updated: 2026-10-18 14:09 CEST. Proof checkpoint is `faca56de`.
Starting checkpoint is `4ac2365d`. Main source remains `c0cc8a05`.
Read `lean/notes-current-supported-source-simulation.md`.

The strongest broad result is conditional partial correctness of the
checked implementation model. A supported successful top-level traversal,
empty inherited constraints, initial semantic facts and scheduled
resources give exact equality of the input and returned finite tree
languages. This does not prove general termination or full public Haskell
correspondence. The required source semantic instances remain explicit.

Actual closed-Mu preparation now also supports all available values with
zero stored-plan binder depth. These include open ordinary nodes, unions
and references with closed recursive Mu components. A source-built example
has a cold closed Mu in an open node and union. Actual preparation changes
the heap, retains both open values and makes the recursive unfold warm.
This does not prepare arbitrary open Mu values or transport observations
from the cold reader.

Actual source execution and causal reader history now derive the selected
writer, exact current probes and both reconstruction schedules. The seed
assumes no Same, Directed, BodyIH, selected writer or output endpoint.
Earlier writer syntax remains separate from requester syntax. Literal
normalization inclusion has an actual Directed instance. Actual source
node calls derive both local directions from indexed strict-child cases.
These results do not yet construct the general source relation or its
changing-capture used-binder local clause.

A source-built counterexample strengthens the reader boundary. Both heaps
are Ready. Inputs and replacement values are available at both heaps.
The returned Mu pair still fails depth-one agreement at the separate
reader. One compared output is explicitly unavailable there. The two heaps
allocate independently. This does not refute a common later reader,
output availability or WarmSupport. It is not a Haskell defect.

Full Audit passes 3315 jobs and 72078 dependency checks.
All 15 new public and 3 constructed heads pass complete
statement, proof and standard-axiom checks. All seven selected strict logs
are empty. Three canonical builds have no warnings. The boundary canonical
build and Audit retain only the existing ClosedCompletion warning.
Seven component manifests pin 298 entries. Independent review finds
no material issue. Evidence is in
`lean/restart-evidence/20261018-supported-source-simulation/`.

General changing-capture used-binder simulation and reader support remain
the main source gap. Initial query-operand ancestry, all active node-owner
exclusions, fresh-call bounds, recursive completion, repeated convergence,
equality resources and host Int adequacy remain separate obligations.
No Haskell patch or new executable defect is added. FINDINGS retains the
repair registry first. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Publication awaits the existing direct approval. No push is retried.
The full-library goal remains active.

The production modules are SourceCurrentZeroDepthReaderSupport,
SourceCurrentRetainedProbeSchedule, SourceCurrentSourceDirectedCases and
SourceCurrentReadyReaderObservationBoundary. Audit adds only these four
imports. The first two modules each add two public declarations. The source
clauses add ten. The reader counterexample adds one. The three separate
constructed probes cover actual cold preparation, a different-syntax
requester and a recursive-capture node and union schedule. They do not
count the production counterexample twice.

All 30877 starting tracked files remain. All 3310 older non-Audit Lean
sources, 242 Haskell files and 206 active package files retain their bytes.
Two stashes and three other worktrees retain their metadata. Preservation
checks 163 frozen manifests with 1072 module entries. Earlier proofs,
repairs, counterexamples, attempts, drafts and optimized core remain.

## Concrete theorem boundary

SourceCurrentOuterInitialActual.node_call derives NodeLaw from Context,
Frame, Fits, Carrier, inherited readiness, resident input, scheduled Room
and a literal successful nodeCall. SourceCurrentAllocatedPartialMemoSound
defines NodeLaw. The result accepts no additional finite terms. It retains
exactly those input terms that satisfy the inherited constraint. Empty
inherited constraints give equality of the finite tree languages. The
theorem does not construct every semantic source instance needed by those
premises. It does not state that every call returns or that Haskell has
been proved equivalent to the model.

## Source-generated relation work

SourceCurrentRetainedProbeSchedule.binder consumes an actual completed
source binder, its initial Context, forward Keeps into a reader and an
actual causal Path from empty. It recovers the whole selected record,
current probes and one actual earlier writer. Its Seed retains each
writer prefix and callback path, body, depth, ordinary field and exact
selected key. It constructs the selected Mu unfold and then ordinary
reconstruction with that same Mu replacement. It proves the initial
reader epsilon successor, final warm replays, availability, local histories
and retained selection. The unfold can allocate. Its returned values are
available at the final execution heap. The initial reader is not claimed
to contain those returned values already.

SourceCurrentSourceDirectedCases.Below includes exact literal references,
whole Mu values and full ordinary rows. It does not unfold Mu inside the
literal inclusion test. below_directed proves Directed at any fixed
reader. Literal occurrences use the same whole Mu and actual unfold at
that reader. union_member and union_reconstruction derive normalization
fragments from actual calls. Below.trans is exact inclusion composition.
No arbitrary-P transitive-closure simulation theorem is claimed.

The node rule consumes actual paired raw source calls and paired stored
calls at one Ready execution heap. Indexed strict-child hypotheses apply
only after those children have their own actual calls. They supply Empty
agreement for row survival and mutual relation membership for ordered
children. The rule derives both local root clauses. It does not assume
or conclude a global Directed law or parent relation membership. A source
generator must supply that membership, then prove the binder local law.

The main remaining construction must allow actual source and stored
endpoints to seed mutual self membership before local simulation is
proved. Epsilon steps need a directional relation. Ordered row children
need both directions. Empty agreement belongs where physical filtering
uses it. A Mu and its unfold need not agree on physical Empty. An earlier
writer's own syntax must be used for its body argument. The current
requester's ordinary probe is the exact selected ordinary field, but its
source syntax need not equal that earlier writer's syntax.

## Reader support boundary

Zero-depth support uses actual closed preparation. It covers open
ordinary structures with closed Mu components. It leaves arbitrary open
Mu preparation unproved. The closed degree-decrease argument cannot be
applied to an arbitrary open self capture without another proof.

The new counterexample builds both Ready heaps from one source-built
base. They then allocate independently. Two changed captures agree at
depth one at the reader. Four actual source and stored calls replay warm
at the execution heap. Their two used-Mu results fail depth-one agreement
at the other heap. Its first result is explicitly unavailable there. It
shares a reference identity with that reader's own resident open Mu.
Actual unfolding selects a row containing that resident value. An exposed
bare reference distinguishes the ordered first children. No payload is
edited. This does not refute a common forward-growth reader, availability
of all compared outputs or WarmSupport. It does not establish a finite
tree language difference or executable Haskell failure.

## Validation and continuation

Selected jobs use Lean 4.34.1, 4 GiB maximum and high limits, zero swap and
five-minute caps. All complete public probes use the eight required
printer and linter options. The permitted axioms are propext,
Classical.choice and Quot.sound. Failed attempts remain unselected.
The first root fixture public print terminated with SIGTERM. Its cause
is not established. The final corrected fixture has a literal empty
strict log and a complete passing public print. No failed or warning
attempt is classified as a clean check.

Read NEXT.md in the evidence directory before the next proof step. Verify
the checkpoint, preservation and clean committed closure. Keep all work
local until the existing publication approval is resolved. Record actual
Haskell fixes first in root FINDINGS. There is no new Haskell fix here.
