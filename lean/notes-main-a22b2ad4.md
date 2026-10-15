# Conservative emptiness and refused equality classes

Current source main: `a22b2ad46ffcad57a77b64447c18da7b0850f52f`.
Preserving merge: `e612302b`. Pre-merge checkpoint: `aaeeac64`.
Backup: `backup/formalize-before-main-a22b2ad4-20261015-1648`.
Proof commits: `598ad8dc`, `59b2fbf4`, `0414c98b`, and `dab4eade`.
These results extend the [stateful gate checkpoint](notes-endpoint-memo-stateful.md).
Full source correspondence and full library scope remain open.

## Source comparison

Upstream adds `Data.CFTA.Enumeration.provablyEmpty` and an early return in
`reduceEqConstraints`. The primary gate uses `belowEnd=True`. It retains the
24a710a3 descendant check at ordinary endpoints. Refused classes receive a
secondary check with `belowEnd=False`. This mode has the older free-reference
endpoint rule. It still checks constrained Mu nodes and performs required
unfolding. The new Boolean controls only the extra endpoint descendant read.

For a refused class, the source first requires every secondary path check to
clear. It then projects the original children, intersects the path nodes,
and calls `provablyEmpty`. A true answer makes every original child empty.
Otherwise the selected-class path requirements and edits continue. The
partition and scans are lazy. A successful early check need not demand later
primary classifications or selected-class work. Exact source receipts must
retain the reached call order.

`provablyEmpty` explores a local table of at most 1000 admitted closed keys.
Each row requires its original children and one intersection per equality
class. Contradictory rows are omitted. Empty requirements are impossible.
Requirements outside the table remain possible. A synchronous Boolean
operator marks a key when some row has every requirement possible. Iteration
starts from false and stops when the finite key set is unchanged. The source
does not explicitly union the previous set into the next set. Monotonicity
from the bottom derives ascending iteration.

The new class requirements use literal `foldr1 intersect`: `[a,b,c]` gives
`a intersect (b intersect c)`. The reduction helper uses the first item as a
right-fold seed: `[a,b,c]` gives `b intersect (c intersect a)`. Exact language
laws connect both to common membership. Their native calls and allocation
schedules remain distinct. Neither new emptiness fold uses mergeAlternatives.

The budget bounds admitted keys. It does not bound native work. EmptyNode
matching precedes the budget guard, so queued intersection values can still
be demanded after budget exhaustion. Exposure, projection, and intersection
must each complete. An empty start can return without demanding exploration
or the fixed point. A nonempty start omitted from the table can return false
without demanding the fixed point. False proves no accepted witness.

Only Enumeration, Equality/Operations, EqualitySpec, and CHANGELOG change in
the upstream delta: 105 insertions and 24 deletions. Interned constructors,
intersection bodies, equality normalization, Sized, and cfta-generator remain
unchanged. Local package differences from this main are the retained
constructor-probe changelog entry and the standalone caller-repro comment.
All production definitions match this main.

## Additive proof coverage

`EndpointGateModes` proves enabled-mode equality with the stronger gate and
disabled-mode equality with the older gate. Stateful equality retains every
error, pending result, Boolean, and returned constructor heap at each fuel.
This adapter does not retarget the complete class pipeline or its memo calls.

`ConservativeEmptiness` proves monotonicity, ascending iteration, finite
stabilization, stability after extra iterations, and leastness. A complete
finite state list supplies the bound. Empty requirements are false; outside
requirements are true. The one-sided soundness theorem uses independent
accepted finite witnesses with a smaller-witness row decomposition.

`ConservativeEmptinessRows` derives that decomposition. Its rows contain the
original children followed by class requirements in literal foldr1 order.
The primitive laws concern only empty, intersection membership, and projection
coverage. Satisfied nontrivial classes cannot contain the root path. Each
class intersection therefore contains an accepted proper subtree. Original
children also have smaller accepted witnesses. Term height supplies the
induction measure. Physical classification readback and one-level accepted
row exposure then derive Decomposes. The final theorem supplies finite-graph
emptiness soundness without assuming Decomposes or algorithm correctness.

`ConservativeEmptinessExplore` follows the completed-value worklist schedule.
It skips Empty first, then checks budget, existing keys, and closedness.
An admitted row prepends its flattened requirements to the remaining queue.
Lexicographic descent on budget and queue length proves termination. Old
lookups retain their exact rows. Unique keys remain unique. The table grows
by at most the initial budget. Zero budget drains the finite queue and returns
the identical table. Rows, keys, and closure bits are completed input values;
this theorem does not establish native producer completion or runtime cost.

`RefusedEqualityEmptyPass` models the new branch before selected-class edits.
A satisfied nontrivial class supplies an accepted common projection. A sound
emptiness oracle cannot reject that class. Replacing all children by empty
cannot add a forest term. The resulting pass preserves each forest term
satisfying both original constraint sets. This is a conditional primitive
graph theorem. It does not assume correctness of the whole pass. Its oracle
soundness premise still needs the actual per-call explored graph bridge.

The previous endpoint and three-memo proofs remain current components of the
primary path check. The older gate components apply to the secondary policy.
Preserved historical cycle theorems still concern their historical definitions.
No old proof definition changed; Audit imports are additive.

## Concrete source boundaries

The actual IntMap table must supply a finite carrier, exact row readback,
and correct classification. Its key is an untagged machine-Int node identity.
Rec can share a Mu identity. Closedness of every generated requirement,
resident identity uniqueness, no ID reuse, and sufficient machine capacity
must be derived. Tagged logical keys alone do not establish this contract.

Actual nodeEdges exposure, normalized active classes, path order, getPath
coverage, and native intersection receipts must establish the row premises.
General native completion is unproved. Keep InputsThrough, semantic finish
receipts, internal word bounds, sidecar allocation coverage, and the
candidate-parametric Mu/repeated-pair context law as separate obligations.
Global memo ownership, suspended cells, concurrency, finite containers,
unsafe IO, and GHC execution remain source limits.

A temporary boundary probe confirms why normal form is necessary. A nullary
`a` with a class built by mkEqConstraints accepts `a` and is not proved empty.
A raw singleton-root class also accepts `a`, but provablyEmpty returns true.
A raw empty class accepts `a`, but provablyEmpty raises `foldr1: empty list`.
The raw cases violate the documented normalized Constraint invariant. They
are not counterexamples for valid normalized input. Closedness alone is too
weak for a theorem over every raw representable payload.

Probe: `/tmp/mcfta-provably-empty-a22b2ad4-20261015.hs`.
Log: `/tmp/mcfta-main-a22b2ad4-raw-boundaries-20261015.log`.
The closing preservation snapshot retains both. Run with:

```sh
nix-shell --run 'env PATH=/usr/bin:$PATH cabal exec -- runghc --ghc-arg=-package-id --ghc-arg=cfta-0.1.0.0-inplace /tmp/mcfta-provably-empty-a22b2ad4-20261015.hs'
```

## Caller regression and validation

The upstream regression now expects EmptyNode from the fixture's
reducePartially, termsMatching, and README fixed-point composition. Its nearby
withLeaf variant retains an accepted term and the tested bounded language.
The strict Nix build passes all libraries, executables, tests, and benchmarks.
All six suites pass: 697 examples plus the golden suite. Fourmolu passes the
three changed Haskell files. No Cabal metadata changes; the previous metadata
check was not repeated. Sized is unchanged; its separate 205-rank probe was
not repeated. The repository instructions require the Nix validation.

A temporary copy of OuterCallerCycle replaces its identity observer with
`reducePartially root == EmptyNode`. Its fresh-process --cold run prints
`Just True`. The historical repro remains byte-identical. Its old --cold
observer asks for nodeIdentity EmptyNode and raises an observer error. The
intermediate 24a710a3 Just 17 result is historical. Neither the old observer
error nor the obsolete default certificate demonstrates a current cycle.

The full pinned Lean build passes 1,999 jobs. The audit checks 51,206 theorem
dependencies and permits only propext, Classical.choice, and Quot.sound.
No new warning occurs. The old unused-input warning remains. Logs:

- `/tmp/mcfta-main-a22b2ad4-lean-audit-20261015.log`
- `/tmp/mcfta-main-a22b2ad4-build-tests-format-20261015.log`
- `/tmp/mcfta-main-a22b2ad4-caller-empty-20261015.log`
- `/tmp/mcfta-main-a22b2ad4-proof-kernels-20261015.log`
- `/tmp/mcfta-main-a22b2ad4-refused-pass-20261015.log`

The read-only policy and emptiness audits in /tmp preceded the new modules.
Their statements that these new components lack proofs are historical.
Their source-demand and representation obligations remain applicable.

## Next proof target

Connect actual exploration receipts to the completed finite table. Retain
ordered exposure, projection, and native intersection effects. Derive closed
resident requirements and exact untagged identity readback. Then instantiate
the source-shaped row theorem and per-call oracle soundness. Carry both gate
modes and all three memo families through the actual lazy refused-class scan.
Connect that scan to the new pass law and the selected-class fallback.
Whole reducePartially and repeated-pass termination remain open.

Keep the optimized interned core and all older constructor/equality targets.
New derived-refinement frontends, named measures, full causal/pending
correspondence, getAllAtPath, decision-model, parser/decoder bridges, and
extraction remain open. Sized exact node-count classes, finite execution,
canonical sequence, distinct size order, and both signed inverse implications
remain separate contracts. Component proofs and finite examples do not
establish these remaining full-library obligations.
