# Independent current caller graph review

Reviewed SourceCurrentAllocatedPartialGraph and its current state/prefix/rebuild
definitions against cfta/src/Data/CFTA/Equality/Operations.hs:76–96,145,160–168.
No ordering defect was found in the completed serial graph.

NodeCall and EdgeCall use separate tables. begin publishes before demand.
Evaluation uses the captured original request selected by demand, not a later
alias candidate. The body result reaches the same finish handle. Busy and
absent outcomes have no successful call constructor. The graph alone does
not prove that every request completes or that warm cells have source origins.

Ordinary source rows run reduceEdgeIntersection, then reduceChildren on the
returned edge, then the remaining row list. The graph preserves that order.
ParentEdge tests raw contradiction before local child work and invokes the
actual checked constructor afterward. Descendants reads the returned raw
constraint, combines inherited first and own second once, then performs each
actual indexed descent before the recursive NodeCall. This distinguishes the
inherited-first operation key from the local precheck's own-first key.
Inherited contradiction skips own access and all child calls. The walk and
Children length theorems justify the later raw same-arity setChildren branch.

modifyNode retains the literal ordered edge identity comparison and raw node
constructor. The Mu body correctly records literal MuReconstruction.rebuild
completion. The bidirectional Mu pattern uses createMu (Interned/Type.hs:674–676),
so an unconditional identity branch would be incorrect. No such identity
shortcut is present. Raw Rec has no successful body, matching the source error.

The graph retains exact checked, merge, fourth, and both caller-result tables
through advance. Three global memo bundles are separate indices in the new
Reads graphs. Constructor and equality prefixes do not replace those tables.
Protected running-cell retention, physical validity, warm semantic cell laws,
and global heap coherence must still be proved from actual initial invariants.
They are not graph premises or established by the read schedules alone.

Remaining source bridges include mutable typed cache/key correspondence,
first-writer publication and winner reread under concurrency, GHC thunk forcing,
the actual outer recursion completion/rank, machine identity capacity, and
ordered map/list demand. The graph is not a literal executable-worker or host
runtime correspondence theorem. General binder origin/cleanliness and its
global-event operational adapter also remain explicit.
