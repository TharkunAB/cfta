# Independent review of constructed edit resources

Reviewed: 2026-10-16 21:25 CEST.
Final source: `SourceCurrentAllocatedFiniteOrdinaryEditResources.lean`, 443 lines, SHA256 `38e0f21535cf113b198a1fa0eb42ad3fdc07d13fc31b23e772842d603876b3c2`.
Result: no material defect found. No production file changed in this review. No Haskell behavior change is involved.

## Actual construction

The private construction proves three mutually used claims by strong induction on the literal original input size. It has no completed graph, worker success, future capacity, callback result law, or future Ready premise. The only operational producer at a leaf is the existing initial-only SharedLeafResources endpoint.

The proof keeps captured original profile limits separate from the current input limits. A selected child changes the physical heap, inventory, and global bundle. Its original suffix values keep their original profiles and height bounds. Their availability follows from the exact prefix receipt's Keeps. The recursion does not inspect a generated leaf result.

Every row rebuild uses the original symbol and complete raw guard. The original field annotation grows through the actual child-prefix operation growth. The exact child graph length proves the source arity. The literal makeEdge return becomes the next row entry through advanceHeap. There is no MkEdge call, implicit guard normalization, or universal conjoin assumption.

The row profile uses the actual current coherent and cached facts. The ordinary node profile uses actual returned resident rows and current coherent and linked facts. Exact ordered transport proves that the rebuilt row list has the original row length. Constructor filtering and canonicalization cannot add rows. Cache-hit readback is covered by OutputConstructors, not assumed from ID equality alone.

The strong native/output/Merge/slot profile invariant is retained by physical_stored at every raw constructor join. A leaf supplies its changed native and Merge certificates. The weaker FiniteOrdinaryEdits structural store is used only to obtain narrowing; it does not replace the stronger store.

## Counts and cumulative headroom

The source uses ValuePositions for possible leaf calls, including Empty. It uses separate original ordinary-node and edge occurrences for reconstruction. Thus a node-level editAt on Empty can pay for target forcing. An ignored list-root editAt instead returns immediately. Repeated IDs and repeated row positions remain in the conservative input counts.

Each leaf permits the full captured Target cost plus a fixed native query cost. Current slot hits fit that upper bound. The proof needs no distinct-miss count. The captured slot profile remains fixed while the current output profile can widen.

Every Budget contains an actual ConstructorWorkTrace and observed request-count bounds. node_work and edge_work record their literal Work actions. Trace composition preserves the actual intermediate heap and request order. budget_next uses actual trace supply bounds, then additive Numbers identities pay for the next suffix. It does not define work as a counter difference.

The node ordinary case has initial room for both its row traversal and final makeNode. The row case has room for children, its actual makeEdge, and the remaining rows. The selected-child case has room for that child and the unchanged original suffix. Each later call receives the exact prefix heap and derived headroom.

## Four public endpoints

node, children, rows, and list construct their own actual graph, strict Reads, next inventory, final global bundle, and full physical receipt. Their semantic and structural results use the same Reads. Their StableRun uses the same raw graph and complete returned Shared state. Final capacity and both final supplies follow from that trace and the initial headroom.

The public signatures retain legitimate initial Ready, strong Stored, captured availability/profile/class facts, current input availability/profile/height, edit Populated/Allowed/Safe facts, initial global Valid, and initial numeric headroom. They do not take a future range plan or result law. The node endpoint also takes HasLeaf, as required by the existing physical effects API.

The list-root ignored branch constructs the identity raw graph and empty Work trace. Its generic public endpoint still takes the conservative forest headroom; it does not expose a separate minimal-assumption zero-cost theorem. This is a stronger initial precondition, not a false resource conclusion.

Independent conditional language preservation remains available from SharedEditLanguage on the returned Reads and a valid compiled edit. These resource endpoints expose structural NodeNarrow/EdgeNarrow. They do not claim unconditional language equality.

## Validation

- Root canonical `edit-resources-build-6.log`: terminal exit 0, 1368 jobs. Only the historical inputs dependency warning appears.
- Independent imported public check: four complete axiom/signature pairs, terminal exit 0, 2588 log lines. All axioms are propext, Classical.choice, and Quot.sound. No warning, error, sorryAx, or truncated terms appear.
- The independently reviewed source digest is unchanged after the imported checks.
- Root owns substantive execution integration kernels. This review does not duplicate those builds.

The retained internal draft snapshot has its original verified digest ea58c36a. The final internal construction changes only the captured parameter name from rows to rowLimit before the added public wrappers. Historical draft evidence stays unchanged. An exact old callback-counts snapshot is also retained because that separate producer continued to change after the draft review.

## Remaining scope

The theorem covers finite ordinary inputs with unrestricted full guards and class data subject to the explicit initial class facts. It excludes Mu, references, and explicit union throughout those input profiles. It accounts for constructor Work requests and constructor supplies. It does not establish equality-interner capacity, whole host instruction cost, GHC forcing correspondence, repeated outer-pass bounds, or whole-library completion.
