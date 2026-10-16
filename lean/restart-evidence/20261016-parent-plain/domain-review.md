# Independent returned-domain review

Reviewed at 2026-10-16 15:26 CEST. No material defect found.

Reviewed source: `SourceCurrentAllocatedPartialReturnedDomain.lean`, 175 lines, SHA256 `a012277ccf471b8d3354f9bdc5bac704f0f1c8d0d33149fb4dcf9a4fcedb6429`.

`Shape` at lines 26–28 has exactly three child-list cases: original children, erased original slots, and the singleton Empty sentinel. It makes no guard, language, arity, or heap equality assertion. `Shape.regions/child_region` derive actual returned-child Regions. `Shape.height` derives the original edge-height bound, including zero-height nullary input to one Empty child. These results use the actual stored owner edge. They do not infer structure from EdgeLaw.

`Stored` at lines 82–83 requires Shape for every returned edge cell and its captured original request. This is a meaningful additional warm-cache domain. It is not derived from arbitrary Context or semantic result laws. Initial empty outer tables derive it over arbitrary supplied checked, merge, and fourth state. Later completion must derive it at each new edge finish. The module correctly leaves the general constrained result-shape law open.

The lifecycle laws at lines 93–154 are physical and structural. Checked advancement, node publication, and node finish leave the edge table unchanged. Edge lookup and demand create no returned cell; the private reverse Returned lemmas prove that every later returned cell was returned earlier. They need no Protocol because they do not promise forward survival of overwritten cells in malformed tables. `Stored.finishEdge` requires the actual selected evaluating cell and a local Shape for that exact owner/result. It installs that result at the same handle and preserves all other completed cells. It assumes no future cache validity, body result law, or completion callback.

`Stored.bounds` is the correct weaker consequence. `Stored.child` reads the exact returned owner cell and combines its Shape with Regions of that owner's original children. It derives both Region of the selected returned child and strict node-rank descent below that original edge request. It neither substitutes an arbitrary candidate request nor assumes all returned children are original children.

All thirteen public axiom/full-signature pairs and the two definitions passed independent imported checks. Five integration kernels passed:

1. Original child shape transfers Regions and the height bound.
2. Erasure derives Region children without requiring Region for the original slots.
3. Nullary input to singleton Empty sentinel has Region, equal edge height, and strict empty-child rank descent. Its returned arity differs from the original arity.
4. Actual edge publication, a completed parent body, and exact owner finish preserve Stored and install the exact original request's returned cell. The separate forward Protocol frame proves owner survival; Stored itself does not supply it.
5. A literal zero-bound warm hit skips the body and retains the whole caller. Its actual captured owner's Shape and child domain transfer to a coherent resident candidate by the stored key and immutable operand equality. No candidate Shape or desired result language is assumed.

The pure shape kernels use immutable records. They claim no host allocation receipt. The two lifecycle kernels use actual caller publication, graph, finish, and literal worker operations. Final direct runs returned exit code 0 with no warnings, errors, or `sorryAx`. Only `propext`, `Classical.choice`, and `Quot.sound` occur.

`region-next-review.md` maps the remaining joint completion induction. In particular, cache Shape belongs to the parent EdgeBody result before descendant traversal. The later raw rebuilt row is not that edge cache entry. The next proof must derive actual recursive graph completion and Stored after each reached prefix; this module alone does not prove those facts.
