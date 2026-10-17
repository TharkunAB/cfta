# Independent Cap and projection review

Reviewed: 2026-10-17 02:08 CEST.

Result: PASS. No material mathematical or actual-state correspondence defect was found in the reviewed sources.

## Exact sources and local invariants

- `SourceCurrentConstrainedCap.lean`: SHA `9476718c37ef698ca9ffb09412f6a358ab6af7bb98b072835eb214f3e747be5a`.
- `SourceCurrentConstrainedCapProjection.lean`: SHA `a130617097a3c4cde9e031e69e08c49588cde99fa4580744b25dc12428f7da8a`.

A positive ordinary cap ignores that layer's complete guard and requires a smaller cap on each ordered child. Mu enters only through the hereditary case. A stored union keeps the cap on each alternative. `Cap.annotated` proves that cap zero equals hereditary annotation, including union alternatives. `Cap.mono` adds ordinary constrained layers without converting an unconstrained reference into evidence about its dereferenced body.

The actual constructor laws use physical coherence, cached child readback, or resident canonical rows. `makeEdge` recovers the exact full guard and child list. Guard validity is required only at depth zero. `makeNode` restricts its proof to surviving canonical rows, then uses complete row readback for a canonical hit. `makeUnion` covers empty, singleton, ordinary concatenation, and stored-union outcomes. It does not assume that arbitrary numeric identities carry the desired cap.

## Actual projection and depth arithmetic

The `read` theorem consumes the supplied actual read. `readAll` visits each original value at the prior read's actual returned heap. `union` uses that same row list and literal node reconstruction. Mu storage follows the same states. These steps require no `CostHeap` or global annotation-heap premise.

The mutual Project/ProjectRows proof quantifies over depth. Selecting an ordinary child changes depth to `depth - 1`. A child Project of path length `k` returns cap `(depth - 1) - k`. The enclosing ordinary Project has path length `k + 1`; truncated natural subtraction makes these bounds equal. A recursive Mu or union head keeps both remaining depth and remaining path. It does not consume a path index during head normalization. The local exposure theorem supplies the cap and Mu store at that exact head return. The suffix row proof receives physical growth from the selected child's actual prefix and retains the original suffix cap facts.

The forest offset is correct. `Forest []` executes source union and retains depth. `Forest [index]` selects an original root and retains depth. The first forest index is not an ordinary child selection. A forest path of length two consumes one ordinary layer. Thus the general result is `depth - (path.length - 1)`, with natural subtraction also handling the empty path. Missing signed indices return the actual Empty value. They do not impose an artificial range or arity condition.

`complete`, `complete_endpoint`, and `forest_complete` construct their own graph from legitimate initial semantic readiness, availability, closedness, causal Mu storage, and cap facts. They apply cap preservation to the same graph and complete returned heap from the existing finite path theorem. No second projection, output replacement, future result law, or supplied completed enclosing query is used.

## Independent imported checks

The final public probe contains 22 axiom/full-signature pairs: 13 Cap declarations, including its two predicate definitions, and nine Projection endpoints. It passes with exit 0. It emits no warning, error, `sorryAx`, or truncated term.

Two substantive imported integration kernels pass with exit 0 and no diagnostics:

1. The first builds literal raw recursive source syntax `binder false (node [good [var 0]])` from the empty constructor state. It then runs actual `makeEdge symbol bad [recursive]` and `makeNode [row]`, with `valid good` and `not (valid bad)`. It derives the shell cap from the exact returned rows and children. It records the returned row's complete bad guard. It constructs its own finite `[0,0]` projection and stable literal worker run. The same actual return has both `MuStored` and hereditary annotation. No completed projection or desired cap object is a public premise.
2. The second constructs `Forest [0]` and then `Forest [0,0]` at the first actual returned cache. It derives cap one for the first result and hereditary annotation for the second. The second call obtains readiness and retained original availability from the first returned physical facts.

The copied canonical projection build completed successfully. The root reports aggregate Audit PASS 2742 jobs / 62061 dependency checks. The independent probes import the canonical final source artifacts; they do not run Lake or modify production modules.

## Scope

This closes finite signed path projection and cap preservation for the stated local closed inputs. It allows finite constrained ordinary shells above hereditary recursive source values. It does not establish that arbitrary selected endpoints meet the depth condition. It does not establish cap closure for a native intersection of positive-depth operands. Target composition, selected-edit mask preservation, broader recursive completion, machine headroom, and Haskell lazy-runtime correspondence remain separate obligations.
