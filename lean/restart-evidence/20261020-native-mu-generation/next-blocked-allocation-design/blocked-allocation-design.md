# Pending optional operation with a new nested Mu

Design status: uncompiled and uncomputed. Prepared on 2026-10-20 at 18:11 CEST. No Lean job belongs to this package. The actual equations below are proof obligations, not established facts.

## One candidate and one reservation offset

Use the fixed native Symbol and Guard. The source has one available lexical input, `reference (intersection 0 1)`. Build the following source from the empty constructor heap:

```
node outer7 [raw mu y. node inner8 [var 1, var 0]]
```

The inner binder is raw and uses its own local reference. Its outer capture is the actual pair reference. The returned outer node is open. Its inner Mu is a complete actual source record. Derive body availability and the rich source Context from the actual source build and available pair input.

Let `reserve heap key` change only `heap.nodes` to `(Cache.intern heap.nodes key).2`. Let the oracle heap reserve `.empty` on the base heap. This candidate schedule uses ordinary `.node` and `.mu` requests. Empty ordinary constructors use the literal Empty fast path. The dummy `.empty` key is intended to be absent and unqueried. Check that property; do not infer it from arbitrary reserve validity.

Run the actual normalized Depth callback on the oracle. From its completed value, compute `ordinaryLevel`. Run the actual normalized ordinary callback next. Define `outerKey` to be `muKey oracleDepth oracleOrdinary`. This definition uses two finite actual operations; it does not refer to the later real call or assume a fixed point.

The actual warm entry reserves `outerKey` on the same base heap. Prove that the dummy key and outerKey were both absent at base. Each reservation must consume exactly one next node identity. Their issued maps and tables differ at that reservation. Their heaps are not equal. No future callback result equality follows from Context.reserve or from equal counters.

## Staged checks after canonical GO

1. Compute the base completed source call and its returned body shape. Derive the base rich Context from that call. Derive both reserved contexts with `Context.reserve`. Derive body availability from actual physical and issued reservation growth.
2. Compute both oracle callbacks. Retain their actual completed values and adjacent heaps. Compute the outerKey from these two values.
3. Compute both actual callbacks from the outerKey-reserved entry. Check exact value equality with the oracle Depth and ordinary values. Check the concrete lookup branch for each intervening request. In particular, no intervening nested request may hit outerKey. Equal next counters alone are insufficient.
4. Select the literal inner Mu child of the actual Depth result. Retain its complete entry/body/depth/ordinary payload. Check that its key is absent at the actual warm entry and contains the same complete payload at the actual final ordinary-callback heap. The pair substitution must change this nested key from the base source key; no desired inequality is assumed.
5. Check that outerKey is still reserved with no nodeRecord at the final ordinary-callback heap. Rewrite the actual optional call through the two completed callbacks and the literal request hit. It must equal `pending outerKey afterOrdinary`. Check that its state contains the selected new inner Mu.
6. Build the checked caller-written control `pureWork; optionalBinder pair body; pureWork`. Derive its current physical InputsThrough plan from the actual body availability and literal step equations. At bound 3 the first pure Work yields, the optional call returns blocked, and the final pure Work is not executed. Retain the exact blocked reason, unchanged optional control and checked native advance. The selected target must be absent at the checked entry and present at this blocked execute state.
7. Apply the official stopping-generation execute theorem once after canonical GO. Eliminate its initial-cell arm with the actual absence. Retain the same recovered site/call/checked mapping/resume/count and generated build/Rooted Written tuple. Do not construct a parallel desired site.

If any callback or lookup check fails, retain the failed calculation and exact branch. Do not change the example into a prior completed-operation specimen. There is no broad search matrix.

## Scope

The proposed initial heap contains a deliberate valid orphan reservation. It is a warm model state. It is not a closed fresh-empty native execution or a Haskell reproduction. Rich Context permits such a reservation; it does not supply complete-table coverage. The desired result is a concrete model example where terminal pending work installs a different complete nested Mu before it stops.

No compileMu owner, compiler source ancestry, writer uniqueness, global cache completion, fixed-point/profile identity or termination statement follows from this design. The native control is caller-written. The same-call generated rooted writer comes only from the actual stopping-generation theorem, if its premises and all listed equations are checked.
