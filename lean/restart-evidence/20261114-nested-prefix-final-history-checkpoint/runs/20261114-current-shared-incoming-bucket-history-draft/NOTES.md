# Raw bucket history at a shared incoming write

Status: UNCOMPILED CANDIDATE. The root owns validation and publication.

Public candidate:

`MicroCFTA.SourcePruningEnumerationSharedIncomingNode.singleton_bucket_history`

The input is an ACTUAL supplied-bound successful `SharedIncomingNode.run`
singleton. No validity, semantic assignment, finite-model, native-capacity,
old-bucket or ancestry-source hypothesis is supplied. The theorem inverts the
actual operation and derives:

- Its actual `findRoot` result and canonical target.
- The complete old payload and raw bucket at that target in the original Core.
- The exact read Core produced by that lookup.
- The complete written Core, with `incomingScs ++ oldScs` stored at the same
  canonical target.
- The actual stored bucket after the write.
- Exact ancestry membership: a key at the written target comes from the
  original active ancestry or that target's original ancestry.

The list equality preserves the old bucket as an ordered suffix. Every old
raw target, complete trie and duplicate occurrence remains literal. This is
an operation receipt before any later clear. It is not a conditional model
restatement. It applies to first assignments and native merged assignments.

The existing native observer has an unchanged-caller disjunction. That branch
does not export the full bucket receipt. The source-goal first-assignment
theorem supplies source certificates for an original `None` slot. This result
supplies a separate general structural receipt for any successful shared
incoming slot. The pure write helper remains private.

## Actual shared clear audit

The actual selected-prefix recursion test is the same literal operation for
both shared recursive drivers. This is not a legacy-native equivalence:

1. `SourcePruningEnumerationSelectedStep.runPrefixWithNarrow` calls
   `SourcePruningEnumerationRecursion.checkRepeated` on its actual value read.
2. `checkRepeated` tests the native recursive boundary and the current
   canonical target's ancestry. On a repeated key, it executes
   `setValue root (.unenumerated (some handle) [])`.
3. `SourcePruningEnumerationParkedRestart.adapt` removes the old raw bucket's
   waiting counts and keeps the actual checked Core.
4. `SharedRecursive.resume` and `SharedPreparedRecursive.resume` take the
   literal parked restart. They do not call `continueWith` for this cleared
   slot. The earlier completed expansion owns its Left callback.

Source locations at the pinned versions:

- `EnumerationState.lean:56`: `RecursionKey` stores a node and path sets.
- `EnumerationState.lean:62`: `recursionKey` omits `sc.var`, removes duplicate
  path sets, and sorts the resulting path sets.
- `EnumerationState.lean:126`: `inheritAncestry` copies keys from active
  ancestry. It adds no raw target or bucket record.
- `SourcePruningEnumerationRecursion.lean:16`: `checkRepeated` performs the
  actual empty-bucket write.
- `SourcePruningEnumerationSelectedStep.lean:58`: the true check builds the
  parked result.
- `SourcePruningEnumerationSharedRecursive.lean:153`: the parked singleton
  directly resumes.
- `SourcePruningEnumerationSharedPreparedRecursive.lean:144`: the prepared
  driver uses the same parked restart.

## Precise remaining relation

The new write receipt preserves an old raw bucket across one actual incoming
operation. Its ancestry equivalence can identify which earlier active or
target history supplied a repeated key. Existing Entry origin producers can
identify the original full bucket when an ancestry key is first entered.

Those facts do not identify a later cleared bucket with an earlier processed
bucket. The missing producer must follow the SAME actual branch through its
entry, preparation, path descents, fresh allocation, shared fold, incoming
writes, aliases, finalization and restart. It must retain each removed raw
target and each complete path occurrence. Equal keys provide only equal
deduplicated path-set collections, not a raw target map or an occurrence map.

The existing final child aliases and terminal observer cover the original
terminal bucket of an ACTUAL earlier child call. Applying them to a later
clear still requires the actual relation above. Proper paths also require the
actual descendant calls. A post-state lookup cannot recover the erased raw
bucket by itself. The source does not retain that raw bucket in an ancestry
key or in the `parked` constructor. This is a proof extraction gap. It is not
an accepted-source failing trace or a demonstrated Haskell defect.

## Full objective retained

The MAIN target is still ONE finite accepted completion of each actual emitted
partial term for the SAME original root, under ONE assignment satisfying all
retained constraints and all historical removed obligations. It retains the
original same-source initializer, identity/no-stop worker, paths, domains,
aliases, residuals and actual partial readback. The target and initializer are
pinned in `SOURCE-SHA256SUMS`. No new postModel-to-removed-Holds premise replaces
the missing relation or the finite assignment.

The full objective also includes typing and depth adequacy/completeness,
preprocessing/LPO in both directions, exact stream order, multiplicity and lazy
demand, exact accepted terms at each size, counts, weights/training, both rank
inverses, host bounds and compiled Haskell correspondence.

No Haskell, live source, Git, board, compiler or temporary data changed.

```lean
#print axioms MicroCFTA.SourcePruningEnumerationSharedIncomingNode.singleton_bucket_history
```

Strict elaboration and standard-axiom checks remain pending.
