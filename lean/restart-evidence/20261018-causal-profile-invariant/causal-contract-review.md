# Causal stored-profile contract audit

Reviewed on 2026-10-18 at 18:47 CEST. This is a read-only source and receipt review. It adds no Lean declaration, proof pair, fixture, or build.

The new per-payload contract and its actual execution bridge have no material issue. The general publication law remains unproved. The new contract does not reinstate the refuted all-Context Fusion conjecture.

## Exact contract and bridge

`StoredProfileFunction.denote value assignment` evaluates the full stored encoding. It assigns a profile to each reference leaf. It keeps the actual profile of every other closed leaf. `StoredMuProfileContract.shadow name local assignment` changes only `name`.

For the exact stored payload `mu entry body depth ordinary`, the contract is:

```text
Correct entry body depth ordinary :=
  forall assignment local,
    Equivalent
      (denote body (shadow (interned entry.identity) local assignment))
      (denote ordinary
        (shadow (uninterned (ordinaryLevel depth)) local assignment))
```

This predicate has no heap parameter. The assignment and local profile are arbitrary. It assumes neither a desired output relation nor a later reader. It does not state that arbitrary resident payloads satisfy the contract.

The checked `execute` theorem accepts the same outer replacement map and the same complete local replacement on both sides. The two initial heaps can differ. Each heap must be Ready, contain its original payload, and make the replacement inputs available. Each literal execution must complete. Returned heaps can differ. The proof derives replacement availability for both local maps, rewrites their resolved profiles to the exact shadows, and composes profile equivalence. It does not assume that either execution is warm or that either returned heap satisfies a future law. See [the contract and bridge](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentStoredMuProfileContract.lean:21) and [the stored execution bridge](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentStoredProfileFunction.lean:132).

No cross-absence condition is needed for these two single-local maps. If a later caller uses the shared map that binds both local names, it must derive actual cross-absence and use `StoredProfileFunction.congr` to remove the irrelevant override. The contract does not assert physical value equality, row matching, or all-depth observation equivalence.

## Minimum supported source relation

Keep one common symbolic lexical list: fixed complete records and varying reference labels. Keep its original source shape. Let `S = NativeNormalizationInputs.support expression inputs`. A sufficient proposed profile condition is:

```text
forall name, inl name in S -> rhoLeft name = rhoRight name
forall atom, inr atom in S ->
  rhoLeft (leftNames atom) = rhoRight (rightNames atom)
```

Exact equality suffices for the proposed publication comparison. An extension to equivalent assigned profiles needs a separate evaluator-congruence proof. This report does not assume that extension.

Use `support`, not syntactic `Uses` and not every lexical slot. An actual ordinary marker can equal a name in an unused capture or a discarded source row. A condition on all lexical slots would add an unsupported freshness requirement. `NativeNormalizationInputs.actual_free`, `fixed_origin`, and `ordinary_fresh_fixed`, plus `NativeNormalizationFreshness.ordinary` and `reserved`, state the existing actual support facts. `StoredProbeCompatibility.extend` is the exact-value template for a pure profile extension.

Keep the existing `Aliases` on `Scope = Depth :: support`. Keep the scoped local self tests. Assigned profile equality does not preserve the original reference alias classes. `UsedBinderAliasTransport.extend`, `extend_depth`, `extend_fresh`, and `publication` handle the original aliases. `NativeNormalizedComparison.capture_support` transfers old support under a new local. These facts permit binder entry without freshness for unused captures.

For node syntax, restrict the condition only to children of original live source rows. `StoredLiveSourceLineage.child_compatible` shows the needed support inclusion via `evaluateEdges_member`. Dead original rows need no child relation. For union syntax, `evaluateMany_member` gives member support inclusion.

## Concrete proof order and remaining obligation

A proposed source lemma compares two actual builds of the SAME source expression, at their actual entry and return heaps. It retains their common symbolic lexical list, original aliases, scoped self tests, and the support condition above. Its conclusion compares the denotations of their actual root-filtered results. Its cache hypothesis is the new Correct predicate for selected resident recursive payloads. It must cover arbitrary nested source binders.

This source lemma needs exact filter control. Equivalent raw profiles alone do not identify a bare own reference or a union that contains one. Use `UsedBinderOutputTags.bare` or `scoped_bare` to derive the bare-self branch. Use `FilteredUnionCoverage.parts` for the exact retention rule `member != bareOwn OR parent = bareOwn`. Do not filter assigned profile names a second time after reconstruction.

One possible noncircular organization is a syntax induction for that binary source lemma, with Correct heaps at the actual returned cuts. The binder case uses the exact selected payload and its stored Correct proof; it also retains the actual current probes and finish branch. Selected old payloads need not have the current source syntax. Actual growth can transport the payload lookup forward to a returned cut. This is not a backward inference of publication history.

Then `PublicationHeapInduction.path_heap` supplies Correct heaps at the exact callback cuts. Its publication obligation receives the invariants at `before`, `afterDepth`, `cut`, `allocated`, and `afterBody`. Apply the binary source lemma to the strict source body callbacks, with actual local freshness and filters, to prove the candidate Correct BEFORE installation. The reserved outer payload is not yet installed at `afterBody`. Actual lookup and completion then retain an older winner or install the proved candidate. This is a proof plan; the binary source lemma and general publication step are not yet checked.

The exact outstanding publication theorem has the existing `path_heap` obligation shape:

```text
forall event,
  Heap Correct event.before -> Heap Correct event.afterDepth ->
  Heap Correct event.cut -> Heap Correct event.allocated ->
  Heap Correct event.afterBody ->
  Correct event.entry event.body event.depth event.ordinary
```

The generic chronological induction already proves preservation conditional on this obligation. It does not derive the obligation from Context, Ready, or an actual publication alone.

## Closed and raw binder boundary

The stored interpreter freezes a value with empty original free support as a captured constant. A closed Mu stays opaque. An open stored Mu is encoded as a SMART binder, even if its original source constructor was raw. Thus `denote (actual raw build)` cannot in general be replaced by `evaluate originalSourceSyntax` under new assignments. For example, an open raw Mu whose body is an external reference can become Empty under an Empty external assignment; the original raw source binder interpreter is opaque. This is a direct distinction between the two definitions, not a newly checked counterexample to the new Correct predicate.

The proposed source proof must distinguish original closed/open records, smart used/unused finish, and raw retained binders. Existing `NativeNormalizedComparison.probes_same` provides the current used-local branch comparison from actual probe calls. Prior cache Correct must supply the selected older writer's semantic body/probe relation. No complete general source or binder theorem follows from these supporting modules yet.

## Validation and exact pins

The review reuses selected strict, canonical, and full-public receipts for StoredProfileFunction (six heads), PublicationHeapInduction (seven heads), and StoredMuProfileContract (three heads). Each selected strict log is zero bytes. Each canonical build succeeded without a warning. Each full group has all eight print options, complete statement/proof/axiom pairs, and only the standard three permitted axioms. No new Lean runs or proof pairs were added. The selection and manifest record the exact source hashes and receipt files. No mutable root runner, worker, peaks, fixture, or shared selection is pinned.
