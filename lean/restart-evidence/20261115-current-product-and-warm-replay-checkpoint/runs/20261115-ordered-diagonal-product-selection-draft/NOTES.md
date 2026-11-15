# Ordered diagonal selection from the actual finite product rows

Status: UNCOMPILED CANDIDATE. Root owns validation and publication.

One reusable public theorem consumes literal Kernel.pairs sources sources and
an actual ordered All₂ row law against rawResults. The stronger row law is:

```
(pair.1=pair.2 -> relation pair.1 row) and
(pair.1!=pair.2 -> row.children=[empty])
```

The weaker disjunction from the initial task is not used. It would permit a
self pair to return only a sentinel and provide no related diagonal target.
The actual source query proofs must supply this stronger local classification.

Additional assumptions are finite and scoped to the given lists:

- SAME heap and Facts; every raw result is EdgeResident in that heap.
- For a source in sources and two related targets in rawResults, functionality
  identifies those COMPLETE target rows.
- A related target in rawResults for a source in sources belongs to the actual
  surviving rawResults list.

The proof derives a selected list in ORIGINAL source order. All₂ retains one
target for EACH source position, including duplicate occurrences. It also
returns selected membership in rawResults, selected residency in the same heap,
exact full-row membership equivalence with surviving rawResults, and
canonicalEdges(surviving rawResults)=canonicalEdges selected.

Construction and existing APIs:

1. Kernel.pairs_member proves that every literal (source,source) diagonal is
   present in the actual equal-symbol product.
2. Existing BinderSchedule.related_target extracts its actual ordered result
   from All₂. The self implication supplies relation without a witness oracle.
3. A small PRIVATE list induction constructs the selection in original source
   order. It does not assume a selected product, canonical equality, or a model.
4. Existing BinderSchedule.related_origin identifies the original pair of any
   surviving raw target. Its non-self implication would give the literal empty
   child and contradict survival, so the pair is self and relation holds.
5. Scoped functionality identifies that target with its selected diagonal
   target. Scoped liveness proves the reverse membership inclusion.
6. Existing InternedNodeSetCongruence.canonical_same uses the SAME heap's
   coherence and both resident lists. No heap replacement or future growth is
   assumed. Standard classical logic supplies the finite equality case split;
   there is no new axiom declaration or extra DecidableEq Guard requirement.

BinderSchedule's two public generic All₂ membership helpers are reused. Their
list proofs are not copied. No current-source, native execution, warm-cache,
source-P, history, or semantic completion condition is added to this algebraic
lemma. Root still must derive functionality/liveness and the strong row law
for the actual substitution readback at its real common heap.

The original full/coupled goal header is copied byte-for-byte. This finite-list
bridge does not prove cache-history correctness, global native closure, or the
same-root finite joint witness. It does not choose or splice semantic models.
No live code, compiler, Git, board, Haskell, or /tmp operation was used.
Stop after this bounded packet as requested.

Validation: normal dependency build, then strict-check a private source copy
with the import-free PROBES fragment. No credit before successful elaboration
and a standard-axiom report.
