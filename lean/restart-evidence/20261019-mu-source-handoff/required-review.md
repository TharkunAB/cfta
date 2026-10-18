# Required primary retention boundary

The selected production source is `SourceCurrentRequiredPrimaryRetentionBoundary.lean`, SHA256 `3e3fd6228c3533d377493266efc40dae2ee73ffa496c4f4ae112e7ee8d195091`.
The sole public head is `SourceCurrentRequiredPrimaryRetentionBoundary.required_changes_primary`.
It has no caller premises. It constructs all witnesses.

The actual source is the raw binder `mu x. outer[union[x,leaf],leaf]`.
Every row has empty own equalities and a top Boolean guard.
The selected record has paths `[[0,0],[0,1]]`.
The proof derives record coherence, two distinct paths, and an actual normalized result from `mkEqConstraints 4`.
Here `4` is normalization fuel, not an arity bound.
The source produces a closed Mu with a self occurrence in its stored body and `usesLocal = true`.

The proof derives the initial `SemanticReady`, cost heap, union normality, causal plain guard heap, and input availability from the literal source construction.
The original primary class returns false and supplies the exact false `ClassTrace`.
The literal `requireAll 8 8` returns successfully.
It exposes the ordinary body and retains the selected closed union endpoint.
The primary class on the returned forest returns true.
Trace uniqueness excludes a false class trace at that same final heap.
`SourceCurrentRequiredEndpoints.selected_paths_closed` derives `ForestClosed` for both original paths at the returned forest.

This refutes false-primary retention through Required on normalized active records.
It does not assert that this record was returned by an actual allocated Scan call.
It does not refute Required language preservation or structural guard origins.
It establishes no Haskell defect, infinite execution, or final Parent acceptance.

Selected evidence:

- `required-direct-7`: exit 0; raw strict log is exactly zero bytes.
- `required-canonical-1`: exit 0; the target builds. The log replays one unchanged warning from `InternedFreshOrdinaryClosedCompletion.lean:24:5` about unused `inputs`.
- `required-public-1`: one complete public signature/proof/axiom pair; all eight print options; no omissions; only the standard three axioms.

All twelve owned Lean runs retain immutable source snapshots where applicable, logs, metadata, effective memory limits, and peak records.
The first three boundary runs test missing paths, accepted plain Mu exposure, and mixed ordinary/Mu paths. The third also verifies the two-path gate-change example.
Production direct attempts 1 through 6 retain the local elaboration and simplification failures. They are unselected.
The production source is unchanged after direct attempt 7.
No additional selected fixture is needed: the public production theorem is itself a source-built constructive boundary witness.
