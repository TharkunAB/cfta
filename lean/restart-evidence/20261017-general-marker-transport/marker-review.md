# General marker transport

Reviewed and frozen on 2026-10-17 at 03:46 CEST.

The source is `SourceCurrentConstrainedCapMarkerTransport.lean`.
Its SHA-256 is `a3588e24128d5478d6ffebf8778b15c5eef5ab119443c42f721c23b000e073cc`.
The final source has 264 lines. `marker-final.source.lean` retains the same bytes.

## Result and premises

`transport` at source line 209 proves general free and deep occurrence transport through the actual stored substitution. Its conclusion concerns the value at the supplied `.done value after` return. The marker receives the old reference's weight. The proof needs an initial `Context`, a `DepthHeap`, availability of the body and marker reference, an input `Classified weight bound body`, `weight old = bound`, and marker freshness in the body's free names. It accepts every natural bound, including zero. It does not assume the output classifier, a guard cap, a completed native query, or a callback result law.

`callback` at source line 234 proves the same classifier for the actual normalized `SourceRecursiveIntersectionMaybeMu.callback` return. It inverts the literal raw substitution, derives the raw classifier with `transport`, and applies the existing self-reference filter theorem at the actual intermediate heap. Pending raw substitution cannot satisfy the supplied callback success equation.

The body can contain arbitrary stored ordinary, union, and Mu records. This theorem has no restriction to direct union recurrence. The theorem is a preservation result for a supplied actual return. It does not construct general substitution or native-query completion.

## Proof checks

The proof classifies the encoded stored plan. `encoded_free_support` uses indexed input origins and literal stored-plan encoding. Every returned free name comes from an original free name, with only the requested old-to-marker replacement. Captured closed values add no free names.

For ordinary and Mu inputs, all free names already satisfy the deep bound. General free support therefore proves the output bound even if smart reconstruction changes the record or the cached depth. Root unions need recursive member classification. The mutual proof follows the literal stored-plan members and uses their actual source availability and free-name readback.

`InternedRecordDepthExecution.build_depth` and `InternedRecordDepthSource.source_free` transfer this pure plan result to the same actual returned record. These results include the current depth/free readback for warm canonical winners. The proof does not replace a warm winner with a newly computed candidate. It does not transfer a result from a historical eager executor.

Old-reference absence does not imply unchanged identity. The stored executor shortcuts a closed value. An open ordinary or Mu value can reconstruct even when the replacement does not occur. The integration below tests this distinction.

## Validation

The absolute-path strict source check passed with no output in `marker-direct-5.log`. The canonical build passed all 1009 jobs in `marker-canonical.log`. That build replayed only the historical unused-variable warning in `InternedFreshOrdinaryClosedCompletion.lean:24:5`.

`marker-public.lean` checks both exported theorems. `marker-public-1.log` contains two explicit full-signature and axiom pairs. It has no diagnostic, truncation, or `sorryAx` entry. The dependencies are the standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

`marker-kernels.lean` contains three integration pairs. `marker-kernels-6.log` passed with no diagnostics or `sorryAx`.

1. `constructed_open_mu_reconstruction` has no premises. It constructs the closed nested-binder source expression from an empty heap, extracts its actual open inner Mu, and executes the actual stored substitution. The observation proves that the record identity changes and the cached depth changes from one to zero. The kernel derives the initial and returned classifiers from those actual construction facts.
2. `general_warm_replay` accepts one actual general stored substitution. It derives the returned context, depth heap, and retained original inputs. It constructs a second literal execution with the same value and the same whole returned heap. It then applies `transport` again at that warm entry. No second success or intermediate classifier is a premise.
3. `actual_normalized_callback` accepts an actual raw substitution. It constructs the literal normalized callback result, derives its classifier, and proves that a marker of positive maximal weight is absent from the returned deep names. No callback success or returned classifier is supplied.

All failed source attempts and their raw logs remain under the `marker-*` prefix. The final component manifest pins those artifacts without replacing them. No old proof source, Haskell source, Git state, or `.olean` file was modified by this component owner.

## Remaining boundary

This module closes general marked free/deep transport through actual stored substitution and normalization. Guard-cap transport, actual warm-Mu cleanup, finite callback construction, and native returned-cell occurrence installation use separate proofs. This module alone does not establish general recursive native completion, selected-class closure, machine capacity, or GHC runtime correspondence.
