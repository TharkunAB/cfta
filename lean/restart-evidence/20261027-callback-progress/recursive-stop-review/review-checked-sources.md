# Checked source review

CLEAR for the two installed sources. This review remains open for the public readback and final documents. It does not claim an archive or publication result.

| Source | SHA256 | Actual Root strict check |
|---|---|---|
| SourcePruningEnumerationNativeProgress.lean | `15ea08bbe764cede05fd8f811da2fcb669bf079b956990351b4238e3d52d6343` | native-progress-strict-2: exit 0, empty raw output, warnings as errors, all linters, 4 GiB, swap 0 |
| SourcePruningEnumerationCallbackProgress.lean | `6cb988bf498cc19c8138ffa73a7be3d975a61a0389dff09eda635d3bb5dd8efb` | callback-progress-strict-1: exit 0, empty raw output, same limits |

The installed sources are byte identical to these successful strict snapshots. The native installed dependency build passed with 1360 jobs. Its 558-byte raw output has SHA256 `fcd4a031dd2be673394bb83f9c0a63c0bf1c1db83fffbd8ef8061c14eecda6c4`. No compiler or build was run by this reviewer.

The native proof uses the actual cached candidate flags and canonical waiting support. Each blocked target has a stored referring slot. ProperState excludes pure-none referring buckets and supplies a nonempty strict descendant path. A decoded native slot with a nonempty bucket is itself a candidate, including Mu and Union slots. The assignment's forest equality identifies the referenced target term. Suspended.Holds supplies strict descent. The finite strict-dependency lemma gives a contradiction. No Graph interpretation is fabricated, and arbitrary residualMeaning is supported.

The callback proof calls callback_complete_semantics once. It retains the whole old packet in one conjunction. Independent literal recovery gives the exact old 2032-byte declaration, SHA256 `874e0ac089c46007fe07d66015b4f968b6166841e69876422626ba8ba2da8159`. The preceding namespace, variables, local notations and instances are also byte exact: 1356 bytes, SHA256 `bc3f8e3333c3d902b85084c434678358c71037bf13c76694ff34c5cacdecc72f`. The only declaration transforms are the theorem name, grouping of the old result, and the appended observer. The old admission is unchanged.

The observer uses Frame.values to derive ProperState at the actual returned core. It uses the retained old iff to derive the same assignment at that core. It then calls native progress with the same returned Packet.valid and Packet.safe, caller, heap, updated metadata and framed cache. It assumes no future execution, final assignment, recursive completion, or after-ProperState.

The conclusion excludes the stuck decision after recording. On a false callback the old continueWith law uses that exact decision. On a true callback runtime still returns complete[]; nonstuck does not refute oracle rejection or imply a recursive call. Neither result supplies ProperState from Packet/Canonical, preserves it through every native preparation, excludes depth exhaustion or unsupported projections, or proves positive recursive output coverage.

The first native strict failure and its exact source are retained. The final native repair changes proof terms only relative to the generalized-residual v2 statement. The initially incomplete callback draft is also retained with its API/import precheck notes. It was not presented as a checked proof.
