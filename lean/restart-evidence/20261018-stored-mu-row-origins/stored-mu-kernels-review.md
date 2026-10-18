# Actual open stored Mu row integration

The single public constructed theorem is `MicroCFTA.StoredMuKernels.open_stored_mu_row`.
It has no premises. All initial and returned data come from this file's actual source execution.

The source builds a smart outer Mu from an empty heap with one available external reference, `intersection 0 1`. Its body is a union of leaf row 7 and row 8 with ordered children outer-self, external-reference, and an inner Mu. The inner Mu has row 9 with ordered children inner-self and the same external reference. Both retained Mu values are open. The checked `nested` predicate requires a Mu child with a nonempty free-name list. The source syntax uses the exact nested lexical indices 0 and 2 for the inner self and external reference.

The replacement environment maps only the external reference to Empty. It leaves all other names absent. Actual repaired substitution reconstructs the open outer Mu and the open nested Mu. The external Empty removes the recursive row alternative. The actual returned value has physical row 7, the full Unit guard, no children, and no free names. No BinderFree or finite Cap premise is used. The self-only recursion in the inner row is called recursive; this fixture makes no claim of a nonempty finite language for that Mu.

Initial SemanticHeap, payload Covered, source availability, and History from empty are derived from the actual source build and the available primitive capture. Replacement availability is derived directly from the partial environment and Empty availability. The fixture invokes `SourceCurrentStoredMuRowOrigins.mu_complete`. Its returned complete value and heap are identified with the literal computed execute outcome by injection of Outcome.done. Thus the full Rows receipt refers to the same original body, replacement map, returned value, and exact returned heap. Rows retains the actual depth callback, original-body execute under the sparse local shadow, local availability and replacement facts, literal raw-row provenance, and the full binder reader receipt.

The private `checked` theorem holds the entire stated conjunction. The public theorem forwards that exact proposition. This proof packaging keeps full printing small. No Claim abbreviation or auxiliary printed group is used.

Selected strict is `stored-mu-kernels-direct-3`; its raw log has exactly zero bytes. Selected full constructed group is `stored-mu-kernels-public-1`; it checks, prints the complete theorem, and prints its axioms with all eight required settings. Its only axioms are propext, Classical.choice, and Quot.sound. All selected runs record effective memory.max=4294967296, memory.high=4294967296, and memory.swap.max=0 under a five-minute wrapper.

Attempt 1 checked the initial source facts only. Attempt 2 also checked the producer integration with a closed inner Mu. Attempt 3 strengthens that inner Mu to be open and therefore exercises nested binder reconstruction. All three strict attempts passed with zero-byte logs. All raw snapshots, logs, limits, metadata, and peaks are preserved. The component has one constructed proof pair and no new production declarations or auxiliary pairs.

This fixture proves one actual substitution and its row receipt. It does not prove an initial-source occurrence rank, binder result equality in general, all-owner exclusion, a fresh-call bound, or general outer termination.
