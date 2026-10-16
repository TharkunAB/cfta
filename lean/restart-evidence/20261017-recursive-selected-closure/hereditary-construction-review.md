# Local construction and head closure review

The final sources are `SourceCurrentHereditaryConstruction.lean` and `SourceCurrentHereditaryExposure.lean`. The construction module has 506 lines. The exposure module has 207 lines. This review uses their final canonical versions.

`MuStored` is a conditional representation invariant on each completed Mu record. It states that annotations on both exact stored probes imply the annotation on the stored body. It does not require every cache record to satisfy the annotation. The invariant is explicit for an arbitrary warm cache. `InternedNestedRequestFacts.complete_verified` establishes physical facts from independently available body and probe records. It does not establish a guard relation between those records. The new proofs do not infer `MuStored` from those physical facts.

The actual construction proof derives this invariant for every new completed Mu record. The recursive syntax induction proves annotations for the actual depth probe, ordinary probe, and reserved-name body. The miss branch installs the derived body certificate before first-writer readback. The hit branch uses `InternedProfileHeap.stored_probes` and the current physical facts to identify the stored probes. It then applies the existing conditional certificate. Smart cleanup selects the annotated body, empty, or the annotated Mu. It does not inspect annotation validity in the executor.

`build`, `buildMany`, and `buildEdges` follow the actual ordered binds. They retain the conditional store even at a pending outcome. Their public premises concern initial syntax, captures, physical facts, and the initial causal store. The private recursive callback obligation is discharged by the syntax induction. `closed` constructs its own literal successful return from the existing closed-construction completion theorem. It does not take a supplied successful build.

The substitution proof derives annotations for the actual stored leaves and replacement inputs. It invokes the same literal repaired construction. `unfold` substitutes the original annotated Mu into its annotated stored body. `optionalBinder` follows the actual repeated-pair test and the literal repaired binder construction. Neither theorem takes a future result annotation or completion law.

The exposure proof follows the actual finite worklist. Ordinary rows use their original guard and child annotations. Unions use actual member annotations. Mu exposure first performs the literal repaired unfold. The ordinary fast path returns those rows. The fallback reads the original root at the exact cache after the first unfold. Physical exposure receipts supply facts, availability, and complete cache histories at each prefix. `head` then invokes the actual ordinary constructor at that same returned cache. The supplied head graph is a verification input; it is not presented as general completion. The integration tests construct their own head graph using initial closed readiness.

The imported public check contains 24 declaration pairs. Each pair prints axioms and a full explicit signature. The four integration pairs check:

- Closed allowed syntax constructs its own value and causal store. A later unrelated edge with an invalid guard and its ordinary cap retain the earlier value. A finite actual head is then constructed. Its result retains the local annotation. The cap heap is proved to fail the global annotation invariant.
- A closed source program replays its exact value and full cache without allocation.
- Actual optional binding constructs its own successful return before its annotation and store are extracted.
- A concrete recursive Boolean-guard syntax family, with a union and a self reference, instantiates the unrelated false-guard cap result for both smart-cleanup choices.

These checks pass with all linters enabled. The public signatures and kernels have no `sorryAx`, warnings, errors, or truncated output. Both production sources are unchanged after canonical validation.

This component proves local annotation and causal-store closure for actual constructor, substitution, and exposure operations. It does not prove that arbitrary earlier warm Mu records have construction provenance. It does not prove whole native execution annotation, causal-store transport through every Merge comparison, recursive selected outer completion, convergence, or full Haskell runtime correspondence. No Haskell defect is claimed.
