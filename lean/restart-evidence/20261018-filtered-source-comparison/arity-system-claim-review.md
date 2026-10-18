# Review of the current system claim

Reviewed on 2026-10-18 at 19:32 CEST. This review reads the live declarations. It adds no Lean declaration, build, or proof pair.

## Broad outer reduction claim

For each ambient reference interpretation, the proved language relation is:

`L(input) ∩ Sat(inherited) ⊆ L(result) ⊆ L(input)`.

A successful bounded modeled call adds no accepted finite tree outside the input language. It retains every input tree that satisfies the inherited equality constraints. With inherited payload `some []`, satisfaction is universal and the two languages are equal.

The exact law is [NodeLaw](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentAllocatedPartialMemoSound.lean:29). The actual worker theorem is [OuterInitialActual.node_call](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentOuterInitialActual.lean:432). Its input premises explicitly include initial Context, Frame, Fits, a finite guard carrier, inherited readiness, input availability, initial scheduled Room, and the literal successful bounded call. It derives actual semantic reads, returned Post/Frame/resources, result availability, and NodeLaw at the exact returned caller. It does not require a desired invariant at each future stage. It also does not construct all its initial facts or prove success.

The extra direction needed for exact inherited filtering is `L(result) ⊆ Sat(inherited)`. NodeLaw does not prove this direction. [Sat](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceEqualityPrecheck.lean:35) maps contradiction to False. A contradictory inherited payload therefore makes the conditional preservation obligation vacuous. The unconditional output-language inclusion remains. This does not imply a physical Empty result. The literal [union body branch](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentAllocatedPartialWorker.lean:77) returns its original union regardless of the inherited value. No Haskell defect or new executable counterexample follows from this review. Even an empty-language conclusion would need a separate reflection law to imply the literal Empty constructor.

Initial semantic admission is only partly produced separately. [PartialInitialization.constructed](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentAllocatedPartialInitialization.lean:106) derives Context from actual closed source construction and covered guard allocation history. [Frame.initial](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentConstrainedCapGeneratedQueryResources.lean:76) still takes the recursive guard certificate. The final node theorem does not discharge that certificate for every supported public input.

## Stronger constructed Sized result

[SourceFreshOrdinarySizedEntry.constructed_complete](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceFreshOrdinarySizedEntryCorrect.lean:113) starts from a literal completed closed modeled construction and valid source annotations. It derives the internal semantic, coverage, depth, guarded-budget, and annotation heaps. Both modeled reference and optimized paths complete with the same result and final cache.

If that result is `.ok (.ok api)`, [SourceSizedApiLaws.Exact](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceSizedApiLaws.lean:15) gives finite distinct classes, exact accepted-term membership at each node count, exact counts, out-of-range rejection, rank coverage, both rank/unrank directions, and exact ordered finite enumeration prefixes. Valid annotations and the literal source construction remain premises. Errors remain possible; the theorem does not promise that every source produces an API. These Sized laws do not prove completion of the separate general outer reducer or verified execution of the Haskell implementation.

## Central remaining whole-library obligations

- Prove general recursive source comparison and the causal payload facts required by later cache hits. Current body/probe and root-filter interfaces do not provide this universal producer.
- Derive all semantic initial facts, including the recursive guard certificate, for every supported public recursive entry.
- Prove general outer completion. Active-owner exclusion and a bound on fresh calls are separate obligations. Repeated-pass convergence also remains separate.
- Prove the implementation correspondence. This includes Haskell demand/cache behavior, machine-integer adequacy, and the external interfaces.

Audit success establishes checked dependencies for the modeled statements. It does not discharge these remaining obligations or establish whole-library correctness.

## Review of the system note

I read `lean/notes-current-system-claim.md` in this checkout. I found no material issue in its stated broad reduction guarantee, initial assumptions, contradiction boundary, constructed Sized caveats, or remaining whole-library obligations. Its distinction between completed modeled construction and a successful returned API is correct. The root-filter discussion is consistent with the explicit requirement to retain original root structure; this review adds no new proof of that separate source-comparison step.

## Live source pins

- `SourceCurrentOuterInitialActual.lean`: `b38770861fb19a9514f9f4c49f2d18a9ecf79572bbedcc3f90cf941c1240919b`.
- `SourceCurrentAllocatedPartialMemoSound.lean`: `d9954897cde59e88abb27f68fde9842f60662f862847ede783193283fe3c8d7e`.
- `SourceFreshOrdinarySizedEntryCorrect.lean`: `cc8ad1f6bf8eeda9a8c96b7a57773b95533be446837578165d17c883eb0f6209`.
- `SourceSizedApiLaws.lean`: `cead8df5d7024eeff9ef9345acf5d68a93f1e5679ee40623d7c556673722f577`.
