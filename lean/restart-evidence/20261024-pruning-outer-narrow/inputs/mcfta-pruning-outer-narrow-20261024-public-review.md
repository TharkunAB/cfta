# Outer pruning narrow public-output review

Status: PUBLIC_OUTPUT_CLEAR. Reviewed at 2026-10-24 07:30:47 CEST.

Arity authored the declaration proposal and its earlier source plan. Root authored the selected definition and proof bodies. Guard independently reviewed the frozen declarations. This is an independent review of Root's actual public check input, complete public output and selected implementation against those declarations. It is not an independent reproof of Arity's declaration design or the imported foundations. I ran no compiler or prepared program, imported no candidate program, and changed no repository, Git, network or board state. Earlier owners and reviews remain unchanged.

I read the complete 96-line selected source, all 16 lines of the actual public check input, all 74 lines/6361 bytes of the public raw output, both actual source/public reports, the Root body gate and setup-failure record. I compared all seven literal STRING fragments against the selected source. I reread the frozen owner controls and exact contracts, and Guard's complete 8225-byte declaration review. The public output contains exactly five complete signatures followed by five axiom reports. It contains no ellipsis, truncation marker, unresolved type placeholder or diagnostic that hides a premise. The selected source has no sorry, added axiom, proof-limit override, helper, instance, induction or unreviewed local have/let.

The public input contains the import of SourcePruningOuterNarrow, pp.deepTerms and pp.maxSteps printing settings, all five explicit @-checks, and all five axiom commands. Its copied checked.lean is byte-identical. The printing settings are confined to this diagnostic input. They are absent from the selected production source. The public report's source_sha256 names this actual 686-byte diagnostic input, not the 96-line production module. Both identities were checked separately.

## Actual public statements

All five signatures use the fixed complete SourcePruningTemplates.Symbol. Guard, Typing and Key remain independent Type parameters. The only instance premise is the existing DecidableEq of EdgeKey Symbol Guard. No Eq Guard/Typing/Key, new Monad, semantic typing law or desired final certificate appears.

| Public head | Complete observed contract |
| --- | --- |
| narrow | The existing public holeKey/fits/admits, Metadata Typing, fuel, original raw uv, complete Value and native State produce the existing MergedSourceComparison.Result of a complete Value. No success or validity premise is added to the definition. |
| narrow_mu | Every fuel returns the identical complete Mu record and identical native heap. The entry and all three stored Value fields remain explicit. There is no Ready or closedness premise. |
| narrow_type | Incoming membership uv in metadata.types returns the original complete value and identical heap for every fuel and every constructor. It does not substitute a representative or updated type-position set. |
| narrow_fallback | Non-Mu and incoming non-membership give equality with the actual narrowAt call at holeKey metadata.typing uv. This is equality of the entire Result, including failed results and their actual heaps. No successful output is assumed. |
| narrow_complete | Initial Ready before, Available before value and value.free=[] derive one actual fuel/result/after, the done equation, Keeps before after, Available after result, result.free=[], and the same actual result/after for every fuel+extra. No Ordinary or unchanged fallback heap conclusion appears. |

The printed non-Mu forall has the actual interned NodeKey entry and three complete Value arguments. The public type-membership and non-membership propositions remain on the original raw uv. The finite theorem's availability/closedness hypotheses concern the actual input, and its final cache and result predicates are conclusions. It contains neither a supplied final heap certificate nor a second completion premise. The final forall retains the SAME result and after from its existential packet.

The selected definition tests Mu before raw membership and delegates only the remaining case. Both bypasses return the original value and native heap. The theorem bodies use direct constructor cases. The native finite producer appears once in the shared non-Mu/non-member proof branch. Its actual seventeen-field packet supplies the chosen fuel/result/after and larger-fuel law. The two bypasses use fuel 0 and pure_keeps. This agrees with the frozen scope and does not claim that native fallback effects leave the heap unchanged.

## Actual axioms and checks

Every one of the five reports lists exactly [propext, Classical.choice, Quot.sound], including the public definition and the rfl Mu wrapper. No report is axiom-free. No additional axiom or omitted report was found. These actual reports are the evidence; a short proof body does not justify a smaller inferred axiom set.

The actual source-check-2 report has exit_code 0 and a literal empty raw log. Its copied source is byte-identical to the selected 5073-byte source. The command uses warningAsError=true and linter.all=true. The public-check-1 report also has exit_code 0 and binds all 6361 actual raw bytes. Both outer receipts use the existing serial capped wrapper with 4G/5m, and both effective limit records give memory.max=memory.high=4294967296 and memory.swap.max=0. This review did not rerun either check and does not report a later build, Audit, commit, seal or push result.

source-check-1 is retained as a Root setup failure, not a Lean proof failure. I read its complete traceback: the Python driver failed on read_bytes of the absent selected source before spawning Lean. setup-failures.json separately records the earlier literal-STRING/digest gate mistake and dependent missing-gate body-write failure. source-check-2 is the first actual source Lean invocation in this retained sequence. The failed setup attempt must remain in evidence accounting, without being counted as a failed Lean proof.

## Scope boundary

This component proves literal Value-level outer control and a finite structural cache result. It does not prove native memo2 realization, native NodeId/Int extraction, IntSet/list correspondence, concrete PartialTyping/unification/key laws, fits/admits soundness, coupled enumeration effects or full typedTypes/driver/pruning soundness. It adds no Haskell repair, stronger H6 result, resource or convergence claim. A bypass performs no modeled native heap action; this is not a runtime cost assertion. The existing whole-goal boundaries remain unchanged.

## Inspected immutable identities

Paths in the first table are relative to /tmp/mcfta-pruning-outer-narrow-20261024. No inspected input was modified.

| Input | Bytes | SHA-256 |
| --- | ---: | --- |
| SourcePruningOuterNarrow.lean | 5073 | 683318a8481f24af623174b5ea6ac9580520a86eba41a7eb2a441f9763e1ab28 |
| source-check-2/MicroCFTA/SourcePruningOuterNarrow.lean | 5073 | 683318a8481f24af623174b5ea6ac9580520a86eba41a7eb2a441f9763e1ab28 |
| source-check-2/raw.log | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| source-check-2/report.json | 641 | 7d79729f809ba2811c10d3a9e300dc2190b6abd11b8319899750e7d21a7443a3 |
| public.lean | 686 | de8e041ff27ed80abefdf1395a7a8a6a7d757fb260994d1680a00e915d899181 |
| public-check-1/checked.lean | 686 | de8e041ff27ed80abefdf1395a7a8a6a7d757fb260994d1680a00e915d899181 |
| public-check-1/raw.log | 6361 | c26bdd5a1927cfbe1b0365acf234f48819ce7f75c9452b1b0950c5c01a97bad7 |
| public-check-1/report.json | 509 | 3f51526e0bf4871ba8a5d1dc176d0d5bde4c910b680093fbfde5cc4d0da7920d |
| body-gate.json | 4127 | e600eed61a06e0ea8709f825d0049745766b24db3866211949e02de5f7280c58 |
| setup-failures.json | 1936 | 4adc5e99b63db3db3063d6b673f75ea2fc9aba8826149447c262a142c111ec31 |

The exact declaration owner remains /tmp/mcfta-pruning-outer-narrow-20261024-proposal. Its contracts.json is3254 bytes/SHA78616572a7fd9efa1c4d85a033d8e30c36e8527fff62c4e330170a2ddc393740; pins.json is7261 bytes/SHA4ca506dea1d6a6b4691137ad0dbf5622b1bdc668f047804e41b6632b70ac8982; FROZEN.json is970 bytes/SHAd742fa145205d8d29f92edb303e2d1a5f83064d85d33cd69b01253a3acec3b16. Guard's declaration review remains /tmp/mcfta-pruning-outer-narrow-20261024-declaration-review.md,8225 bytes/SHA1e634983c4193bd121af84ee1e9d58932862a7b76c2b1a8d0ba4f2101991b221.

The retained outer source-check-1.log has SHA9f8af3d737259eafb24fe8970ac0620704108267f04a8aca940363d7bccc7ce1. The actual outer source-check-2.json has SHA2d1b00b96371b2be269968348e96a4fe55703444d5b4f72c8c461e7d8b23862c. The actual outer public-check-1.json has SHAd86df7c4ffd0fabf27bd98bedb22362dbb6ce9d51d128d359eb624725986d9d4. Both corresponding effective limits.json files have SHA408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3.
