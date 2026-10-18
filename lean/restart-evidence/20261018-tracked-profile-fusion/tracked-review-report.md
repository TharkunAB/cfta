# Independent tracked profile, base, and writer review

Status: final source, selected probe, and constructed fixture review complete. No material issue was found.

Reviewed production hashes:

- SourceCurrentTrackedRootProfile: `4d2725dc6ed820bf6ead7af131de0d96d68f0517cc50af399427a3fb707d8f62`.
- SourceCurrentTrackedFilteredFusion: `dd4f3b302ff195290b80f92f35e6141ab5fd9beff7f37c14c86e2f26b051e7cf`.
- SourceCurrentTrackedWriterFusion: `62996854bc5214574ea5c8a8b2f07b45f4c9cda44f1a2a6fc027b30e548d587b`.

No material mathematical or contract issue was found. This review performs no Lean runs and adds no proof pairs.

## Tracked profile semantics

`mask` retains a pure profile only when every root name is tracked. It retains the whole pure list or replaces it with None. It does not discard selected list members. Thus an untracked reference and an ordinary node can have the same opaque tracked observation. `Related` is profile equivalence for this explicit observation. It does not claim structural equality or full language equivalence.

`mask_empty` follows because the empty list always passes the tracking test and every nonempty list remains physically nonempty after either branch. `mask_equiv` transports the all-names test through set equivalence. `mask_combine` follows the actual append rule and the conjunction of both all-names tests. It keeps opacity absorbing.

`Related.empty` uses actual Ready, residency, and proper records to convert profile Empty to physical Empty. The availability premises exclude arbitrary zero-row ordinary records. `Related.bare` requires the observed name to be tracked and uses the existing normalized available singleton reflection. The normalized union cardinality, distinct identities, flatness, and nonempty-member facts come from Ready. Neither theorem asserts reflection for arbitrary raw records.

`nil_equiv` is an exact pure profile equivalence: with no tracked names, the observation keeps only Some [] and maps every other profile to None. `mask_single` retains exactly the singleton-name set test when that name is tracked. `mask_cons_fresh` states exact equality only when the added marker is absent from the complete pure profile list. None has an empty getD list, so its equality case is immediate. This helper does not assert freshness of a later result or identify value free names without additional provenance.

## Exact old-contract recovery and base clauses

The tracked Fusion contract retains every premise of the earlier bounded contract. It adds the marker parameter and changes reference-slot and output relations to tracked profiles. The bound remains on the two original raw source values.

`paired_from_empty` derives Paired (Related []) from the original Paired Empty flags. At reference slots it uses actual resolved replacements, Ready/properness for resident replacements, and literal fallback reference computation. Non-reference slots retain the original exact value equality and map agreement on fixed free names. It adds no reader-wide lexical availability premise.

`to_empty` therefore recovers the exact earlier SourceCurrentBoundedFilteredFusion.Fusion contract. It derives filtered and reconstructed output availability from the actual warm filter and execute calls. It assumes no desired output Empty law.

The empty source clause inverts the actual builds, filters, and executions. The variable source clause uses the actual selected lexical index. Reference slots use the supplied resolved tracked relation directly. Fixed non-reference captures use exact capture equality, source-scoped self tests, filter equality, and execute_congr on the filtered free support. Unused aliases remain allowed. Historical contexts and raw growth stay explicit in the contract; these base cases do not need stronger future facts.

## Actual selected writer and depth induction boundary

`publication` decomposes both actual historical callbacks and verifies each raw build and root filter. It derives intermediate growth and issued extension, then composes them with the supplied actual Keeps suffix. Historical context replay constructs the complete reader lexical contexts, including unused captures. Both raw builds and filters are replayed at the same reader.

The original raw callback depths come from the actual historical rank producer and deterministic build equality. Both original raw plans are bounded by the stored body depth. The proof places no depth bound on replacement values or reconstructed outputs.

The actual publication aliases and support-scoped self tests feed the source law. The shared replacement map binds both original local names. Its cross-absence theorem derives exact execution agreement with each original sparse map. Fixed captures use that same map on both sides. Arbitrary outer replacements may resolve Empty. The supplied local Related markers premise is a lexical input relation, not a supplied callback output law.

`writer` consumes the stronger actual issued Written receipt. It recovers the earlier publication, keeps its syntax and full captures, and derives cut-to-reader and body-to-reader Keeps from reserve/body/publication/suffix growth and issued provenance. It does not infer issued extension from old Grows or infer an earlier history from a final history. The stored body depth is strictly less than the selected candidate Mu depth.

The uniform induction premise `forall rank < selected.depth, forall expression, Fusion rank expression` remains explicit. The module does not prove that premise, assume the earlier writer has the current requester syntax, remove an outer symbolic lower operation, or prove the full used-binder source clause. The stronger tracked relation is a prerequisite for those later proofs.

## Validation readback

The review personally read the final root direct6, base direct4, and writer direct1 logs. All three logs have zero bytes. The source hashes match their frozen execution snapshots. The selected canonical checks are root canonical5, base canonical3, and writer canonical1. Each completed with no warning or error text. Full public groups root public1 (14 declarations), base public1 (4), and writer public1 (2) passed the hardened print and standard-axiom checks. The root, base, and writer full constructed groups each add one reused pair. All groups enable all eight required print options, print @check/full proof/axioms, and contain no warning, error, sorry, elision, or pretty-print failure. The selected executions use Lean 4.34.1 with memory.max=memory.high=4 GiB, swap.max=0, and the five-minute cap. No source or existing evidence file was edited.

## Constructed scope

The final root fixture strict1 builds the actual used Mu `mu x.7[x]` from an empty source heap and derives Ready/Available. Its opaque tracked observation agrees with an untracked fallback reference. It proves disagreement with tracked marker 99, records the tracked singleton versus empty-tracking opacity, and applies mask_cons_fresh at the exact absent marker. It makes no finite-language claim.

The final base fixture strict1 builds that same used Mu and constructs actual variable raw calls under distinct source names. One map resolves its selected slot to the Mu and the other leaves an untracked bare reference. It derives both lexical Contexts, source-scoped aliases/self tests, actual maps and calls, and the original Paired Empty premise. It invokes both the tracked reference theorem and to_empty. It does not supply the output Empty equality as a premise.

The final writer fixture strict2 builds an actual publication with source node `7[var0,var1]`, a local self slot, and used captured interned reference 0. The outer map resolves that captured reference to Empty. It derives an actual issued Path from the empty heap and recovers Written at the original reader. It then performs a real source preparation of the dead edge, derives the final Ready/Keeps suffixes, and checks both exact sparse stored callback calls warm at that final heap. The local candidate is a nonempty Mu, and both reconstructed callback outputs are Empty. The smaller tracked body law is derived from the tracked node step and actual variable child laws. The public constructed theorem invokes publication; it retains Written but does not instantiate the uniform writer induction premise.

All three constructed statements use private checked witnesses with public aliases of exactly the same explicit signatures. Their public probes print the exact alias proof and its standard axioms. The final selected writer strict2/public1 source hashes match the owner-confirmed pins. The earlier writer fixture list-membership failure remains preserved and unselected. This review adds zero Lean runs, zero public declarations, and zero constructed proof pairs; it reuses 20 public and 3 constructed pairs.
