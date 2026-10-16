# Independent review of the hereditary Merge guard producer

Date: 2026-10-16 22:59 CEST.

No material defect was found in the five frozen modules. This review covers all 638 source lines and the five final integration kernels. The owner manifest is `283a24506ec6d22f45a8635bac79fef66a1bafc9d5a156abdc5b054970f89c0d`. All 47 manifest entries matched their current bytes at review time. No source was changed. No Lean, Lake, or Haskell process was run for this review.

## Branch closure

`MergeGuardBody.lean:65–84` processes each small row's children through ordered requests. Each returned contract supplies its own original-relative guard certificate. The literal edge constructor retains the original raw guard and uses the actual returned child list. Physical availability comes from those same contracts.

`MergeGuardBody.lean:86–117` handles every retained column shape. A singleton returns directly. Empty and multiple ordinary operands use the literal ordinary union and then a recursive request. The initial hereditary profile excludes the recursive-boundary union branch. The union's profile follows the actual constructor at the current heap. Closedness is derived from the initial ordinary profile, current availability, and coherence. It is not a future result premise.

`MergeGuardBody.lean:120–138` restricts the column profile to members retained by the actual completed selection. `selected_inputs` supplies membership in the original column. It does not claim that every input remains or that selection preserves multiplicity. The ordered map certificate separately retains each returned occurrence and its physical readiness through later effects.

`MergeGuardBody.lean:141–171` derives each column operand from an original row child. The final large-group row uses literal Top. `top_bounds` proves Top fits the same bound vector, including the zero vector. The proof does not reuse an arbitrary original parent guard or assume a property of the selected output.

`MergeGuardBody.lean:177–222` follows both literal threshold branches and the actual ordered groups. The small branch handles up to four rows. The large branch returns one row. Returned rows remain resident through later effects. The final normalized node constructor consumes their derived profiles. Group membership comes from the source grouping partition. The body endpoint at lines 225–243 handles Empty, ordinary closed traversal, and the literal unchanged open case. Mu, explicit union, and references cannot satisfy its initial hereditary ordinary profile.

## Captured originals and the first winner

`MergeGuardCache.lean:20–25` stores a universal certificate for each entry's own complete captured original. Physical storage remains a separate invariant. The hit endpoint at lines 49–57 uses semantic coherence, current input availability, and physical storage to recover equality of the complete captured original with the actual request. A matching reference alone does not establish that equality.

`MergeGuardProducer.lean:37–66` follows the actual mutual Run/Call recursor. Bind passes the first prefix's exact heap and memo to the actual continuation. Work and selection transport both storage invariants through their actual effects.

The miss case at lines 73–92 first applies the smaller body Run induction hypothesis to its physical certificate. It then universally instantiates the same smaller Run with each initial guard profile. This derives the candidate certificate before `remember` and the current-winner reread. No completed body, candidate law, returned profile, or successful recursive callback is supplied at this producer boundary. Reusing the induction hypothesis proves two properties of the same supplied body graph. It does not run a second body or select another heap.

The current memo may already contain the key after the body. `winner_certificate` at `MergeGuardCache.lean:60–74` retains that entry and uses its derived stored law. If the key remains absent, it installs the newly derived candidate law. Physical readback at the actual final heap identifies the retained entry's original with the current input. The final returned law therefore concerns the actual first winner, which may differ from the miss candidate.

## Allocated execution and stable return

`MergeGuardFinite.lean:27–39` applies physical verification and guard production to the same supplied allocated Call. `Call.graph` retains its exact output, heap projection, and memo. It only removes the equality-operation component from the proof used for the pure guard property. The physical result still comes from the original allocated graph.

The finite endpoint at lines 42–55 constructs its own allocated Call from initial Ready, physical storage, and input availability. It derives the guard law and stable literal worker return for that same Call. Its result includes the same full allocated state and completed memo. The cold endpoint derives both empty-table storage invariants. There is no supplied completed Call, result bound, future capacity, or recursive body law at the finite endpoint.

The full allocated state here consists of the constructor heap and equality operations. It is not the full outer checked caller state. The large Top-row primitive allocates the empty equality field at the reached operations state. Heap erasure does not remove this fact from the allocated graph or stable worker result.

## Final five kernels

The final source `merge-guard-kernels.lean` and log `merge-guard-kernels-1.log` contain five axiom/full-explicit-signature pairs. The source enables all linters and explicit proof, universe, and deep-term printing with a 1000000 step limit. The final log has five axiom reports and five explicit signatures. It contains no error, warning, `sorryAx`, or omitted marker. This review inspected the existing source and log; it did not rerun them.

1. `actual_miss_then_warm` derives the miss winner and then the same-state warm law from an actual body graph.
2. `actual_reentrant_winner` checks retention when the actual returned body memo contains the key. It is conditional on that memo observation. It does not prove that such reentry must occur.
3. `five_row_actual` proves the literal five-row threshold equation and applies the producer to the actual large branch. This is a parameterized actual-execution integration check, not a concrete allocated five-row fixture.
4. `ordered_actual_requests` retains a separate original-relative certificate at each literal list position and proves exact output length.
5. `constructed_then_literal_hit` constructs a cold allocated return and then a literal warm call with work fuel 1 and selection fuel 0. The output, complete allocated state, and memo remain identical. It does not claim that work fuel 0 can perform a lookup.

## Source scope

The source anchor is `cfta/src/Data/CFTA/Interned/Operations.hs:611–648`. It groups by symbol and child count, uses the threshold four, retains each small row's raw guard, and uses Top for a merged row. Singleton retained columns return directly. Other ordinary retained columns are unioned and merged recursively. The new proofs follow the existing completed graph model of that source computation.

The generic `clear` primitive remains explicit. These proofs do not establish the allocation or CAF forcing caused by every Haskell selection comparison. They do not establish GHC demand order or HashMap group enumeration events. The completed sequential graph, the actual allocated Top-row primitive, and its literal bounded worker remain the stated execution scope.

The same-vector guard certificate does not bound the number of output rows, allocation requests, active outer frames, or the whole root's numeric plan. The hereditary domain excludes Mu, explicit union, and references. The raw constraint paths retain the natural-index guard model. General constrained outer completion and whole-library Haskell correspondence remain separate obligations. No Haskell defect was found.
