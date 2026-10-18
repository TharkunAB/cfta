# Independent review of physical Empty preservation

Reviewed on 2026-10-18 at 15:44 CEST. This review makes no source changes and runs no Lean builds. It reuses two production proof pairs and one constructed proof pair. It adds zero proof pairs.

## Result

No material issue was found in `SourceCurrentStoredNonemptyReplacement.lean`, SHA e04d1fb538ec4533b02244ada1896b8fb13d869a11f50f9f5d6f6e4ddc5cb69b. The conclusions concern the physical `referenceOf == .empty` test. They do not concern finite-language emptiness, output identity, observation equality, or general termination.

## Proof and premise audit

`execute_nonempty` (source lines 80–97) takes initial `Ready`, resident source availability, available supplied replacements, and a literal completed substitution call. Each resolved replacement on an original free name must be physically nonempty. Unmapped names resolve to references. Bindings outside the source free names do not need a nonempty condition.

The private `identity_inputs` proof (lines 23–49) supplies singleton positive name costs and exact available capture slots. `identity_test` (lines 51–78) uses `InternedStoredCostRetention.encode_retains` on the full encoded source. The argument retains arbitrary open nested Mu syntax. It does not identify the actual identity-substitution result with the original value.

The producer constructs an auxiliary identity call from initial facts through `SourceCurrentStoredReconstruction.execute`. `SourceCurrentStoredEmptyCongruence.execute_same` then compares resolved physical flags only on original free names. `SourceCurrentStoredEmptyInterpreter.execute_test` connects the actual identity return to the encoded flag. There is no supplied future identity return, future Ready premise, or assumed result equation.

`unfold_mu` (lines 99–120) binds the exact local self reference to the whole available Mu and leaves other names unmapped. Availability of the stored body follows from parent availability. Both the whole Mu and fallback references are physically nonempty. The conclusion compares the returned flag with the STORED BODY flag, not the outer Mu flag. A raw Mu can be physically nonempty when its body is Empty. The theorem does not contradict that case.

The review read the complete cost-retention, Empty-congruence, and Empty-interpreter dependencies. Cost retention uses positive source occurrences through encoded binder shifts, closed capture profiles, and live row children. The interpreter processes the complete open Mu body and smart binder. The congruence proof restricts environments to original free support. These dependencies do not require BinderFree or a finite Cap.

## Constructed evidence

`nonempty-replacement-kernels-direct-2.source.lean` builds its own closed outer binder from empty. Its first child is an open USED Mu with both self and outer references. Two different nullary ordinary replacements occupy a live original free slot. The two actual substitutions run in sequence. Their outputs are distinct and physically nonempty. Both actual `Keeps` facts are constructed from initial source availability and replacement availability.

The fixture invokes `execute_nonempty` at the exact first call. It also constructs an actual unfold of that same source Mu and invokes `unfold_mu`. The public witness retains both equations, source construction, distinct replacements and outputs, actual call states, live free-slot occurrence, and the exact unfold call. The public alias has the same full statement as the private checked theorem. This is a nonvacuous physical test; it supplies no desired future Reads or output law.

## Evidence selection and limits

Selected production strict: `nonempty-replacement-direct-4`, terminal zero and literal zero-byte log. Selected canonical: `nonempty-replacement-canonical-1`, terminal zero, warning-free completion of 592 jobs. Selected full production group: `nonempty-replacement-public-1`, two pairs. Selected constructed strict: `nonempty-replacement-kernels-direct-2`, terminal zero and literal zero-byte log. Selected constructed group: `nonempty-replacement-kernels-public-1`, one pair. Both groups pass the existing hardened all-eight-option, complete-printer, standard-three-axiom checker. Effective memory max/high are 4 GiB and swap is zero. No checks were rebuilt for this review.

Earlier failed attempts remain in the producer components. This review selects only final receipts. Its allowlist excludes mutable aggregate manifests, authority documents, and other agents' working selections.

The result does not establish general changing-capture binder congruence, a Generated Empty fusion induction, a source-ancestry rank, supported Haskell correspondence, or global recursive completion. In particular, physical nonempty does not imply a finite accepted tree.
