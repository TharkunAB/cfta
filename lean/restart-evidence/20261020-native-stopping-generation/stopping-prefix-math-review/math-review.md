# Stopping native sites and physical prefix splits

Independent source review on 2026-10-20 at 18:28 CEST. No material mathematical issue was found. No Lean job or new proof pair was run. The previous current checkpoint evidence is unchanged.

## Reviewed bytes

The stopping-site candidate has 307 lines and SHA256 6765f0cb387e13fc84a41821e5d2348150877f4791597a190faa22e68c6d1215. The prefix-bind candidate has SHA256 e8fff0ca4d8230b098b82b8a518bf99fbf46985c50f82d04cfcf024a1e801913. Both have existing strict and full public readback receipts. This review reuses their two checked public declarations.

The 87-line stopping-generation bridge has SHA256 7feff34b4826c055d28f020ac9c497afdc46206c84b448a544364c530da9eb90. It is reviewed as an unchecked draft. The review does not assert that this source compiles or count a checked bridge theorem. The owner can change that draft later. These snapshots retain exactly the reviewed bytes.

## Stopping-site execute

The public theorem takes actual physical InputsThrough for the bounded checked execute, initial SemanticHeap, and an arbitrary exact selected full Mu at the outcome heap. It returns the same full initial cell or one actual optionalBinder instruction. It has no owner, ancestor, future return, selected source row, or desired output-law premise.

The private step_effects proof derives semantic heaps, physical Grows and issued extension from actual instruction semantics. The work branch uses run_correct and run_issued_extends. The optionalBinder branch uses actual MaybeMu.verified for both done and pending. Heap-preserving controls are treated separately. step_kind uses the actual physically admitted WorkInputs and work_noNewMu. It does not treat arbitrary Work as a non-Mu effect.

prior_or_none uses physical record retention. An earlier Some with a different payload cannot be silently treated as absent. The exact selected full payload remains unchanged.

At the generating instruction, call is the literal maybeMu outcome. siteStep is the actual checked step. Its done/pending mapping retains the whole native advance and unchanged operation cache. sameHeap proves siteStep.state.native.machine.heap equals call.state for both constructors. Thus target presence and suffix growth refer to the same actual call heap.

The result uses an actual yielded prefix Trace and count = prefixFuel + 1 + remainingFuel. It retains the exact equality between the whole execute and resume remainingFuel siteStep. The terminal pending case remains blocked, with its real partial heap. There is no fabricated successful or yielded suffix Trace. The physical and issued suffixes are reflexive when the checked step terminates, and come from actual remaining execution when it yields.

The outer induction works backwards over the actual bounded execution. A selected target already present after the first step is classified by at_step. A target created later keeps the same recovered site while the proof prepends the actual first step and composes physical and issued prefixes. count zero returns the exact initial cell. Failures and constraint errors use the actual terminal step heap.

This is an operation-site producer. It does not infer native memo History from physical growth, or original source bindings from encoded captures. It does not identify a nested source writer; that is the bridge's task.

## Prefix-bind split

bind_prefix_cases takes an actual physically checked yielded Trace of control.bind next. The remaining control is arbitrary. It derives either an unfinished nonpure inner Trace at the exact final checked state, with the exact remaining = inner.bind next equation, or the actual inner pure-return Trace and continuation Trace at one identical middle state. Their fuel counts add to the original bound.

At zero fuel, steps_zero fixes the whole state and control. A pure inner code is already an actual return with a zero-length trace. Other controls are nonpure. For positive fuel, step_bind relates the actual bound step to appendStep on the unbound step. A yielded inner step contributes one exact physical Trace.cons using inputs_before_bind. A pure return starts the continuation at the same state and adds no inner instruction. step_done_iff justifies that case. Failed, blocked and constraint-error inner steps cannot match a yielded bound step.

The nonpure first alternative is essential. It avoids assuming a future inner completion. The theorem does not turn an arbitrary bounded blocked outcome into a yielded Trace. A caller must supply or derive the actual yielded prefix before applying this split. It retains only the current physical checks; it asserts no language law, field invariant, semantic reader transport, or compiler ownership.

## Unchecked stopping-generation draft

The proposed bridge consumes the exact stopping-site tuple. It applies the already checked all-outcome OptionalGeneration.maybeMu at that tuple's entry and call.state. The site's literal None excludes the local prior arm. compiled.symm.trans called identifies the same generated source build with the full nested outcome, including pending. Rewriting Written with called retains the same returned event and stopping heap. No second event or operation site is chosen.

By source inspection, this composition has no mathematical scope mismatch. Elaboration and full public checks remain the owner's work. This draft still does not attach the site to a captured compileMu owner. Prefix splitting is a useful foundation for that future inversion, not a completed owner proof. A nonvacuous blocked example must create a new nested cell inside the terminal call; an earlier instruction's retained target does not force that branch.

## Evidence and portability

The package snapshots all three candidates and the selected existing strict/full receipts for the two checked candidates. It retains their original command strings. Those four reused jobs have 4 GiB max/high, zero swap, five-minute caps and fresh usage gates. Both selected strict logs are empty. The two full groups pass all eight options, full proof/statement readback, omission checks and standard-three-only axiom checks. No new canonical build is claimed.

The package includes live ROOT foundation pins and local snapshots. The default verifier checks the frozen snapshots. --live-root also compares them to the live repository. Candidate verification uses the reviewer snapshots and does not depend on mutable owner temporary directories. The unchecked draft remains outside the checked pair count.
