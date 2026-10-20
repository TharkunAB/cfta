# Independent mathematical review: stopping source writers and native optional sites

Reviewed: 2026-10-20 17:53 CEST. No material mathematical or contract issue found in either frozen candidate. This is an independent source/proof review, not a new Lean check or fixture.

Candidates:

- SourceCurrentStoppingBuildRootedWriters.lean, SHA256 2ccd95c5fc0b271a4446b8f9a2b5732823171e933eacce687c874d7b1711f2ee, 335 lines.
- SourceCurrentNativeMuOptionalSite.lean, SHA256 71d1603ee0e3fcecff34333554a820d035317dd02313e8d81421c70d8713954f, 231 lines.

I read both complete source proofs and their public statements against the actual source/native execution definitions. I read the stopping full printer. For the 2,815,611-byte native printer, I inspected the complete public type and central elaborated proof sections, and checked the entire output for complete proof/axiom printing and absence of truncation or errors. The recursor, exact yielded-state equalities, same suffix and final prefix construction agree with the full source proof. I ran only the existing Python verifiers, read-only, from cwd=/.

## Stopping source writer

The sole public head is SourceCurrentStoppingBuildRootedWriters.build_writer_or_prior, line 324. It takes the original source root, initial lexical inputs, entry heap and rich Context, and any exact full Mu cell at `(build root initial before).state`. It returns that SAME full initial cell or the EXISTING CompletedBuildRootedWriters.Written at that actual stopping state. No done equation, future completion, supplied event, rooted route or desired observation is required. Rewriting a pending outcome selects its actual advanced heap.

The private Rooted predicate is indexed by the SAME issued Path. Supported retains both together. The private support/selection block is byte-identical to the earlier completed-build module's corresponding block; it is copied additively into this new namespace. No old source byte changed. The new source contains no generated `_private` name reference. It imports and reuses the public old Written type.

The pending branches are substantive:

- supported_bind stops at the actual pending heap; it does not run the continuation.
- A pending Depth callback returns only that callback's actual supported path.
- A pending ordinary callback retains the completed Depth path and its own actual partial path.
- A pending cache hit publishes nothing. Its actual earlier probe effects remain.
- Fresh reservation retains nodeRecords unchanged and has its real physical and issued growth.
- A pending reserved body retains the real Depth/ordinary/reservation/body prefix. It does not install an outer publication event for a body that did not finish.
- A completed reserved body constructs the actual Publication with the same callback equations and its original Reached binder route.
- Ordered children and rows stop at their real pending subcall. Completed preceding siblings advance Context and Reached by their actual growth. Actual makeEdge/makeNode/makeUnion/root filter intervals carry NoNewMu and the required physical/issued effects.

The writer induction covers every issued Path, including these pending prefixes. Its trans case chooses one exact earlier writer and extends its suffix, or preserves a later writer and prepends the exact earlier Path. Its publication case considers the same final full cell, actual first-write absence and immutable keepFirst result. Inner body/probe writers retain their own same event; no other event is selected by payload equality.

The Rooted label is derived from the actual source call. For a native generated encode root it is still that generated root, not an original-program binding route. The explicit initial full-cell alternative remains necessary for warm states. Source stopping-state coverage does not by itself identify the native operation or compiler owner that invoked this call.

## Native yielded-trace site

The sole public head is SourceCurrentNativeMuOptionalSite.trace, line 146. It takes the actual physically admitted Trace, an initial SemanticHeap and an arbitrary exact full Mu cell at the trace return. It returns that SAME full initial cell or one exact optionalBinder occurrence in that trace.

The Trace premise is not an arbitrary unverified control sequence. Its cons constructor retains each actual yielded step and the current physical Inputs. Those Inputs include constructor argument availability, current node/edge readiness and key-safety checks where appropriate. The theorem adds no separate Good, Fields, Ready, native History, source writer or captured-owner premise.

step_effects derives semantic preservation, physical Grows and issued extension for the actual instruction. The actual optionalBinder effect is checked on both done and pending outcomes. Other source instructions leave the heap unchanged or run one physically admitted primitive Work. work_noNewMu covers only that admitted Work syntax; the proof does not assert that arbitrary caller-written heap effects cannot make Mu.

step_kind isolates optionalBinder as the only admitted instruction that can add a full Mu. The trace proof then proceeds in chronological order through its actual tail:

- If the selected target is already present at the current step return, NoNewMu moves it backwards for every other instruction.
- For optionalBinder, actual Grows and the exact returned target force the same prior full cell or literal entry None.
- In the new-cell arm, the actual yielded equality excludes maybeMu.pending. The done equation gives the real result and heap.
- Outcome.yielded injectivity identifies BOTH the actual next control and full checked return state. The suffix is the original tail rewritten by these data equalities. It is not an unrelated trace from an equal heap.
- The site tuple keeps that exact prefix Trace, semantic state, available body, maybeMu equation, full native advance with unchanged checked operations, actual yielded step, suffix Trace, target entry None/operation-return Some, and both physical/issued prefix and suffix effects.
- If the target is first installed later, the constructor prepends this exact original instruction to the earlier Trace. The selected site and suffix remain unchanged. Arithmetic retains `fuel = prefixFuel + 1 + suffixFuel`.

The target key and all target payload fields remain fixed. The site body is a separate value; no equality with the selected target or a compiler body is assumed. The source proof retains the actual body availability at the site's entry, not at a later unrelated reader.

## Composition limits

These are complementary contracts, not an all-outcome native generation theorem.

The stopping source head can recover a rooted source writer from the actual maybeMu generated build, including nested publications before pending. The native site theorem locates only OPTIONAL instructions that actually yield within its supplied Trace. Trace has refl and yielded cons constructors; a terminal blocked optionalBinder step is outside that Trace. Its partial heap effects must be handled by a separate all-outcome native endpoint.

The site theorem does not attach a captured compileMu owner, entered domain, body-query trace or native requester. A generic caller-written optionalBinder is allowed. The same actual site must later be connected to the actual compiled request/edge/walk schedule; an independent owner existential cannot be substituted by matching the body value.

Neither theorem proves original-root binding ancestry for native mapped captures, a complete-self decrease, reader/memo History transport, semantic equivalence, renewal, termination or Haskell correspondence. Physical/issued extension is not a native memo retention or owner receipt. No operation or writer uniqueness theorem is claimed.

## Evidence and counts

The stopping package verifier returned PASS for 40 package pins and 20 foundation sources, including live-root byte comparison. Selected stopping-rooted-direct-1 has a literal empty log. stopping-rooted-public-1 has one complete statement/proof/axiom group, all eight printer options and only standard axioms. Its owner ran two Lean jobs, no failed attempt, no canonical job and no constructed pair.

The native package verifier returned PASS for 33 pins. Selected optional-site-direct-2 has a literal empty log. optional-site-public-1 has one complete statement/proof/axiom group, all eight printer options, no omissions/errors/warnings and only propext, Classical.choice and Quot.sound. Its full log SHA256 is f83fcbac016a1870f447e8354d0298932b4b1251b219383783e0865376e04385. Its owner ran three Lean jobs with one preserved earlier elaboration failure, no canonical job and no constructed pair.

Both selected packages record pinned Lean 4.34.1, memory.max=memory.high=4294967296, zero swap, five-minute caps and fresh usage above the stop threshold. The existing completed-build source is unchanged. This independent review owns zero new public heads, zero proof pairs and zero Lean runs. It reuses two prototype public pairs and zero constructed pairs. Fixture work and native terminal-blocked extension are not counted here.
