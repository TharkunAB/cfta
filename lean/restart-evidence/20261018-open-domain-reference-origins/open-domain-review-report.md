# Independent review of actual open Mu body entries and reference origins

Reviewed on 2026-10-18. No material proof or contract issue was found in the two source producers. This review adds no Lean declaration or build.

## Forward derivation of the entered Good state

The captured native writer already supplies Good before, NodeReady for the exact request, and its actual compiler Trace. The entered state is the literal update of that same before state. It changes only the domain cache.

The shortest allocation proof uses SourceRecursiveIntersectionKernel.entered (SourceRecursiveIntersectionKernelCalls.lean:35). Its inputs are the captured machine validity, the request's Domain, and availability of both operands. It derives validity and Extension of the machine with the actual new domain table, plus Domain for the actual entered domain. SourceCurrentAllocatedNativePhysicalCache.advance_valid (line 85) transports both native memo tables through that exact machine update. The heap, equality operation cache, and allocated field heap are unchanged. The remaining fields of Good are therefore the captured fields. SourceRecursiveIntersectionKernel.body_available (KernelCalls:58) supplies both unfolded body operands. This also derives NodeReady of the exact entered body request.

The final SourceCurrentNativeMuBodyOrigins.trace uses the equally direct actual-step route. SourceCurrentNativeMuWriterOrigins.trace supplies the same schedule and operand identities. AllocatedNativeMuSource.enter_prefix gives the exact first yielded step. SemanticTraceReadback.current_inputs obtains the first instruction's physical checks from that actual compiler Trace. PhysicalCompletion.step_invariants receives captured Good, those checks, and CodeFields.compileMu_fields. Rewriting by enter_prefix gives Good at the literal entered child state. No later Good, semantic result, or history is used backwards.

Applying SemanticTraceReadback.effects to the actual child Trace then gives Good at its exact returned middle state. The requestNode continuation's fields are trivial. The optional-binder state equation identifies the following advance. Memo.advance_retained and the captured writer's explicit later Retained receipt compose middle-to-reader retention. NativeReferenceOrigins.forwarded then recovers the actual body request's direct compiler Trace or returned earlier writer at that reader.

## Key existence is separate from availability and machine safety

IntersectionFlatMemoKey.input (line 15) accepts complete node, Mu, union, Empty, and interned-reference roots. A reference to an interned name has a key regardless of whether it is closed. Other reference tags have no key.

A small sufficient pure premise is Control.identity value = some name. Value cases then give an existential complete input codec. Identity existence is sufficient, but is not necessary for keyability: Empty has a codec and no identity. SourceKey_complete converts two complete codecs into requestKey = some key. This conversion does not need heap facts, Original syntax, closedness, or word bounds.

For the selected Mu query, the existing SourceRecursiveIntersectionCode.mu_identities (SourceRecursiveIntersectionCompileMuBounds.lean:56) already supplies both identities from the bothMu/leftMu/rightMu decision. NativeMuBodyOrigins.request uses that theorem and its small private identity_keyable lemma. It excludes the direct arm for the CURRENT selected Mu request without adding closedness. Reference, ordinary, union, and repeated payload decisions likewise occur after the identity match in Control.decision. A general payload inversion could use that same fact. It is not needed for the current Mu endpoint.

Original.codec (SourceRecursiveIntersectionInputView.lean:258) is another sufficient pure codec producer. In the prior closed-input terminal scope, closed_original derives Original from captured coherent availability and closedness, and AllocatedNativeMuSource.original_body retains Original when exposing a Mu body. This is a valid way to obtain keyable open body operands in that scope. It is not a reason to require all such bodies closed.

Good and NodeReady alone do not imply Original, a complete codec, or a memo key. NodeReady contains Domain and operand availability only (SourceRecursiveIntersectionThunks.lean:39). Availability admits probe placeholders such as Depth and uninterned references. These tags have no memo-input codec. Physical cache comments that call operands original do not add the distinct Original predicate.

Key existence does not establish KeySafe. The actual child request Trace contains the conditional current KeySafe check in PhysicalExecution.Inputs (line 53). Once key existence is known, current_inputs supplies that check at the exact child entry. Word bounds are used for exact physical key decoding and memo validity. They are not needed to prove that requestKey is some key. No host Int capacity conclusion follows.

## Review of NativeReferenceOrigins

Final reviewed source SHA-256: af28f1080cce1827dc3f4959a33443b154b6688083023301ae49c1a2190cb132.

The reference theorem (line 34) inverts an actual successful compileReference Trace. It derives the literal domain membership, exact physical read, unchanged full checked entry, and actual child Trace with one less instruction. Missing binder or payload branches cannot produce the supplied successful Trace. The left and right consumers retain the original operand order. They derive the interned reference shape from the actual selected compiler branch.

The private stopped proof distinguishes an unkeyed direct compiler body from an actual returned cell. In the keyed branch, it uses the current Trace input check, physical validity, and literal lookup/demand. Warm ready values and cold protected finish use the actual request payload. The public forwarded theorem transports only a genuinely returned cell through explicit Retained, then recovers its earlier writer from final History. The direct case retains its actual compiler Trace. No internal History is assumed.

The writer consumer retrieves one actual captured reference writer. Its resolved child starts at the same checked state because the read has no state effect. The output carries that child's exact direct/returned provenance at the final reader. It does not assert that the read value is original source syntax, closed, or a semantic result law.

If a later consumer needs the read value identified as a complete Mu, captured NodeReady supplies Domain.bindings. Domain.lookup_mu and SourcePreparedSharedRows.read_identity identify the available binding. A new binding from Mu entry can be identified by Environment.enter_lookup. If that consumer also needs Original syntax for old bindings, it needs OriginalBindings or a proved causal producer. AvailableBindings alone does not supply Original.

## Review of NativeMuBodyOrigins

Final reviewed source SHA-256: 3c86eb339009f24b651f80405197af90de5cf96684ee1a4451e39d34a262bdaa.

Body (line 35) retains the same operand identities, exact entered domain, actual child Trace and result, Good at entry and middle, optional binder equation, and literal final state update. Its Forwarded receipt concerns that exact child request and same child result.

The returned consumer (line 76) recovers the actual protected writer from final History and the returned cell. It derives Body from that captured Trace and captured Good, with explicit retained native tables through the final reader. It does not substitute a candidate for an earlier first winner.

The request consumer (line 99) first derives final native History and Good from its actual successful request Trace. It excludes only the current Mu query's direct arm using the selected branch and complete codecs. The BODY receipt still keeps an honest direct/returned split. The theorem adds no closedness, BinderFree, finite Cap, or future completion premise. It consumes an observed successful Trace and does not assert that every recursive request succeeds.

## Exact remaining boundary

The new producers close the physical entry and reference-read scheduling gap. A full source-ancestry proof still needs to compose those actual domain reads, union members, and Mu publications with generated-body RowAt anchors. General retained used-Mu body/probe alignment remains open. A final reader's publication history must not be used to infer a publication history at an earlier optional-binder entry.

Original query ancestry must retain both Joined operand rows, actual guard conjunction, and ordered child pair traces. A generated body's unchanged full guard is not an unchanged guard of either query operand. No source-anchor size fact gives a bound on actual generated recursive children or excludes all active ancestor keys. General recursive outer completion and public Haskell correspondence remain open.

Only final production sources and explicit selected production receipts are included in the review manifest. Mutable fixtures, root peaks, shared selections, global Audit metadata, and authority documents are excluded.

## Selected validation

The selected reference own-source run is reference-origins-direct-3. The selected body own-source run is mu-body-origins-direct-3. Both logs contain exactly zero bytes. Canonical runs reference-origins-canonical-1 and mu-body-origins-canonical-2 completed. The only permitted canonical warning is the existing replay warning in InternedFreshOrdinaryClosedCompletion. Earlier body direct-1 and direct-2 attempts are unselected because their logs contain warnings.

The imported full-proof groups are reference-origins-public-1 (five declarations) and mu-body-origins-public-1 (four declarations). Each group includes all eight explicit printer and linter options, complete signatures, complete proofs, and axiom checks. The verification checks printer failures, omissions, warnings, and any axiom outside propext, Classical.choice, and Quot.sound. Every selected execution records Lean 4.34.1, memory.max and memory.high of 4294967296, and memory.swap.max of zero. The review reuses nine public pairs. It adds zero public pairs and zero builds.
