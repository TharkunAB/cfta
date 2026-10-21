# Native positive positions and the selected edit relation

Reviewed 2026-10-21 02:55 CEST. This package contains a source-only plan. All proposed contracts below are unproved. It owns zero Lean jobs, zero public proof pairs, and zero constructed examples. No official file is changed.

## Exact next primitive

The next missing primitive is the positional law for the ACTUAL optional constructor:

    maybeMu pair body before = .done result after
    Ready before; Available before body; Cap Plain depth body
    GuardHeap Plain before; NativeMuPublication.History empty before
    -----------------------------------------------------------
    forall p, PositiveAt result p -> PositiveAt body p

Here Ready is SourceEqualityRequiredCache.Ready. GuardHeap is the existing ConstrainedCapGuardHeap.Heap. This contract concerns one actual completed primitive. It assumes no future callback or native completion. The initial causal history can come from the actual source-started checked prefix. History at the primitive return must be derived from its operation receipt, not supplied as a future support premise. The signature can be reduced during proof if one of these existing physical support premises is unnecessary.

A private proof must transport the SAME natural child path through the actual ordinary-probe callback, then perform exact first-winner probe readback. It must not identify the selected stored body with the current callback body. The result must keep the actual operation equation.

The new in-progress StoredMuPositivePositions.reached/source contract, as coordinated with guard_inventory, is narrower and reusable:

    PositiveAt (finish smart (mu entry stored depth ordinary)) p
      iff smart=true and usesLocal depth ordinary=false
          and PositiveAt ordinary p.

That statement selects the ordinary probe of the SAME complete retained Mu. The used branch follows depth correctness and retained_of_used. The unused branch follows source_unused/history_unused and eraseSelf. It does not yet show that a positive position of that ordinary probe occurs in the incoming maybeMu body. This is the precise remaining constructor obligation. This package does not pin or claim completion of the in-progress module.

A full new positional heap evaluator is unnecessary. Prove one actual callback/encode transport privately, then consume the existing stored-Mu observer at actual request readback. Reuse InternedStoredSubstitution's actual encode/leaves and SourceRecursiveIntersectionMaybeMu.callback_eq/maybeMu_eq. The proof can follow ConstrainedCapStoredSubstitution.encode_typed's finite value/row/list recursion, but it must retain positions rather than only a depth bound.

Closed leaves stay exact lexical captures. Open ordinary rows keep their guards and ordered child indices. Unions add no child index. A capped source Mu is hereditary Plain, so its entire reconstructed region has no PositiveAt occurrence; use the causal MuStored law obtained from GuardHeap, rather than infer it from scalar depth equality. The nested Mu case is therefore excluded by Plain, not mapped through an opaque Mu input.

Existing BinderFreePublicationPositions.publication proves body/ordinary positional equality only for BinderFree event.expression (lines 487–503). It is not a theorem for arbitrary generated encode syntax. Open stored Mu values encode as .binder true (InternedStoredSubstitution lines 58–68), so the binder-free premise cannot be silently dropped. NativeNormalizedComparisonExecution.closed_compared is a stronger actual normalized source comparison, but its Compared predicate has absence/freshness and common-table premises. It does not directly export unconditional positive-path equality for arbitrary used callbacks. Its source recursion is useful prior art, not an already available replacement for the proposed primitive.

Estimated new primitive proof: 250–400 lines, mostly private finite encode/callback inversion, plus one actual maybeMu endpoint. This is an estimate, not a checked implementation size. Do not copy the complete normalized source evaluator or add a public provenance hierarchy.

## Exact native request law after that primitive

For an actual captured node request, the useful conditional local conclusion is:

    for every d,
      Bindings Plain source request.domain.key ->
      Cap Plain d request.left -> Cap Plain d request.right ->
      forall p, PositiveAt result p ->
        PositiveAt request.left p or PositiveAt request.right p.

Both alternatives are necessary. The source can switch sides at different child depths. The result is a same-position union of competing sources. It is not support in one chosen original slot or one whole source row.

This conclusion still needs a real producer for actual returned native cache entries, including warm hits. Derive that conditional law by the existing checked trace and protected finish induction from actual empty native tables, alongside the existing cap laws. The final endpoint must consume the actual request Trace or literal native execute return. Do not expose the desired cache output law as a new premise of a source-started endpoint. A reusable generic induction may use that law on already returned entries internally, just as the Merge support proof does.

The exact reusable branches are:

- Ordinary root: NativePositiveRowOrigins.positive_child derives a positive source guard using actual Written, active cached fields and conjoin_plain. Its small positive_side helper is PRIVATE and cannot be imported. NativeActivePairedRows.Joined retains full paired rows, exact edge handle, strong writer and joined guard equation. A short direct conjoin_plain contradiction gives the root disjunction from those facts. That route also covers the nullary case without a child premise.
- Ordinary descendant: NativeNodeRowLineage.ordinary/ordinary_body retains the selected child at the SAME ordered index without requiring a positive parent guard. This is essential. positive_child alone requires a nonplain parent guard, so it cannot cover a plain parent with a positive descendant.
- Union: NativeActiveUnionRowOrigins.returned and ActiveRowProduction.Cases retain the actual member call and schedule. Constructor normalization must choose an actual member at the same path. A canonical row index is receipt data, not a path component.
- Mu: NativeActiveMuBodyOrigins.returned preserves the supplied writer's exact entered body child and actual maybeMu. Cap Plain makes each Mu operand and its stored body hereditary Plain. A non-Mu operand keeps its literal body. Apply the new primitive only after the actual body child's conditional path law.
- Reference: HereditaryNativeScope.Bindings.read and ConstrainedCapNativeScope.enter/read retain the SAME complete available bound Mu. Plain bindings are independent of reference syntax: a reference has no PositiveAt constructor even if an unrelated bound record is constrained.
- Self/swap/reset/repeated/Empty: preserve the exact normalized request, or exclude positive results in row-free branches. Do not infer original query order from a normalized writer without the existing Route.

The existing source/physical requirements remain separate. PublicationTrace.source_trace/source_unused gives semantic and causal publication facts from an actual source build heap and actual checked prefix. It does not imply Plain operand caps, Plain domain bindings, native result-position laws, or selected original-source identities. Good and Fields supply active guard operands for actual conjunction. NativePrefixWriterMaps.prefix supplies physical strong writers at the reader but no positional law or internal History at their entry. CurrentNative.At retains cap/occurrence/origin stores; it has no PositiveAt law today. Those interfaces are templates for an actual induction, not proofs of the proposed result.

A public cold empty-domain query can discharge initial Bindings by HereditaryNativeScope.empty. Its recursive entered requests still need Bindings.enter/read. Source-builtness and closedness alone do not discharge those internal Plain obligations.

Estimated next actual native induction: 600–900 lines if it copies the current checked joint certificate/cache/trace pattern additively. A scoped actual ordinary-compiler endpoint would be smaller, but it would not discharge Mu/reference/union branches. Do not advertise a root-only positive guard theorem as full path support.

## A checked false shortcut

The published PositiveNativeSupportKernels.actual_opaque_mu_counterexample has two distinct actual closed source-built raw Mu inputs, empty native result tables, initial Good, actual native execute done and its checked Trace. Both inputs have no PositiveAt at any path because this observer leaves Mu opaque. The ordinary returned result has PositiveAt at []. See the pinned positive-native-kernels.lean lines 121–179.

Thus this proposed unrestricted law is FALSE:

    source-started + Good + closed inputs + actual request
      -> PositiveAt result p -> PositiveAt left p or PositiveAt right p.

Causal source publication does not repair the opaque observer. Cap Plain excludes this example because a capped Mu must be hereditary Plain (ConstrainedCapNativeScope.mu_annotated). The full outer conjecture does not currently supply a cap for every unrelated region of every child. A nonplain Mu outside edited paths can remain untouched. Keep the finite-cap native theorem as an intermediate scope. A general theorem must track untouched opaque barriers or use an observer that records them. No new counterexample or Haskell defect is claimed by this review.

Scalar GuardHeap profile equality cannot replace the positional invariant. GuardReadback.hit_cap lines 93–104 uses only the maximal guard-depth profile. Equal maxima can place positives at different sibling indices. The new stored-Mu finish observer reduces the precise warm cleanup problem to its actual ordinary probe; it does not make scalar profiles injective on positions.

## From native paths to actual class chronology

The pure target is the EXISTING SourceCurrentNormalizedChildSeparation.Rel E. Its member constructor replaces two class prefixes with one COMMON suffix. Its trans constructor composes actual source changes. child_separate is already proved at a congruence fixed point with the all-drop condition. No new pure relation or cardinality wrapper is needed.

For planning only, abbreviate a forest occurrence by:

    FPos values q := exists i p value,
      q=i::p and values[i]?=some value and PositiveAt value p.

The smallest actual class theorem after native transport is:

    runClass ... record phaseValues before memo = .done results after saved
    exact existing physical/readiness/inventory/semantic-read premises
    Merge Support and native returned-position laws at the actual entry
    finite Plain caps for the participating values
    every two paths of record are related by Rel E
    ---------------------------------------------------------------
    forall q, FPos results q ->
      exists sourcePath, FPos phaseValues sourcePath and Rel E q sourcePath.

This law starts with the actual class's captured phaseValues, which can differ from the first Required result. It derives its output relation from the completed literal class execution. It takes no desired source relation or future outer completion as a public premise. The old ClassSelectedChildLineage.Selection/native and ActualClassSemanticReads.class_selected already produce SAME selected edit, actual prefix/call/suffix, target slot, query and writer. They do not prove this path support law.

At an unchanged node or child, use Rel.refl. At an actual edit leaf at a, native support chooses either the current input at a or a target operand projected from a class path b. Target.operand projects before Merge (AllocatedTargetWorker lines 49–75). MergePositivePosition.allocated gives SAME residual path in that projected input. A positive projection/read needs a path-prefix producer: PositiveAt projected p -> FPos phaseValues (b++p), with actual exposure Plain premises. Apply Rel.member with a,b in the edited record and the SAME residual p. Class target fold can choose any operand source; preserve the disjunction or existential member. Do not force the chosen source to be the edited original slot.

The recursive edit and projection cases use real Head/read exposure. The first recursive needle must be Plain. RecursiveSourcePlain.required derives that from ORIGINAL false gate + Required Origin + exact occurrence under independent semantic/UnionNormal support. It does not give a false gate on the prepared forest. RequiredPrimaryRetentionBoundary is the checked obstruction to such a claim. The finite-cap class subcase also makes every traversed Mu Plain. Neither route authorizes a false gate on an already edited phaseValues forest.

For the whole pass, induct over the actual tail-first fold (AllocatedClassWorker lines 53–68). Compose each new class relation using Rel.trans. The private induction invariant may map phaseValues back to the ORIGINAL forest. The public pass endpoint should start with the literal Required return and the writer's original false traces. RequiredForestPositive.requireAll already handles the SAME original forest index and residual natural path under explicit semantic/UnionNormal/cost/availability/GuardHeap Plain. SupportedParentHistory.selected now retains those final-Scan causal facts at the same historical Parent writer. It does not yet transport native or projection positions.

Use actual inherited-prefix coverage to embed every edited own record into E. Do not identify ordered precheck/kept records with the completed combined classes. EqualityOperationFixed.inherited_prefix and OuterOriginDependencies.combine_covers supply the right fixed point and coverage route. SourceCurrentNormalizedChildSeparation.child_separate then applies to the exact completed E.

Estimated actual class/target/recursive-edit bridge: 400–650 lines after native and projection primitives, plus roughly 100–150 lines for tail-first pass and Required composition. These are unproved estimates. The full no-finite-cap outer case still needs causal exposure/barrier preservation through earlier edits. Strict original child mass, historical i<j and a current cap bound are not a forward global rank. Immediate Top-owner exclusion, general renewal, failed internal states, whole outer completion and production Haskell correspondence remain open.
