# Non-Top direct owner copies: source-only investigation

Status: DRAFT. Root must review the complete plan before implementation. This investigation runs zero Lean, Lake, canonical or runtime commands. It changes no official source. It proves no theorem and gives no supported execution counterexample.

The frozen frontier audit remains unchanged. This separate plan narrows its non_top_copy contract. It tests whether the existing positive ancestry law already rules out an inherited payload that returns unchanged after combination and descent.

## Actual operation boundary

A nonempty ready input strictly loses path height at the actual descent, including a warm memo hit. SourceCurrentOuterInheritedDescent.descend_lt and descend_identity_ne prove this at lines79–104. This compares the child with the COMBINED input to descend. It does not compare the child with the earlier inherited operand.

The earlier inherited operand is combined with the returned row's own field. SourceCurrentAllocatedInheritedPrefix.run_combine64–72 fixes that order. SourceEqualityConstraintMemoAllocation.Valid does not permit an arbitrary fabricated combination or descent result: CombineGood.exact and DescendGood.exact retain the literal pure operations. descendCached_correct254–280 recovers that same exact payload even on a hit. Thus this equality-operation memo is stronger than physical native or Merge storage alone.

Manual source expansion suggests this finite algebra case:

- inherited family R = [[[0],[1]]];
- own family O = [[[0,0],[0,1]]];
- normalized combination C = [[[0],[1]], [[0,0],[0,1],[1,0],[1,1]]];
- actual child-0 suffix classes of C are R again.

The reasoning uses EqualityNormalize.suffixes/addCongruences491–519. R contributes suffixes [0] and [1]. The generated pairs [00,10] and [01,11] overlap O, so completion puts all four length-two paths in one component. The next step adds no new component. No class contains a strict-prefix pair. Child-0 descent drops the singleton suffix from the length-one component and retains [[0],[1]] from the length-two component. This is a MANUAL, UNCHECKED algebra calculation. It is not a formal counterexample, a native trace, a Parent.done receipt, or an owner-copy example. It also is not a permitted arbitrary warm result: a real check must construct the exact physical records and interner receipts.

This illustrates why a finite path-height argument alone cannot prove non_top_copy. The checked SourceEqualityInheritedGrowthBoundary.actual_prefix85–99 already gives a separate actual equality-operation example with growing inherited heights. It explicitly does not claim an outer caller reaches that recurrence. SourceCurrentOuterInheritedGain.collision263–304 already derives a genuine intervening height gain if a non-Top active key recurs. It does not exclude that gain.

## The stronger fact already supplied by actual class execution

The algebra example omits the essential owner-copy premise. For a full returned owner, SourceCurrentActualOwnerPair178–187 already obtains the following law from ONE SourceCurrentRequiredPositiveChronology.pass at the same Required/Pass cut:

For every positive owner path q, there are j, p and original with row.children[j]? = some original, PositiveAt original p, and Rel C (index::q) (j::p).

Because that SAME row belongs to the owner's literal row list, j::p is a positive path of the owner. The target is nonempty. The root path [] is positive because that same row is nonplain. These are exactly the supported premises used by the existing PositiveOwnerPair.same_child_pair. They are not supplied desired runtime ancestry: the checked actual class and native/Merge laws derive them.

The existing theorem counts literal paths and only proves that some class retains two paths under index. The proposed extension counts those SAME finite positive paths modulo the inherited equivalence Rel R. This treats the earlier inherited equalities as existing identifications. It does not count row occurrences or duplicate union paths.

## Exact missing reflection lemma

Let parents be the actual combined physical records. Require coherent fields for each actual physical record and congruenceStep (parents.map Record.paths) = some (parents.map Record.paths). The exact first public lemma is:

Rel (parents.map Record.paths) (index::left) (index::right) -> Rel ((SourceEqualityDescend.records index parents).map Record.paths) left right.

This is a derived relation law, not a caller-supplied reflection oracle. Use NormalizedChildSeparation.single87–97 to reduce the left relation to one replacement with a common suffix. If the two replaced prefixes agree, left=right. Otherwise fixed-point consistency excludes an empty class member. Both nonempty prefixes must start with index. The two distinct suffix paths force the exact SourceEqualityDescend.record to survive its two-path test. SourceEqualityDescend.record_pairs91–99 and records_perm82–89 then put the same replacement into the literal descended class family. Intermediate Rel paths may leave the positive-path set. The proof must not assume support closure along those intermediate paths.

Under the contradictory hypothesis that actual descent equals the inherited records, this proves Rel C (index::left) (index::right) -> Rel R left right.

## One inherited equivalence on both sides

Use R on BOTH domain and target, as suggested in the independent guard audit. Let P be the existing deduplicated literal positive-path list of the owner. Form a finite list of representatives of P modulo Rel R. Use only representatives that belong to P. Include the root representative []. This is one finite list construction; it needs no global finite type of paths and no bound on generated values.

Actual combine_covers83–117 gives Covers R C, so every R relation is a C relation. Fixed C is consistent. Therefore [] is not R-related to any nonempty path: otherwise its lifted C relation and the public single-replacement law would force an inconsistent class containing a strict-prefix pair. This excludes the root class from every source target j::p.

For each domain representative q, the actual backwards law gives a positive nonempty target t with Rel C (index::q) t. Replace t by its representative modulo R. This stays in the representative list with [] removed. Covers R C lifts the replacement into C, so the same relation to that chosen target representative holds.

If two domain representatives map to the same target representative, compose the two C relations through that target. The exact reflection above yields Rel R between the domain representatives. Their representative property makes them equal. The existing SymbolicDriver.relation_cardinality_le94–122 then injects the whole finite representative list into that SAME list with [] erased. List.length_erase_of_mem gives the contradiction.

This uses the actual backwards support relation. It is not an unrelated finite-set wrapper, an assumed rank, or an assumed common anchor. It does not need a separate quotient by C, a second quotient-size comparison, or a support-closure hypothesis.

## Smallest proposed proof scope

The exact two-head pure geometry proposal is in proposed-signature.lean.txt. The public child_reflect exposes the literal descent relation law with only coherent physical records and combined fixedness. The public same_child_payload_ne consumes that derived law internally. It keeps the same literal owner row and backwards law as same_child_pair. It adds the coherent physical combined records, inherited class coverage, and actual combined fixedness. It requires no inherited fixedness. Rel R is an equivalence from its constructors alone. Its conclusion is inequality between actual descended physical payload and inherited physical payload.

The existing candidates/positivePaths/positivePaths_spec/positivePaths_nodup at PositiveOwnerPair23–78 are PRIVATE. Root explicitly permits reuse of that exact small 56-line finite enumeration in a NEW module rather than changing a frozen module or adding a visibility-only public wrapper. The proposed new module is SourceCurrentPositiveInheritedChildSeparation.lean in a new /tmp proof directory. It has exactly two public endpoints: child_reflect and same_child_payload_ne. Keep every old module unchanged. Disclose the copied finite enumeration and pin its exact source range. Do not access generated private names. The remaining helpers stay private.

Use a local Quotient over Setoid(Rel R). Form D = (positivePaths owner).map Quotient.mk |>.eraseDups. This avoids a custom representative-selection algorithm. The target list is D.erase (Quotient.mk []). For the cardinality relation use existential positive representatives q and t with their exact quotient identities and Rel C (index::q) t. This relation need not define a global quotient function. Two witnesses for the same target give Rel R between their target paths by Quotient.exact. Lift it by Covers, compose the actual C relations, and apply child_reflect. Quotient.sound then equates the domain elements. The target root quotient is absent by the consistency argument above. This uses no support closure. Estimated new module is230–290 lines: existing finite enumeration56, public reflection~45–65, local relation/root/quotient helpers~45–65, supported count~45–65, declarations~20–30. Stop for root scope review before exceeding300 lines. No new Finset dependency, general evaluator, runtime ledger, or class framework is needed. Reuse relation_cardinality_le directly. No implementation is authorized until root reviews this exact complete plan and both public types.

If this pure theorem succeeds, an actual non-Top consumer can later reuse the SAME saved Parent/selected certificates route. That route already derives the backwards law, nonplain row, combined readiness/fixedness and Covers. SourceCurrentOuterOriginDependencies.combine_covers gives BOTH inherited and own coverage. ActualOwnerPair.prefix_family49–86 currently selects Or.inr for kept own classes. The inherited variant selects Or.inl at the SAME combined receipt. This is an already checked producer, not a new oracle or missing semantic theorem. Under assumed key equality, actual ready identity readback equates the descended full value with the inherited value. descend_correct gives the literal payload equality forbidden by the pure theorem. This consumer is a later small composition, not part of the current source-only plan.

## Causality and remaining limits

Ready/Valid equality records alone allow the algebraic regeneration candidate. The additional relevant premise is the positive backwards law from the SAME actual class pass, not another naked exact equality-operation receipt. Its checked producer uses genuine native Support, native causal History, Merge positive support and the existing finite-cap/guard contracts at actual query cuts. All those remain genuine premises of the resource-backed writer. The plan does not infer them from physical-only warm tables or from the current reader.

The quotient argument may show that these EXISTING laws already exclude a direct copied-owner recurrence. No additional initial-empty causal writer restriction has yet been shown necessary. Do not claim such a stronger premise is required merely because the algebraic height calculation regenerates R. Conversely, no supported warm or empty-table non-Top counterexample has been produced. The theorem and its relation-reflection/representative construction remain unproved and unelaborated.

Even a successful direct non-Top consumer would concern one immediate same-row owner copy. It would not exclude an older active ancestor after an intervening activation, supply untouched anchors for touched-but-not-copy rows, bound fresh renewals, or prove global termination.

Authorship: I authored the existing PositiveOwnerPair, Required/class positive ancestry and chronology, SelectedCertificates, and ResourceParentWriters foundations. This is a new mathematical investigation. It is not an independent review of those authored proofs. Guard supplied the independent same-R-on-both-sides simplification. Root proposed the local Quotient/list implementation and authorized the small copied enumeration as a planning option. All earlier frozen packages remain unchanged.
