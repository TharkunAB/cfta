# Actual optional-binder input positions

Source-only review, 2026-10-21 03:01 CEST. This package owns zero Lean jobs, proof pairs, or examples. The proposed new endpoints are unproved. Existing frozen components stay unchanged.

## Recommended primitive

The following actual-operation contract is the smallest useful next target with existing derived entry certificates:

```lean
(pair : Nat × Nat) (body : Node) (before : Heap)
(semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
(available : Available before body)
(bounded : SourceCurrentConstrainedCap.Cap Plain depth body)
(guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain before)
(earlier : SourceCurrentNativeMuPublication.History empty before)
(result : Node) (after : Heap)
(actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before = .done result after)
(path : List Nat)
(positive : SourceCurrentRequiredPositivePosition.PositiveAt result path)
-- conclusion:
SourceCurrentRequiredPositivePosition.PositiveAt body path
```

Plain is the exact predicate SourceMemoGate.plain guard=true. The natural path is unchanged. Source and canonical row indices may differ. The theorem does not infer a successful operation from support premises: actual supplies its literal completed outcome. Consequently Ready and complete-cache Covered are unnecessary. SemanticHeap supplies the actual Context and decoded depth heap. No future history, final positional invariant, new public evaluator, or eventual native result is a premise.

The guards premise can be weakened locally to the existing SourceCurrentHereditaryConstruction.MuStored Plain before. GuardNative.stored derives that predicate from guards at lines26–31. Retaining guards initially gives the direct match to the actual outer/native support producer. This is a representation certificate about earlier Mu payloads, not a desired position-output law. A proof can minimize this premise during implementation.

No PlainDomain or native Bindings premise is required for this primitive. maybeMu performs one literal old-pair substitution, not a native bound-name read. Bindings Plain is a separate premise for the later native reference branch. No ProbeFree, source weight, maximal classifier, or positive request rank is required for one-way positions. Marker references have no PositiveAt even when their names alias another free reference. Their genuine physical availability is still required in the private general callback lemma; Depth and ordinary marker availability are already produced by existing source facts.

The smaller phrase “actual .done + finite Cap + causal history” omits essential physical input statements. The current public source endpoints do not derive SemanticHeap and Available body from a bare History object. The proposed theorem retains those facts. Causal history also does not itself expose a public GuardHeap Plain theorem in the reviewed APIs. A new history induction could derive that initial scalar certificate by reusing actual callback-profile production and name-map invariance, or actual source startup can supply GuardExecution.closed_heap and actual-prefix preservation. Do not silently claim that missing public composition is already checked. The explicit existing guards premise keeps this task bounded.

## Exact existing readback removes the warm-winner problem

SourceRecursiveIntersectionMaybeMu lines21–36 defines the actual callback as stored substitution old→reference marker followed by root filtering. construct executes the literal Depth callback, then the repaired ordinary callback, then request true. maybeMu returns body unchanged if its exact old pair is absent. callback_eq/construct_eq/maybeMu_eq, lines40/48/59, preserve the exact encode, leaf pool, all intermediate heaps, hit/pending branches and final request.

The strongest useful prior art is SourceCurrentNativeConstructReadback.construct, lines47–92. It consumes an ACTUAL construct.done, initial SemanticHeap, Available body and earlier causal publication history. Its Readback receipt, lines28–44, fixes the CURRENT raw ordinary substitution, its exact filter call, the current ordinary probe, the full final selected Mu payload, result=finish true selected, and the operation-derived causal history at return. It keeps those witnesses in one existential tuple. It does not identify the selected stored body with the current incoming body.

The new SourceCurrentNativeStoredMuPositivePositions.reached/source, lines70/84, derives exact SAME-cell readback positions:

```lean
PositiveAt (finish smart (.mu entry storedBody depth ordinary)) path ↔
  smart=true ∧ usesLocal depth ordinary=false ∧ PositiveAt ordinary path
```

The current ordinary probe in Readback is the exact depth/ordinary pair of the selected cell. SourceCurrentNativeRequestProbes.request_probes derives that alignment. It uses full physical readback; equality of just keys or reference identities would be insufficient. A used winner is opaque by actual DepthHeap.Correct and retained_of_used. An unused winner returns eraseSelf ordinary by history_unused, including a retained earlier writer. This is already a literal source-derived law, not an unproved body/probe positional invariant.

Thus the only new path proof needed is CURRENT callback result positivity→CURRENT incoming body positivity. Readback's arbitrary-view epsilon Origin equivalence is useful receipt data but is not a complete same-path structural theorem by itself. In particular, do not convert an observational Mu read into a PositiveAt constructor.

## Small private proof decomposition

1. Prove backward PositiveAt for actual repaired stored substitution. The statement takes initial Facts, Available input, Cap Plain d input, MuStored Plain, physically available replacement values and hereditary Plain replacement annotations. It concludes, from an actual execute.done, that each returned positive path already occurs in the original input. This slightly general statement is sufficient for replacing old with a bare marker. It does not assume a desired origin relation.
2. Closed input leaves are exact immutable captures. InternedStoredSubstitutionScope.global_lookup and input_closed, together with Context/coherence/availability, retain the full captured value. Do not identify a repeated leaf occurrence index with encode.slot's first matching identity index.
3. An open ordinary input retains its source row guard and ordered child calls. SourceCurrentStoredSubstitutionOrigins.node, lines87–118, exports NodeRows. NodeRows, lines58–74, fixes sourceIndex separately from the returned canonical index, the actual buildEdges prefix, selected original row, Calls on its children, literal makeEdge, suffix and full symbol/guard/length equations. Calls.indexed, SourceCurrentStoredSubstitutionCalls lines39–60, extracts the SAME child index and actual prefix/call/suffix. Apply the structural input induction to that exact child. A nullary positive row uses the preserved guard directly.
4. An open union adds no natural path step. SourceCurrentStoredSubstitutionOrigins.union, lines121–165, fixes actual ordered Calls and literal makeUnion. Use structural positive inversion of actual makeUnion to select an actual operand at the SAME path, then Calls.indexed and the input induction. Such an inversion must include ordinary merging, flattening, canonical duplicates and warm full-record readback. Existing checked private makeUnion_positive in MergePositivePosition and the BinderFree component are proof templates; their generated private identifiers cannot be imported. The public UnionRows arbitrary-view Origin clause is not a license to unfold opaque input Mu barriers.
5. The open Mu case stops. ConstrainedCapNativeScope.mu_annotated, lines20–23, derives hereditary Plain for the COMPLETE incoming Mu from its finite cap. ConstrainedCapStoredSubstitution.execute, lines162–173, instantiated at depth0, derives hereditary Plain for its literal reconstructed return from MuStored and Plain replacements. RequiredPositivePosition.not_plain contradicts a positive output. This handles nested smart cleanup and earlier warm winners without a full new positional heap or a raw-body↔ordinary theorem.
6. Literal references either remain references or are replaced by hereditary Plain values. They cannot create a positive path. Empty cannot create one. Preserve the actual substitutions and the initial representation store through intermediate child calls using the existing Checked.stored certificates and physical Verified effects.
7. Specialize the private substitution law to old→reference marker. Actual root filtering only removes bare-reference alternatives; it cannot create positive positions. Derive callback backward positivity from the SAME actual raw return and filter. Then use ConstructReadback on the ACTUAL maybeMu used branch, eliminate the used-local positive output via the stored observer, and apply the CURRENT ordinary callback law. The pair-absent branch is literal identity.

This is a finite input value/list/edge induction, not a generic all-source heap evaluator. Estimate 250–400 lines if the existing exact row-call receipts avoid recopying the whole encoded build proof. Actual structural union inversion and required intermediate store support can increase that estimate. The theorem should remain one public primitive; private constructor facts are sufficient.

## Why the finite cap matters

PositiveAt treats every Mu as opaque. A generic input may contain an open raw Mu with constrained stored rows. encode at InternedStoredSubstitution lines58–68 turns that open Mu into a SMART binder. Cleanup can expose its rows at a path which was blocked by the original Mu. Causal construction alone does not turn this opaque observer into a complete native source observer.

A candidate counterexample shape, not checked here, is union[oldPair,rawMu y(constrainedRow[otherReference])], where otherReference differs from oldPair and y. The actual encoded nested smart binder has no use of its own local and can expose the constrained row, while the outer oldPair occurs only as a bare union alternative and is removed. The input has no positive paths through that Mu. This shape is excluded by Cap Plain because the constrained Mu is not hereditary Plain. Do not cite this sketch as a new checked example.

The existing CHECKED PositiveNativeSupportKernels.actual_opaque_mu_counterexample is stronger evidence against the unrestricted full-query shortcut, not a checked maybeMu-only example: it starts two actual closed source-built raw Mu operands and empty native tables, then actual native execution exposes a nonplain ordinary result. Neither opaque operand has PositiveAt. That theorem does not refute the proposed finite-cap primitive. It also does not establish a Haskell defect.

PlainCap is sufficient for the private Mu stop only when the earlier conditional representation store is available at the actual reconstruction entry. Physical Facts/Good alone do not establish MuStored for arbitrary polluted earlier payloads. Scalar GuardHeap does not prove arbitrary same-position equality between stored body and probe. It is used here only to derive hereditary Plain returns in a region whose input cap already requires hereditary Plain. The positional work remains in the exact ordinary/union input recursion.

No general native request law, actual class Rel transport, global renewal, termination, outer completion or production Haskell refinement is proved by this investigation. The capture/encode programs are generated source syntax. The result does not identify them with the original user program.
