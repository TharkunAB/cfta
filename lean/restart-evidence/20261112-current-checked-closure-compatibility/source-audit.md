# Current checked pruning and ordinary startup

Base: 77be632308956b58f39ff12281b0d3f4008b6e17. Integrated main:
e53852064d3ef5a2eafec47d754c27504b11de5f, including PR210/211.
The full formalization goal remains ACTIVE. No production Haskell changes.

## Checked modules

- SourceSynthesisCurrentCheckedHereditarySharedCompletion: 208 lines; 1 laws; SHA256 78bc0711b6855c3d0ded9f519ae32eba59e3930a63e08856654c535a961317e5.
  - MicroCFTA.SourceSynthesisCurrentCheckedHereditarySharedCompletion.accepted
- SourceSynthesisCurrentOrdinaryInitialModelWork: 149 lines; 1 laws; SHA256 824f75f7527c2d4b76a42d55c7d271641c70c4481e44f91e2be9910a53905b3c.
  - MicroCFTA.SourceSynthesisCurrentOrdinaryInitialModelWork.uses_native_initial
- SourceSynthesisCurrentOrdinarySharedModelWork: 230 lines; 1 laws; SHA256 dac4eae9b8725cd17c64721bf74cddf0757b70e0274fb6c36a31c0338fd49d44.
  - MicroCFTA.SourceSynthesisCurrentOrdinarySharedModelWork.uses_checked_native_initial
- SourcePruningEnumerationSharedPreparedRecursiveChildPolicy: 200 lines; 4 laws; SHA256 524af07316926d35a196cef73cebbed9769bcf8341bccac29b4551f1c50166b8.
  - MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild_shallow
  - MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runWithChild_shallow
  - MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resume_zero
  - MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resume_prepared

## Exact current checked endpoint

CurrentCheckedHereditarySharedCompletion.accepted invokes the current caller
initializer once. It retains the ENTIRE initializer tuple: one actual build,
preparation Receipt/cache, conjunction Fields, full Context/inventory/caller/
modeled initial globals, Facts/Available/ProgramValue, growth/issued extension,
full physical guard origins, same inherited live identity/readiness, closed
root and Original. Current whole native Type fields and Mu store are observers
of that SAME build. Cold TypeReady/SharedReady, support, union normality,
causal history, costs, closed stores and idle facts are derived internally.
All Type indices use the once-encoded library.

One generic rank producer supplies the same checked result. The theorem uses
its actual request, envelope output, first phase, phaseNeed and forecast cover.
Room bits of that cover remains an explicit condition. It returns base
literal ranges; all larger outer fuels produce the SAME result and complete
state, with literal ranges at each larger fuel. Inner fuels remain the exact
computed need. One next/final/graph retains Checks, full endpoint Reads from
initial globals to final, Post, Frame, Fits, full physical forecast guard Heap,
Available, semantic NodeLaw, SharedReady, Type-profile GuardHeap, History,
closed result, NodeFields and whole ValueFields. No future Ready, ValueFields,
build, model or completed worker is assumed. No second worker is run.
The forecast physical Heap and Type-profile GuardHeap remain distinct facts.

## Original Program and startup composition

CurrentOrdinaryInitialModelWork.uses_native_initial combines current
uses_root_member with ONE cold CurrentInitialModelWork producer. Its actual
current source whole term transfers through closed_language at that SAME
returned build. It retains ordinary Typed, exact original Program/goal
annotation, Projection/toProgram/count, COMPLETE initializer/startup tuple,
the existing universal counted observer, and an actual assignment for the
same term. It does not execute a pruning worker or require Room.

CurrentOrdinarySharedModelWork.uses_checked_native_initial performs the
stronger checked composition. It takes raw Eligible, tokens.Perm ORIGINAL
queryArguments, empty libraryAvoid, bits/budget, empty-pending metadata,
formulas/solver, ambient and residual meaning. It derives ordinary Typed and
an actual current source return. ONE current checked producer returns the
complete initializer and checked endpoint above under its EXACT Room.
closed_language observes that same build. Its returned inherited live identity
makes inherited satisfaction true. The SAME NodeLaw transfers the exact
source annotated term to the returned result. ONE postworker startup producer
uses that result/heap/next inventory/after caller/final globals. It returns the
same handle readback, Packet, canonical state, initial slot, waiting,
candidate expansion, graph carrier and references, and one actual assignment
for that SAME term. The assignment satisfies the initial graph, has origins,
refutes empty pending, and has pending size exactly N and work
(N+1)*N + (if recursiveBoundary result then 0 else 1).
N is complete annotated-term size, not Program.components. Formula-instance
transport is private and preserves the public statement. No independent
endpoint/term or old/current Context equality is joined into the proof.

This is the strongest new positive prefix: an original admitted program
passes through CURRENT construction and checked pruning to a valid startup
with its same witness and complete state/cache receipts, provided its computed
storage forecast fits. It does not prove full enumeration or an original-input
bound for its capacity, traversal, alternatives or total work.

## Recursive child policy

SharedPreparedRecursiveChildPolicy defines resumeWithChild/runWithChild and
an actual eagerChild adapter using existing Output/Failure/HookResult types.
Each reached branch performs the same selected prefix and one checked common
preparation. Smaller-depth callbacks use that same child policy. Existing
continueWith, recordTypes, finish, Fits/narrowing, native endpoints, metadata,
Caller and full Memos remain. Four laws prove ENTIRE old shallow HookResult
equality at every depth and decision, full entry equality, exact zero-depth
cases, and the exact prepared-prefix call. The sole repair adds explicit width
arguments inside one function-equality proof; all three operations and four
public statements are unchanged. This module does not prove eager semantic/
resource preservation, source lazy demand/order or default equivalence.
Existing finish can discard processed receipts on complete outcomes.

## Validation, Haskell and remaining scope

All four strict source packets pass. Full Audit passes: 5822 live modules,
five affected, 4819 imports, 94008 axiom reports. All five portable checks
pass from /tmp. All 261283 old Audit bytes remain after four imports. Effective
memory.max and memory.high are 4294967296; memory.swap.max is zero. One Lean
thread and the existing repository Lake cache are used. No binary archive is
copied. These are manually specified Lean source models. Haskell compiler,
extraction and runtime correspondence are not established by these checks.

No Haskell source or Cabal file changes. External owner post1182 reports a
runtime-reproduced Liquid duplicate-name defect on main e53852064: contradictory
refinements are conjoined and entailments become vacuous; separate readers use
first/each/last types. FINDINGS records the exact report, controls and intended
last-entry type AND refinement repair. The owner holds
fix/liquid-repeated-argument-names; no published repair is reported yet.
ROOT has read the report and has not repeated that runtime experiment. Liquid
arguments have no required-use rule; the Hectare route has required uses.
Do not duplicate the external repair. Prior PR210/211 focused Nix/GMP checks
remain recorded: fourmolu passes and 16 synthesis examples have zero failures.
No full Haskell suite/corpus/benchmark is claimed. Historical pins remain.

Next genuine gap is eager CPS semantic/resource preservation. Existing child
resource proofs hard-code shallow ChildDispatch.run; their bucket-length cost
is not a descendant/all-alternative bound. Source reverse generalization,
whole traversal and original-input capacity/work/depth, source order and
multiplicity/lazy demand, reduction/refold/weights, both inverses, full guards/
signed/Word/Int/errors and refinement/training remain explicit separate targets.
Default synthesis does not call boundDepth. Source success alone need not
imply inhabitance; this positive theorem supplies an admitted Program witness.

## Frozen composition plan

The following read-only plan is retained for provenance. The checked 230-line
composition above now implements its route. Its text adds no public premise.

# Current ordinary witness at the same checked startup

2026-11-12 16:31 CET. Read-only audit. No compiler, source, repository, Git, Haskell, root-doc, or evidence changes. References below use `lean/MicroCFTA/`.

## Result and exact inputs

There is no new mathematical premise for this composition. The existing current root witness and the new checked producer have the same current firstOrderRaw input. The generic startup producer accepts the returned full Post endpoint directly. Do not call CurrentCallerInitialization or CurrentInitialModelWork again: either call would select a second initializer instead of using the checked producer's initializer.

The smallest next source is `SourceSynthesisCurrentOrdinaryCheckedInitialModelWork.uses_checked_native_initial`:

```lean
variable {Typing : Type}
variable [DecidableEq FullSyntax.Formula]
variable [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
theorem uses_checked_native_initial
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {program : Program}
    {tokens : List (String × Ty)}
    (unpruned : lib.libraryAvoid = [])
    (eligible : SourceSynthesisCurrentProgramAdmission.Eligible
      lib query true program query.queryGoal tokens)
    (covered : tokens.Perm query.queryArguments)
    (bits budget : Nat) (metadata : Metadata Typing)
    (emptyPending : metadata.pending = [])
    (ambient : InternedGuardedLanguage.Env Symbol)
    (residualMeaning : Constraint → Term Symbol → Prop) : ...
```

`Symbol` is Label FullSyntax.Formula, `Constraint` is the existing source Constraint, `Node` is Value Symbol Constraint, and `literal` is the Label program literal adapter. The Symbol equality instance is inferred from Formula equality as in the verified historical ordinary checked wrapper. No extra symbol-name freshness, unique-query-name, successful build, member, model, Ready, worker, or future capacity supplier is required. Demanded raw images/results and original last-lookup query types remain in the EXACT current Eligible certificate. Original token multiplicity remains in covered; it is not replaced with a permutation of already-normalized tokens.

## One source witness, one checked producer

Call `CurrentRelevantAdmission.uses_root_member:296-350` ONCE. It returns ordinary Typed, current raw success at Int.ofNat program.components, and one body. Define `whole := .node (literal "filter") [SourceSynthesisPr210TypeReflection.candidateRigid query.queryGoal, body]`. Preserve source evaluate membership, exact whole.atPath [0], Projection whole program, toProgram whole = program, and the exact component count. Do not replace candidateRigid by historical rigidTerm: the current reflected source is different.

Call `CurrentCheckedHereditarySharedCompletion.accepted:53-208` ONCE with that SAME current raw success. This internally uses ONE current initializer and ONE rank producer. Preserve its ENTIRE outer existential prefix, not only its preparation Receipt: fields/cache/value/heap/built, conjunction Fields, full initial Context/inventory/globals, Facts/Available/ProgramValue, growth/issued extension, full physical guard-origin heap, inherited identity/readiness, closedness, and Original value. The inventory remains indexed by that SAME built proof.

The returned computed Room implication remains INSIDE these witnesses. Its request/output/first/need and cover are exactly the checked producer's definitions at caller(bits+2)cacheheap and its actual seed. No fixed-width Room discharge is supplied by ordinary admission. Use the returned implication once to select one result/after/full endpoint.

## Membership at the same value and result

`LabelProgramBuildRoles.mapSyntax_ordinarySymbols` turns the SAME built equation into build(mapSyntax literal expression)[]empty=.done value heap. `InternedGuardedExecution.closed_language:201-205` then transfers the SAME evaluate proof to native meaning at value for the chosen ambient. This is a build observer, not a second build producer.

The guard interpretation is `H := SourceEqualityPCSGuard.holds formulas solver`. Its exact definition at SourceEqualityPCSGuard:39-47 is raw PCS equality satisfaction AND the actual evaluateGuard result .yes. The theorem is relative to the supplied formulas and solver. It does not infer an external theorem prover's correctness or allow a different arbitrary H after the worker has been executed.

`PartialMemoSound.NodeLaw:29-36` gives result → original membership unconditionally, and result ↔ original under Sat term request.inherited.payload. The returned SAME emptySame identity says emptyValue cache=.live identity[]. Thus that payload is some[], and Sat holds for EVERY term. Reuse this returned identity; no second preparation or new inherited supplier is necessary. Apply the equivalence in the reverse direction to retain whole at result. In fact the same argument yields equality of the complete original/result languages for all ambient and term under H, if exposing that small stronger observation is useful.

The exact goal annotation and Program projection belong to whole, which is unchanged by NodeLaw transfer. Neither a newly chosen equivalent annotation nor a new projected Program is needed. Preserve original native membership and result native membership explicitly.

CurrentProgramStructure.current_root_structure:235-255 additionally supplies ProgramSize program.components expression. The generic OriginalProgramTermSize.build_accepted:34-46 then proves the projected component count for EVERY H-accepted result term, using NodeLaw's result→original implication and the SAME mapped build. This generic helper is not tied to historical firstOrderRaw. An optional all-result counted-projection clause needs no second current or historical source producer and can use count=program.components directly.

## Postworker startup at the actual returned globals

Call `SourcePruningEnumerationRecursive.initial_packet_models_origins_work:52-102` ONCE with formulas, solver, next, after, final, metadata, result, post.context, resultAvailable, resultClosed, and emptyPending. These are the SAME full next/final/Post/after witnesses from the base checked graph. Do not pass initial inventory, initial caller, globals, or only final.query. This is postworker startup; CurrentInitialModelWork.accepted:40 constructs cold raw startup and cannot replace it.

The producer returns one handle with encodeNode result=some handle and actual lookupNode in after's heap. Retain its full startup clause verbatim. The concrete Cached startup is:

```lean
⟨EnumerationState.initial handle,
 fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary result else false,
 fun _ => none⟩
```

Retain Packet formulas solver next after final metadata startup, Canonical, exact slot0 .unenumerated lookup, suspendedBound=0, canonical waiting, exact candidate/flag agreement for every slot, CarriesGraph at0, and ReferencesCarry. These are current operational invariants. A semantic model does not replace them.

Apply the returned models function ONCE to H/ambient/residualMeaning/whole/resultMember. Retain ONE assignment with assignment0=whole, Satisfies(handles H ambient afterHeap) residualMeaning assignment startup.core, pending refutation, and AssignmentOrigins whole startup.core.counter assignment. `NativeLanguage.handles:19-23` uses actual lookupNode and independent native meaning at that same afterHeap. The ambient is the SAME one used in original/result membership. residualMeaning is arbitrary; the startup state has no residual attachment, so no residual-model supplier is required.

The SAME assignment satisfies literal P=N and P≤N, where N=NumberedTerms.size whole, and W_N=(N+1)*N+(if recursiveBoundary result then0 else1). This is a pointwise annotated native size. It is not Program.components, a bound on all witnesses, actual total work, or a recursive-depth certificate. The flag remains conditional on the actual returned result; no ordinary-nonrecursive premise is added.

## Complete retained endpoint and instance transport

After Room, preserve ALL checked outputs unchanged before appending membership/startup: base literal ranges, stable larger-fuel SAME result/after equations, larger literal ranges, next/final/graph, Checks, canonical endpoint Reads globals→final, full Post/Frame/Fits, physical forecast guard-list Heap, result availability, NodeLaw, SharedReady(encodedLibrary lib), Type-profile GuardHeap Origin(encodedLibrary lib), History(encodedLibrary lib), result closedness, NodeFields(encodedLibrary lib), and ValueFields Origin(encodedLibrary lib). The full initial physical source guard heap is independent of the Type-profile invariant. No old/current context equality or raw-lib Type-origin substitution is valid.

There is one known elaboration issue, not a missing premise. NodeLaw captures the canonical Formula decidable-equality instance; current source witnesses use the public arbitrary instance. The verified historical OrdinaryCheckedInitialModelWork.meaning_decider_eq:62-72 transports meaning between them by congrArg over Subsingleton.elim. Its use at190-214 already solves the same exact issue without restricting the public instance or changing H. Reuse this private transport locally, because the historical private theorem is not public. Use it for original→canonical result transfer, result→public transfer, and any all-result count clause.

The startup producer's returned Refutes can also capture its canonical Formula instance. Rebuild that vacuous proof directly from CURRENT emptyPending instead of transporting the returned proof: intro group member; rw[emptyPending] at member; cases member. This is the verified historical repair at OrdinaryCheckedInitialModelWork:220-223. The SAME returned assignment and every other model field remain unchanged. No axiom, linter suppression, new public premise, or duplicated model producer is needed.

The full source implementation should mainly copy the checked producer's complete public tuple and append the generic startup packet. The two actual source producers and one startup producer are each called once. All other calls observe their SAME build or result. This is the smallest complete current ordinary checked startup composition; no additional mathematical bridge is open.

The remaining boundaries are the actual computed Room test at fixed width, global prior-hook/earlier-sibling completion, complete enumeration and output coverage, default eager-order/control correspondence, and Haskell extraction/runtime correspondence. The external Liquid duplicate-name repair is owned externally and is already in FINDINGS; this audit neither duplicates nor expands that investigation. ROOT reports the unchanged checked208 producer STRICT PASS1 at SHA78bc0711b6855c3d0ded9f519ae32eba59e3930a63e08856654c535a961317e5.
