# Source and execution boundary audit

The new required-path certificate applies to strict path prefixes.
Terminal endpoints can remain opaque. The actual current shared preparation
derives this certificate at its literal return. The actual selected own
application edit retains an ordinary function annotation at [2,0].
Original source-to-later-slot lineage and full class-fold composition remain
separate. No theorem here replaces that obligation by Annotated or closure.

The source precheck uses inherited constraints in its guards. It supplies
only the own ordered classes to the class edits. The selected own app proof
therefore needs no inherited annotation-region premise. Its initial typed
cache, original forest, actual compiled subtree and actual edit remain
explicit. Native replacement at an exact endpoint has no general shape
claim. The endpoint can instead matter to a terminal enumeration bucket.
That descriptor connection remains separate.

Two small FirstOrder synthesis probes used the unchanged public Haskell API.
Both ran in project Nix+GMP under a one-minute 4 GiB cap. They are executable
observations, not universal type-safety or termination proofs.

The first probe has library f : (a -> a) -> a, no query arguments, goal B,
and size two. Raw and reduced programRuns, reduced typed runs and
solutionsOfSize are empty. programsOfSize reports Left EmptyGenerator.
It rejects the untypable self-application f f.

The second probe adds erase : a -> Unit, has goal Unit and size three.
The untypable erase (f f) is absent. The distinct returned Programs are:

- erase (erase erase)
- erase (erase f)
- erase (f erase)

The raw programRuns has these three values. Reduced programRuns has five
typed runs, with two Nothing duplicate markers. solutionsOfSize has five
values because two Programs have two typed terms. This behavior matches
the API: programsIn removes duplicate typed terms; programRuns and
distinctProgramsIn track decoded Programs. distinctSolutionsOfSize is the
separate distinct API. The valid reduced typed runs still contain Mu markers
for unfixed Type parameters. The normal generator reports
Left CannotCountConstrainedEdges on this input. That result is not a new
concrete-output defect. The formal count and inverse contracts must state
which accepted terms, typed runs, decoded Programs and error cases they use.

Reproduce the probes with Data.CFTA.Gen.Synthesis. Build these Library and
Query values, then call rawSearchSpace, reduceWithOrder, programRuns,
solutionsOfSize and programsOfSize at the stated sizes:

```haskell
fType = TFun (TFun (TVar "a") (TVar "a")) (TVar "a")
negativeLibrary = Library [("f", fType, ["f"])] [] [] FirstOrder
negativeQuery = Query [] (TCons "B" [])
erasedLibrary = Library
    [("erase", TFun (TVar "a") (TCons "Unit" []), ["erase"]),
     ("f", fType, ["f"])] [] [] FirstOrder
erasedQuery = Query [] (TCons "Unit" [])
```

The current Synthesis source SHA is
dfffbf454516649e115d890e65b6289217dbcf352ccb08e86415d719b32fbc3a.
The earlier source-type-boundary packet retains the full three-encoding
raw/reduced positive replay. These two additional probes are not part of
the Lean compatibility checker. Their finite outcomes establish no bound
for arbitrary source reductions. No production Haskell fix follows from them.

---

# Next actual Required-to-Parent composition

The next proof preserves ordinary function annotations at [2,0] through
the actual pass. It uses current source certificates and a retained path.

## Exact current producer and missing transport

`SharedRequiredPathShape.receipt_shape` takes ONE actual
`SharedScanRequiredNumeric.Receipt`, current Context, Values and ClosedValues.
`RequiredAnnotationRetention.shared_preparation_annotation_ordinary:102`
then derives Ordinary for every annotation child of each ordinary operand
at results[2], provided a selected path [2,0,descendant,...] exists.

`RequiredAnnotationEditRetention.selected_application_avoids_function_annotation:150`
derives that no selected record endpoint is a prefix of [2,0], from the
actual application occurrence, its precheck receipt and SAME ScanReads.
Theorem :165 handles ONE nested EditNode at [2,0], for arbitrary inherited
payload. It does not derive nested calls or preserve shape through a Class.

The smallest useful new invariant is a local shallow predicate:

```
FirstOrdinary value :=
  forall entry rows depth free, value = node entry rows depth free ->
    forall row in rows, forall annotation,
      row.children[0]? = some annotation -> Ordinary annotation
```

Use this together with the existing Program ValueFields certificate. Empty satisfies it vacuously.

## Candidate next module/API

`SourceSynthesisRequiredAnnotationClassPass` should expose
`class_first_ordinary`, `fold_first_ordinary`, `pass_first_ordinary`:

```
pass_first_ordinary lib actualPass ready available closed coherent routes
  avoids initialFirst :
  forall function, results[2]? = some function -> FirstOrdinary function
```

Here actualPass is literal `AllocatedClassPass.Pass kept prepared
requiredChecked merge results after saved`. `ready` is Type SharedReady at
that SAME Required return; routes are the existing source Type ForestPath
facts for kept records; `initialFirst` is the immediately preceding Required
producer. `avoids` is the derived endpoint exclusion above, not retention
at future heaps. A top application-specific theorem should derive it from
the occurrence/precheck/ScanReads rather than expose it as a new assumption.

For each actual Class.edit, start with compiled_placed at [] and descend
through its actual EditList, rows and children. child_placed supplies the
literal [2,0] address. Prefix exclusion rules out editAt there and at its
ancestors. Apply below_ordinary at the annotation, then actual row/node
readback to retain all surviving annotation heads. NativeTypeSharedEdit supplies heap/route facts at actual earlier prefixes.

Fold executes its tail first (AllocatedClassPass:28-30). Reuse the exact
proof order of NativeTypeClassPass.fold:74: derive tail readiness, resident
closed forest and ForestRoutes, then run the head. ClassSlotFields:143-175
already uses this order. Its mixed fields and HereditaryClassFields preserve
Annotated fields, not Ordinary annotation heads; they cannot discharge the
new conclusion by themselves. TypePath.annotated permits opaque annotations.
Final Pass propagation either keeps this forest or erases it to Empty.

## SAME Parent endpoint

A second small attachment can inspect ONE SharedParentNumeric.Receipt.reads
(:45-60). In live -> SharedLocal.Reads.classes -> Classes.Reads.completed,
extract the SAME preparation and Pass, apply the new theorem, and rebuild
the result through MkEdge.Receipt.children (:70). That equation returns the
literal local children or [Empty]. Existing SharedParentWorker parent_fields
(:124) is the exact coupling pattern. No fuel/read-schedule reindex is needed.
FirstOrdinary applies to the actual function operand;
its selected row and EdgeInputs.children at zero then give Ordinary at the
annotation child. An actual successful child row excludes Empty as before.

## Separate unresolved cuts

1. Retained membership: source guard membership alone does not prove a path
is in `paths (kept.map Record.paths)`. Actual Scan can skip classes. A record
in kept gives membership by canonicalClass and signed map; deriving that
record for every later bucket needs actual Scan branch provenance or an
appropriate skipped-class semantic discharge. Do not assume all own paths
are retained. Current preparation receipts already expose the real kept list.
2. Later-slot lineage: this composition covers the SAME local/Parent return.
It does not identify every subsequently selected enumeration slot with that
operand after outer descendants, cached hits, child allocation or hooks.
Existing ValueFields/NodeFields/History retain annotation validity but not
this stronger ordinary-head property. A separate actual origin transport is
needed; accepted startup fields alone do not identify arbitrary later slots.
3. Model existence: full bucket retention is not a proof that every output
has a satisfying assignment or that every accepted source term is generated.
Source coverage, depth/order/inverses and native/Haskell bounds remain open.

---

# Joint finite typing after local annotation retention

Read-only source audit, 2026-11-09 23:30 CET. No builds or source edits.

## Current contracts

- `lean/MicroCFTA/SourceCurrentSharedRequiredPathShape.lean:55` attaches strict-prefix shape to the SAME observed shared Scan/Required preparation. `lean/MicroCFTA/SourceSynthesisRequiredAnnotationEditRetention.lean:150` excludes every prefix of `[2,0]` from actual selected own app records. Its consumer at line 165 retains an ordinary function annotation at the actual edit endpoint. Inherited payload is arbitrary. The consumer still uses current input ordinariness, typed readiness, routes, and derived compiler placement. It is local; it does not yet establish whole traversal retention or an enumeration bucket certificate. Ordinary permits Empty.
- `lean/MicroCFTA/SourceSynthesisOriginalCheckedSharedProgramCount.lean:49` retains one original build, actual shared return, graph/reads, Post and hereditary fields. Lines 88-92 state: IF a finite term belongs to the returned root, its repaired Program projection has `signed.toNat` components. This does not supply an accepted term. `firstOrderRaw = .ok expression` certifies construction success.
- `lean/MicroCFTA/SourceCurrentAllocatedPartialMemoSound.lean:29` defines NodeLaw. It narrows result language into original language and gives inherited-conditioned equivalence. A witness can pass through this equivalence; the law does not construct one.
- `lean/MicroCFTA/SourcePruningEnumerationSharedPreparedPartialOutput.lean:33` derives actual stable partial rendering from the SAME output resource packet and explicit root allocation. Lines 57-61 quantify over assignments: Satisfies current cache implies Satisfies rendered cache and Completes the partial result. There is no existential model premise or conclusion.

`lean/MicroCFTA/SourcePruningEnumerationRecursivePacket.lean:21` contains Context, storage safety, pending-reference validity, cache validity, dependency order and bounded metadata. `lean/MicroCFTA/SourcePruningEnumerationObservation.lean:19` makes PendingRealized mean decoded, available and closed. Neither property establishes domain inhabitation. The metadata Typing parameter does not itself assert a typing judgment.

`lean/MicroCFTA/SourceSynthesisOwnChildTerminals.lean:81` already supplies actual own terminals for app Type slots 0/1 and filter slot 0. Its header explicitly excludes the component annotation case. These direct-slot facts and local function-annotation retention are useful inputs to the source-wide retention proof.

## Exact remaining existence obligation

For an ACTUAL emitted concrete Program branch of the public synthesis policy, construct one finite assignment at its SAME `output.caller.checked.native.machine.heap` and `output.cache.core`. It must satisfy all native domains, representative equalities, suspended constraints and residual guards together. `lean/MicroCFTA/EnumerationCorrectness.lean:142` is the existing Satisfies predicate for this obligation.

This must use the original-source execution and actual branch. Arbitrary user-stop OutputResources can describe partial Program output, so that generic packet cannot imply the stronger public Program claim. The resource entry at `lean/MicroCFTA/SourcePruningEnumerationSharedPreparedSelectedDriverResources.lean:39` fixes the actual root and current reservation, but does not add this model. The source startup connection is `lean/MicroCFTA/SourcePruningEnumerationSharedPreparedSelectedDriver.lean:137`.

The source-derived bucket-retention chain must also restore original-root meaning for that assignment. The current local backward interfaces are `lean/MicroCFTA/SourcePruningEnumerationSharedSelectedEdgeNeutralResourceSoundness.lean:35` and `lean/MicroCFTA/SourcePruningEnumerationSharedPreparedOpaqueLanguage.lean:172`. Their retention gates and final Satisfies hypotheses remain explicit. Backward preservation and existence are separate obligations. Individual domain witnesses do not automatically solve shared finite type equations.

`lean/MicroCFTA/EnumerationAssignment.lean:80` constructs assignments only when every pending slot has `node = none` and `scs = []`. It cannot directly solve native opaque Type handles. `lean/MicroCFTA/InternedGuardedLanguage.lean:24-29` interprets Mu by a least language of finite terms. Source allTypes has finite alternatives (`lean/MicroCFTA/SourceSynthesisTypeSyntax.lean:93-100`), but that fact does not prove that every later intersection or joint constraint system is inhabited.

## Small proposed positive theorem

First formalize the already replayed R210 FirstOrder fixture: the sole library member is `f : a`; query argument is `x : A`; goal is `B`; size is 2. Use ONE returned expression and its actual original build. Define the full finite typed term

```
w = filter(B, app(B, (->), f(->((->), A, B)), x(A)))
```

Proposed, not implemented: `fixture_finite_witness returned built` proves `InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value w` and `Projection literal Prod.fst w (app (var "f") (var "x"))`. This is a concrete source witness proof, not an inference from construction success. A/B and Arrow membership must be proved through the actual source universe and guard equations.

Transport w through the SAME accepted shared return's NodeLaw using its initialized empty inherited payload. Then apply the pure `SourcePruningEnumerationRecursive.initial_packet_models` in `lean/MicroCFTA/SourcePruningEnumerationInitialModel.lean:31` to obtain a model of that SAME startup cache. This supplies concrete raw/reduced witness support. It does not establish a model for every later selected output; the general source-specific joint finite completion theorem remains open.

## Marker and projection scope

`lean/MicroCFTA/SourcePruningPartialMatchSemantics.lean:14-24` makes Completes.truncated permit any full term. It cannot produce a typing witness. `cfta/README.md:443-447` explicitly states that descendant constraints can be dropped at truncated Mu and that a marker is not evidence of nonemptiness. Productive opaque Type values may remain opaque and still admit finite completions. No requirement that every marker become ordinary is justified. Several finite typed terms can project to one Program; that multiplicity is separate from Program size or finite typing soundness.
