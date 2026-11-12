# Default partial agreement and integrated synthesis contracts

Base: 22de6369f7d5d9a72764fa7f2a69fbfb4aea9a8c. Integrated main:
e53852064d3ef5a2eafec47d754c27504b11de5f. Local merge:
89a77f0637f25f98ea52525d59b7dc7453c54da3. PR 210 and PR 211 are merged.
The persistent full formalization goal remains ACTIVE.

## Verified current modules

Three new modules contain 675 lines and nine public laws. Every own-source
checker verifies source hashes, exact public theorem names and namespaces,
and standard axioms only. No old source definition or theorem was removed.

- SourcePruningEnumerationDefaultPartialAgreement: 389 lines; 1 laws; SHA256 fd281edef9382688b1a5b8cb08146b0c5b8b7a2e625378e0bdeca43984978ca0.
  - MicroCFTA.SourcePruningEnumerationDefaultPartialAgreement.default_finished_render_partial
- SourceSynthesisPr210TypeReflection: 187 lines; 2 laws; SHA256 ac619532f5fa22d6e61e6e5810a0626e88e99ef5e5422f611c8c5fc99680ef41.
  - MicroCFTA.SourceSynthesisPr210TypeReflection.decode_candidateRigid
  - MicroCFTA.SourceSynthesisPr210TypeReflection.candidateRigid_eq_iff
- SourceSynthesisPr211QueryBindings: 99 lines; 6 laws; SHA256 626b3fc5cbf4471d7fa6133291ee0948e8690e7ef7a189aa55fc2e173eb0f2c1.
  - MicroCFTA.SourceSynthesisPr211QueryBindings.queryBindings_names
  - MicroCFTA.SourceSynthesisPr211QueryBindings.queryBindings_length
  - MicroCFTA.SourceSynthesisPr211QueryBindings.queryBindings_lookup
  - MicroCFTA.SourceSynthesisPr211QueryBindings.queryBindings_member
  - MicroCFTA.SourceSynthesisPr211QueryBindings.queryBindings_coherent
  - MicroCFTA.SourceSynthesisPr211QueryBindings.queryBindings_idempotent

## Exact scope

The same current finished cache has stable concrete and tagged default
renderings. Their root terms agree under the existing openProgram true
projection. Every residual guard/term attachment agrees in the original
list order. Each actual compression endpoint is retained. Both RenderStable
and compression Frame receipts remain; concrete Canonical remains. There
is one concrete producer and one tagged-root producer. The public header
uses only the same current Packet, Canonical, ReferencesCarry, root carrier,
positive counter and actual finished selector. It adds no future rendering,
model, no-hole or Discharged supplier. Ground satisfaction and existence of
a model do not follow from marker syntax.

The repaired FirstOrder rigid type representation has a decoder roundtrip
to normalizeTy. Equality of candidateRigid first and candidateRigid second
is equivalent to the existing ordinary type equivalence, which identifies
the documented Fun/2 arrow alias. These two laws have no AliasSafe, TypeIn
or variable-name restriction. They concern type syntax. Raw/native acceptance
soundness, type-universe admission and program completeness are separate.

The queryBindings contract retains ordered names and length. It preserves
last lookup; each resulting row has that last type; same-name rows are
coherent; and normalization is idempotent. Every original required token
remains. All six statements follow the rule now merged in PR 211.

## Full compatibility and source validation

Full Audit passes: 5794 live modules, four affected, 4791 Audit imports and
93547 axiom reports. All 259770 previous Audit bytes remain after three
new imports. All four portable Lean/compatibility checks pass from /tmp.
The checks use project Nix, one Lean thread, memory.max=memory.high=4 GiB,
and zero swap. They reuse the repository Lake cache.

Merged Haskell validation passes Fourmolu for Synthesis.hs and SynthesisSpec.hs
and 16 existing focused SynthesisSpec examples with zero failures, one RTS
capability, offline Cabal and disabled optimization. No full suite, corpus
or benchmark was repeated locally. No Cabal file changed. This record keeps
the actual commands, source hashes, limits and measured case count:

```json
{
  "at": "2026-11-12T13:18:51.621686+01:00",
  "main": "e53852064d3ef5a2eafec47d754c27504b11de5f",
  "local_merge": "89a77f0637f25f98ea52525d59b7dc7453c54da3",
  "source_hashes": {
    "cfta-generator/src/Data/CFTA/Gen/Synthesis.hs": "abbd34f76d87164cdedfc63bd96fe771efe16686711ff723485982de752a2c0d",
    "cfta-generator/test/Data/CFTA/Gen/SynthesisSpec.hs": "30f780fb415e48f45083569cb7fd3be73897aaa4e877e3bc34879a48b417e2ec",
    "cfta-generator/cfta-generator.cabal": "ac32cce2048b798f8697c40f81d5a18723e7697d5498c0e1e386e5057b36fc9b",
    "cabal.project": "b45ebca653068a8f58383887846eee2306df274c825f0fabfe5288c73ae3116a",
    "shell.nix": "0473bdc0b22330870d20db83651b81b4af4d854d7592badb12264576cbee7d08"
  },
  "limits": {
    "memory.max": "4294967296",
    "memory.high": "4294967296",
    "memory.swap.max": "0"
  },
  "results": [
    {
      "command": [
        "fourmolu",
        "--mode",
        "check",
        "cfta-generator/src/Data/CFTA/Gen/Synthesis.hs",
        "cfta-generator/test/Data/CFTA/Gen/SynthesisSpec.hs"
      ],
      "exit": 0,
      "log": "/tmp/mcfta-default-partial-20261112-1303/merged-synthesis-0.log"
    },
    {
      "command": [
        "cabal",
        "test",
        "cfta-generator:test:gen-tests",
        "--offline",
        "--disable-optimization",
        "-j1",
        "--test-show-details=direct",
        "--test-options=--match=Data.CFTA.Gen.Synthesis +RTS -N1 -RTS"
      ],
      "exit": 0,
      "log": "/tmp/mcfta-default-partial-20261112-1303/merged-synthesis-1.log",
      "examples": 16,
      "failures": 0
    }
  ],
  "passed": true,
  "full_suite_run": false,
  "new_runtime_defect_established": false
}
```

The old reserved-name, Fun-arity and duplicate-query runtime packets remain
source-versioned. Their checkers intentionally reject repaired source hashes.
Reproduce those old results from formalize e39ffc4ba in an isolated checkout.
Do not rewrite their expected results or delete their counterexample proofs.
New current source contracts coexist with those historical definitions.

## Full objective and next obligation

Attach the full current OutputResources tuple to the SAME concrete/tagged
observation. Keep every inventory, full memo, caller/query, metadata, Post,
Fits and physical Heap field. Recover the universal conditional Completes
observer from the already observed tagged-root success. Do not call another
root producer or identify independent endpoint witnesses. The runtime-only
231-line SharedPreparedMarkerOutput draft is UNVERIFIED. Its frozen hash is
c57aeb56e003e1706890c29bce40596a236b1b524f537a8ae1578b701ffdb1e2.
It is not counted in this checkpoint.

Build the current source Context from repaired constructor discovery,
constructor escaping and canonical queryBindings. Existing row evaluators
and totality laws are reusable. Old whole admission judgments remain
hardwired and require an explicit context-indexed cut. Do not relabel old
firstOrderRaw as the repaired API. A future exact type-universe criterion
needs separated catalog names and a membership converse; its current audit
is a plan, not a proved iff. Rigid query leaves and goals do not blanket-
require TypeIn. Keep only the actual demanded-image/result admissions.

The native prepared backend remains shallow and singleton at child traversal.
The actual default Haskell worker expands children eagerly and can branch.
Neutral narrowing and callback controls alone cannot prove full default
correspondence. Preserve actual ordered branches, failures and native effects.
Continue full reduction/refold/first-birth weights, source stream order and
multiplicity/deduplication, all earlier hooks and alternatives, original-input
work/depth, both inverse contracts, Word/Int, full guards and source errors,
lazy demand, refinement and training. Retain P for Some native payload slots,
A for true expandable flags and logical W_B=(B+1)P+A. That is not runtime cost.
Native annotation size is not Program size. Default synthesis does not call
boundDepth; the earlier bounded-copy/rows/size/rank facts stay separate.

Liquid duplicate-name readers remain under external runtime review. No new
Liquid runtime failure is established. Curried marker names and reported
raw rigid-variable limits remain open. No new production repair was authored
here; this checkpoint integrates the reviewed upstream repairs.

## Frozen audits and initial draft records

The following notes retain their own earlier source snapshots. The current
checked hashes above supersede initial draft hashes. All failed source
drafts remain at their runtime paths. The plans below are explicitly unproved.

### default-partial-agreement-note.md

SHA256: 52eb6129d5d536843bc84147a1d052bacf7fd469ee6ad509316be97b434eb909

# Default concrete and tagged syntax agreement

Frozen: 2026-11-12 13:01 CET. New source-only draft. ROOT strict checking is pending.

Source: SourcePruningEnumerationDefaultPartialAgreement.lean.
SHA-256: 8bb46e331a35449c8ead1ccb7de08cac43202d14496e3c198bfc961a01a2e77c.
387 lines. One public law: default_finished_render_partial, at line 296.

The public inputs match the finished-render candidate. The marker is fixed to ("Mu", FullSyntax.Formula.top). The law calls checked default_finished_render ONCE. It retains that receipt's same term, ordered pending list, concrete endpoint, stable successful observations, RenderStable, full CompressionFrame and Canonical. It calls existing rootPartial_complete ONCE at the original current core. It derives the tagged residual traversal from that root's actual reached core. The conclusion appends the tagged root, ordered pending list, exact tagged endpoint, all-larger-fuel successful observations, RenderStable and full CompressionFrame.

The two syntax equations use existing SourcePruningPositions.openProgram true. The attachment equation preserves each guard, order and occurrence. No erasure function is introduced. A private coupled observer compares actual concrete and tagged fragment executions through getValue_agrees and full Frames. Current finished flags derive empty suspended buckets and actual recursive-boundary lookup internally. Concrete successful branches and paired reads exclude relevant raw-hole cases. The pending-root observer accounts for the extra tagged value read. It does not identify the two final compressed forests.

The local tagged action only composes the existing rootPartial, get and residual expandPartial mapM actions. No new renderer or semantic worker is defined. The statement supplies no Discharged, future no-hole/success, assignment, model or completion premise. Existing tagged completion semantics remain unchanged. The result asserts syntax agreement and stable chosen Success observations. It does not assert raw singleton results, guard truth on markers, a ground completion, typing, whole default traversal, source reduction/refold correspondence, stream order or deduplication.

Only this new runtime source and note were written. All previous sources and drafts remain unchanged. No compiler, Git, repository/root documents, evidence or Haskell edits were made. No Haskell fix or defect was established.


### pr210-type-reflection-note.md

SHA256: da88db58d9c02516e721bcb1d60c57ee060d875ee91c6996d592299fdab30652

# Candidate FirstOrder type reflection

Frozen draft: `SourceSynthesisPr210TypeReflection.lean`, 185 lines.
SHA256: `1579f86d023426cd1c2d2ba2545ad30d68bc8ba7026d889dc4b9c61b30ededf5`.
Root performs compiler checks. No compilation was run here.

Namespace: `MicroCFTA.SourceSynthesisPr210TypeReflection`.
Candidate source head: `79f74df2c3c9d3c864e57a960cb64c8c28883ec9`.
The source header records the saved OPEN, unmerged PR snapshot.

Public definitions:

- `encodeTy` changes constructor names only. Raw variables remain unchanged.
- `candidateRigid typ` is the OLD `rigidTerm (encodeTy typ)`.
- `decodeType` reconstructs raw types from those finite annotation trees.
  Its result on other finite trees supplies no validation claim.

Two public laws:

```lean
decode_candidateRigid (typ : Ty) :
  decodeType (candidateRigid typ) = SourceSynthesisOrdinaryTyping.normalizeTy typ

candidateRigid_eq_iff (first second : Ty) :
  candidateRigid first = candidateRigid second ↔
    SourceSynthesisOrdinaryTyping.Equivalent first second
```

No `AliasSafe`, `TypeIn`, catalog, or variable-name premise is added.
The private structural induction proves decoder roundtrip and commutation
of `encodeTy` with the existing normalizer together. The converse equality
uses the existing `OrdinaryTyping.rigidTerm_normalize`.
Name decoding and separation use the checked candidate module. Variable
decoding uses the existing `EncodedSubstitutionLift.decode_variableSymbol`.

Imports: `SourceSynthesisPr210ConstructorEscape`,
`SourceSynthesisEncodedSubstitutionLift`, `SourceSynthesisOrdinaryTyping`.
All historical definitions and counterexamples remain intact. The source
does not claim admission, generalization, source acceptance, Curried
correctness, or whole Haskell correspondence.


### pr211-query-bindings-note.md

SHA256: c361b8bd95670df9eb85caad6ea521114d5c11fc196b9e451a218d11bade0c95

# PR211 query contract draft

2026-11-12 13:08 CET. Runtime-only, UNVERIFIED source. No compilation or repository change.

Candidate: https://github.com/TharkunAB/cfta/pull/211 at `a3092c6c780b7138654b2de00578815fb9df7e6b`. ROOT reports this candidate is open and unmerged. Its external Haskell owner retains production ownership. The reviewed patch uses the same queryBindings list in rawSearchSpace, rawSaturatedSearchSpace, and typesOf. This draft does not investigate Liquid lookup policies.

`SourceSynthesisPr211QueryBindings.lean` imports only the existing ordinary typing module. It reuses `SourceSynthesisTypeSyntax.Query`, `Ty`, and `SourceSynthesisOrdinaryTyping.queryLookup:35`. The new `queryBindings` maps the original ordered list once. Each row retains its name and takes `(queryLookup original name).getD originalType`. This represents the candidate's Map.findWithDefault rule through the existing last-binding list specification. It adds no map implementation or data type.

Six public laws:

- `queryBindings_names`: exact equality of name lists. This retains order and duplicate occurrences.
- `queryBindings_length`: exact argument count.
- `queryBindings_lookup`: every last lookup is unchanged, including missing names.
- `queryBindings_member`: each returned type equals the successful original last lookup. An actual original occurrence rules out the fallback case.
- `queryBindings_coherent`: two returned rows with one name have equal types.
- `queryBindings_idempotent`: replacing queryArguments with the output and applying the rule again gives the same ordered list. The query goal is unchanged by that record update.

The one private lemma observes List.lookup after mapping only pair values. Its proof follows the existing checked lookup_argument_rows pattern at SourceSynthesisRelevantSingletonLookup:174. The remaining proofs use List.map_reverse, List.lookup_eq_none_iff, List.mem_map, and the existing queryLookup definition. There is no membership, runtime-success, future-state, or semantic-model supplier.

Boundary: these are pure candidate query-list laws. They do not update the old source compiler, prove Haskell Map correspondence, establish raw/native acceptance, transfer old duplicate-query counterexamples to the candidate, prove whole enumeration, or settle refinement lookups. ROOT must strictly check this draft before making a verified claim.


### next-native-default-hook-factor.md

SHA256: b035095ce5a0457e9cf7693d98816793758c1cb605e4f4a660fdc99344842037

# Native control factoring and the default expansion boundary

2026-11-12 12:57 CET. Read-only R239 design audit. No source, Git, compiler, Haskell, or ADR changes.

Two concrete function parameters can remove the hardwired narrowing and recording choices from ONE prepared worker. Keep the existing metadata and receipt types. Move the existing computational bodies into shared definitions and retain the old names as exact prepared-instance wrappers. Do not add a policy record, semantic carrier, second recursive worker, or success supplier.

This gives literal identity narrowing and literal false/unchanged-state callbacks on the current prepared backend. It does **not yet give the eager Haskell default pipeline**: the current child backend defers ordinary children and accepts singleton child observations. That separate boundary is detailed below.

## Existing seams and exact types

Use the existing local types `Symbol := SourcePruningTemplates.Symbol`, `Constraint := SourceSymbolicIndex.Constraint FullSyntax.Formula`, `Node := InternedConstructorTemplates.Value Symbol Constraint`, `Heap := InternedConstructorTemplates.State Symbol Constraint`, `Core := EnumerationState.State Symbol Constraint`, `Cached := EnumerationExpandableIndex.Cached Symbol Constraint`, `Metadata := SourcePruningRecordTypes.Metadata`, `Caller := SourceCurrentAllocatedPartialState.State`, and `Queries := SourceEndpointMemo.Memos`.

| Current definition | Hardwired operation and retained result |
| --- | --- |
| `SourcePruningEnumerationAction.prepare:17` | Calls `SourcePruningOuterNarrow.narrow:11`; returns `MergedSourceComparison.Result Symbol NativeGuard (Value Symbol NativeGuard × Option (EnumerateM Symbol EnumGuard Unit))`, including the actual returned/fault heap. The action rejects Empty, retains unsupported encoding as `none`, keeps the slot on identical handles, or writes the new handle through its actual representative. |
| `SourcePruningEnumerationSelectedStep.runPrefix:43` | Calls that preparation, advances the current caller from `prepared.state`, executes its action at the actual recursion-check core, attaches the native indexes, and calls `recordTypes` on Right. Returns the existing `SelectedStep.Result width Typing`, including full raw reads/actions/callbacks and exact reached caller/queries/cache. |
| `SourcePruningEnumerationSharedPreparedRecursive.continueWith:74` | Calls `recordTypes` on Left; true prunes, false frames the actual callback core and invokes `recur` with its updated metadata and exact restart decision. Other raw callback observations become the existing `.callback` stop. |
| `SourcePruningEnumerationSharedPreparedRecursive.resume:127` / `run:163` | The single bounded recursive loop and initial decision. The prepared ordinary/opaque/terminal expansion remains `SharedPreparedContinuations.run:60`; its ordered sibling driver remains `SharedSelectedContinuations.NativeContinuations.run:619`. |

## Minimal parameter signatures and wiring

The proposed narrowing parameter has exactly the existing source narrowing inputs and native result:

```lean
narrow : Metadata Typing → Nat → Nat → Node → Heap →
  MergedSourceComparison.Result Symbol Constraint Node
-- metadata, nativeFuel, uv, original decoded value, current heap

oracle : Nat → EnumerationState.Oracle Symbol Constraint (Metadata Typing)
-- callbackFuel, then metadata, uv, Left fragment / Right encoded handle
```

The callback uses the existing `EnumerationState.Oracle:297` alias. It therefore returns an actual `EnumerateM Symbol Constraint (Bool × Metadata Typing)` action. No callback result is supplied as a theorem hypothesis.

1. In `SourcePruningEnumerationAction`, extract `prepareWith narrow metadata nativeFuel representativeFuel uv oldHandle scs oldValue heap`. Its return type is the existing preparation result above. Move the current body unchanged except replacing the call to `OuterNarrow.narrow` by `narrow metadata nativeFuel uv oldValue heap`. Keep the generic `NativeGuard`/`EnumGuard` form of the current Action helper; the displayed signature is its source specialization. Retain all Empty/unsupported-encoding/unchanged-handle/replacement cases. Make old `prepare holeKey fits admits` the wrapper with `narrow := SourcePruningOuterNarrow.narrow holeKey fits admits`.
2. In `SourcePruningEnumerationSelectedStep`, extract `runPrefixWith narrow oracle stop order metadata readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries : SelectedStep.Result width Typing`. Move its body once. It calls `Action.prepareWith narrow` and `oracle callbackFuel metadata uv (.inr newHandle)`. Keep every existing raw observation and result constructor. Old `runPrefix holeKey fits admits graph templates` supplies the old narrowing function and `fun fuel => SourcePruningRecordTypes.recordTypes graph templates fuel`.
3. In `SourcePruningEnumerationSharedPreparedRecursive`, extract `continueWithOracle recur oracle stop order callbackFuel metadata uv fragment caller queries before` with the existing `Result := NativeContinuations.HookResult (Output width Typing) (Failure width Typing) width`. Its only changed line is the Left operation `oracle callbackFuel metadata uv (.inl fragment)`. Old `continueWith recur graph templates` supplies the old recording function.
4. Move the one recursive `resume` body to `resumeWith narrow oracle checkEmpty edgesOf stop order workFuel`. Its exact remaining type is `Nat → Metadata Typing → Caller width → Queries → Cached → Option Next → Result`. Use `runPrefixWith narrow oracle`, recurse with the SAME two functions, and use `continueWithOracle` for the later Left callback. Keep the captured sibling metadata/cache and the actual caller/query threading. The old `resume` is only a prepared-instance wrapper. A small `runWith` initial-decision wrapper can serve both instances; old `run` retains its full old argument list and result type.

Do not also generalize the separate legacy `SharedRecursive` worker in this cut. It continues to call the unchanged public selected-step interface. Do not add `Key`, `graph`, or `templates` as unused arguments to the generic helpers: those belong only in the old wrapper closures. Keep the existing typeclass requirements where the actual operations use them; avoid automatically carrying unused section instances into the new leaf helpers.

## Literal control instances and current-state laws

The prepared instance is exactly:

```lean
narrow := SourcePruningOuterNarrow.narrow holeKey fits admits
oracle := fun fuel => SourcePruningRecordTypes.recordTypes graph templates fuel
```

The default control operations are actual definitions, at every fuel:

```lean
identityNarrow := fun _metadata _fuel _uv value heap => .done value heap
noOracle := fun _fuel metadata _uv _input => pure (false, metadata)
stop := none
order := fun _metadata _candidates => none
```

Using `Metadata Unit` with empty lists gives the unchanged bookkeeping wrapper for source `()`. The native callback itself retains every supplied metadata field, even when instantiated at another current metadata value. There is no empty-catalog `updatedTypes` action to erase. Stop/order ignore that metadata in the default control instance; completed no-stop outputs retain the existing `metadata = none` behavior. Fuel-exhaustion receipts still retain their actual current metadata.

Prove only current operational laws:

- Identity narrowing returns `.done value heap` literally, with no read/rebuild or additional native fuel requirement. The common preparation still rejects Empty before Right, exactly as the Haskell branch at `Enumeration.hs:992` does. For a nonempty decoded value, derive `encodeNode value = some oldHandle` from the SAME current lookup and current coherence using `SourcePruningEnumerationIdentity.lookup_encode:11`. This establishes the common action is `some (pure ())`; do not assume an arbitrary value has the supplied handle.
- The unchanged-handle adapter `SourcePruningEnumerationNarrowAdapter.adapt:10` returns `some (frame checked before)`. Its native flags/waiting remain the actual captured indexes. The prepared caller advance must still be computed. For the identity heap, unfold `SourceCurrentAllocatedPartialState.advance:64`, `SourceCurrentAllocatedQueryMemo.advancePhysical:103`, and `SourceRecursiveIntersectionThunkEffects.advance:40` to prove the resulting complete caller is the input caller. These record updates retain operation caches, native tables/domains, caller tables, merge memo, and fourth memo. Query memos are passed through literally.
- Both default callback observations are the literal singleton `[.ok ((false, metadata), core)]`. The generic Left equation then becomes, for arbitrary later `recur`, `recur metadata caller queries before (some (EnumerationPureSelection.next (fun _ => none) before))`. This follows from the actual callback equation, frame identity, and `Restart.decision:13`, not a future callback-success premise. Do not replace an earlier sibling's actual bounded hook with this arbitrary `recur`.

## Exact compatibility plan

The old public names, argument order, result types, `Failure`, `Output`, `SelectedStep.Result`, preparation receipts, and ordered list driver remain unchanged. The old definitions become wrappers around the moved bodies. Hence old-instance equality is definitional at each wrapper, with literal whole-result equality rather than only successful support. Record explicit wrapper equations, expected to close by `rfl`, for `prepare`, `runPrefix`, `continueWith`, and `run`. The old recursive `resume` wrapper also denotes the SAME fixed `resumeWith` instance at all fuels; there must be no second recursive implementation.

Preserve the existing `prepare_pending_complete`, `prefix_no_ordinary`, `continue_recorded`, `continue_rejected`, `resume_zero`, and `resume_prepared` theorem statements. Existing proofs that explicitly unfold the old bodies may need focused unfolding of the new helper or a wrapper-equation rewrite. Definitional compatibility does not guarantee those tactic scripts elaborate without this small repair. Do not weaken hypotheses or conclusions, suppress lint, or replace actual receipts. ROOT must check the focused definitions and full Audit before publication.

Every generic branch remains the old branch: missing read/lookup; failed recursion check; parked/repeated restart; native preparation fault with its fault heap; no encoded action; empty action result; failed/multiple callback rows; unsupported cache attachment; prepared expansion failure; and exact stopped ordinary alternatives. Leave `SharedPreparedContinuations.run`, `finish`, `preparation_endpoint`, and `NativeContinuations.run` unchanged. The latter runs each actual hook before the next sibling at its returned caller/queries and combines `outputs ++ later`; the factor must not sort, deduplicate, parallelize, reset global state, or feed an earlier caller to a later sibling. No adequacy, progress, or order proof follows merely from choosing neutral operations.

Suggested implementation order is Action extraction and exact wrapper first; selected-prefix/Left extraction and leaf equations second; one recursive worker and compatibility third; literal identity/no-op current laws last. Keep each reviewable. This note authorizes no source edit by itself.

## Why this is not yet the literal eager default pipeline

Haskell `enumerateFully':927` passes `enumerateNode`, not `enumerateShallowHere`. `enumerateNode:725` recursively expands ordinary children through `enumerateEdge = enumerateEdgeWith enumerateNode:761`. The current shared native `ChildDispatch.observe:46` instead calls `SourcePruningEnumerationShallowChild.prepareChild:15` for nonterminal ordinary children and allocates a hole. `ChildDispatch.run:64` carries one optional attached cache. `ChildTraversal.Result:201` / `run:211` accepts exactly one successful child row. An eager ordinary child with multiple alternatives cannot simply be substituted at this signature; that raw observation is a stop under the current code.

Even with no oracle, eager and deferred traversals can order alternatives differently. A schematic unconstrained tree `r(A(C), B)` with two choices each at C and B illustrates it: eager traversal reaches C before B; shallow traversal allocates A/B first, then C, so the minimum-ID loop reaches B before C. The nested choice order can change. This is a source-control illustration, not a compiled counterexample or a Haskell defect.

Therefore name this result a neutral-control instance of the prepared worker. A full default-native result additionally needs either an actual branching eager native expansion path with its exact caller/query endpoints, or a proved ordered simulation of the shallow scheduler against eager execution. No such native shallow/eager theorem was found. The existing `EnumerationUntilBridge.no_stop_eager_successes:220` is explicitly eager and cannot remove this condition. Do not introduce an arbitrary future eager callback/completion supplier or silently label the two-parameter prepared instance as `runsBy` correspondence.


### next-current-synthesis-context.md

SHA256: 69c89e7a2f026f9111afc11a57694409f3c144f13c1eab87dc445ea7c6b33ab7

# Current FirstOrder context and leaf admission

2026-11-12 13:36 CET. Bounded read-only R240 audit. ROOT reports PR210 and PR211 merged and integrated at main `e538…`, PR211 merge `89a77f…`. The current local Haskell source was inspected. Historical Lean definitions and counterexamples remain unchanged. No compilation, Git, repository, Haskell, or old-note edit.

The smallest useful source cut is a new versioned factory that returns the EXISTING five-field `SourceSynthesisFirstOrderConstruction.Context`, plus positive leaf membership at that actual context. Do not duplicate termsRows, relevantRows, selections, the native builder, or the Program decoder. Whole positive Program/root admission is not yet obtained by renaming the old hardwired judgments.

## Exact factory

Use the checked `Pr210TypeReflection.encodeTy:47`, `candidateRigid:53`, `candidateRigid_eq_iff:171`, `Pr210ConstructorEscape.escapeConstructor`, and `Pr211QueryBindings.queryBindings:17`. Suggested namespace: `SourceSynthesisCurrentFirstOrder`. Define only these current-source bindings:

```lean
-- Names in this block describe the new versioned API.
def currentTypeNode (typ : Ty) : Expression := typeNode top (encodeTy typ)

def currentConstructorsOf : Ty → List (String × Nat)
  | .tVar _ => []
  | .tFun argument result =>
      currentConstructorsOf argument ++ currentConstructorsOf result
  | .tCons "Fun" [argument, result] =>
      currentConstructorsOf argument ++ currentConstructorsOf result
  | .tCons name children =>
      (escapeConstructor name, children.length) :: children.flatMap currentConstructorsOf

def currentCatalog (lib : Library) (query : Query) : List (String × Nat) :=
  (lib.libraryGroups.flatMap (fun entry => currentConstructorsOf entry.2.1) ++
    lib.libraryArgumentOnly.flatMap (fun entry => currentConstructorsOf entry.2) ++
    (queryBindings query).flatMap (fun entry => currentConstructorsOf entry.2) ++
    currentConstructorsOf query.queryGoal).eraseDups

def currentContext (lib : Library) (query : Query) : Context :=
  let types := allTypes top (currentCatalog lib query)
  { types := types
    components := lib.libraryGroups.map fun entry =>
      (entry.1, component types entry.1 (encodeTy entry.2.1))
    argumentEdges := (queryBindings query).map fun entry =>
      (entry.1, .mk entry.1 top [currentTypeNode entry.2])
    argumentOnly := .node (lib.libraryArgumentOnly.map fun entry =>
      component types entry.1 (encodeTy entry.2))
    avoid := lib.libraryAvoid }
```

These are source syntax definitions, not a native Map implementation. Haskell references are `cfta-generator/src/Data/CFTA/Gen/Synthesis.hs`: queryBindings:337, typeNode:416, constructorsOf:515, rawSearchSpace local fields:779-792, and typesOf:842-851. Fun/2 alone is an arrow alias. Fun/0, Fun/1 and Fun/3 remain catalog entries. Mapping the old constructorsOf is impossible because it has already discarded those Fun entries. Apply escaping once to original constructor names. Applying discovery to an already encoded type and escaping again would change raw `con:` names twice.

The catalog MUST read queryBindings, as the current source does. It cannot keep all original shadowed types. Keep first-occurrence discovery order and eraseDups. The existing allTypes/TypeIn accept any catalog, so no new universe representation is required. Rigid query and goal trees need no TypeIn premise. Component images and application results retain their existing role-specific admission requirements; the universe still has four fixed variable leaves.

## Smallest context-indexed adapter and public positive leaf cut

The current LeafTyping judgment is ALREADY catalog-parametric (`SourceSynthesisSourceTermsTyping:67`) and its shape law is generic (:143). The component-instance law is ALREADY catalog-parametric (`EncodedSubstitutionLift.component_instance_leaf:181`). Its later group_instance_terms:191 and all old TermsTyping/RelevantTyping conclusions are hardwired, so use the generic leaf law rather than their original-source wrappers.

One private adapter suffices to place an accepted singleton row in the ACTUAL size-one context pool. Its exact header is:

```lean
private theorem one_row_member_at [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ctx : Context) (asArgument : Bool) (row : Row) (term : Term Symbol)
    (selected : row ∈ ctx.argumentEdges.map Prod.snd ∨
      row ∈ ctx.components.map Prod.snd ∨
      (asArgument = true ∧ ∃ rows, ctx.argumentOnly = .node rows ∧ row ∈ rows))
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (.node [row])) term) :
    ∃ expression ∈ termsRows ctx asArgument 1,
      evaluate (SourceEqualityPCSGuard.holds formulas solver) []
        (mapSyntax literal expression) term
```

This observes current immutable syntax and an existing leaf receipt. It is an INTERNAL helper, not a future-membership supplier in the raw-input API. Its proof is just the three size-one branches at SourceTermsTyping.member:240-265, using termsRows_one:159 and singleton-row inclusion. The old singleton-row inclusion helper is private (:184), so a small local proof is needed unless ROOT intentionally exposes it. No ctx.types equation is needed by this adapter.

The precise public group-leaf target is below. Abbreviations are the existing Symbol/literal/Program/evaluate/mapSyntax/opened source names used by OrdinaryLeafCompleteness. All assumptions concern the original binding and its demanded raw substitution images.

```lean
theorem current_group_member [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (asArgument : Bool)
    (entry : String × Ty × List String) (binding : entry ∈ lib.libraryGroups)
    (rho : String → Ty)
    (admitted : ∀ raw, variableSymbol raw ∈ variables (encodeTy entry.2.1) →
      TypeIn (currentCatalog lib query) (candidateRigid (rho raw))) :
    let typ := substTy rho entry.2.1
    let term : Term Symbol := .node (literal entry.1) [candidateRigid typ]
    Typed lib query (.var entry.1) typ ∧
      ∃ expression ∈ termsRows (currentContext lib query) asArgument 1,
        evaluate (SourceEqualityPCSGuard.holds formulas solver) []
          (mapSyntax literal expression) term ∧
        term.atPath [0] = some (candidateRigid typ) ∧
        Projection literal Prod.fst term (.var entry.1) ∧
        toProgram literal Prod.fst term = .var entry.1
```

Two small genuinely missing structural facts discharge its encoded-scheme seam: `AliasSafe (encodeTy scheme)` for EVERY original scheme, and `substTy (fun name => encodeTy (rho name)) (encodeTy scheme) = encodeTy (substTy rho scheme)`. They were not found in the checked Pr210 modules. Prove them by Ty/list induction. The first uses checked constructor separation; do not add AliasSafe as an original-input restriction. Apply the existing catalog-parametric component_instance_leaf ONCE to encodeTy scheme and encodeTy composed with rho, use its explicit demanded images above, and transport through the substitution equality. Typed.group remains on the ORIGINAL lib/query/scheme/rho. Existing AnnotatedProgramWitnesses.component_member:155 gives singleton-row acceptance; the adapter places it in the actual current pool.

The query-leaf companion replaces entry/binding/rho/admitted by `(name : String) (typ : Ty) (found : queryLookup query.queryArguments name = some typ)` and returns the same packet with `.var name`, candidateRigid typ, and the original Typed.queryArgument. Derive an actual `(name,typ) ∈ queryBindings query` using queryBindings_lookup:48 followed by old queryLookup_member:112. Map that row into currentContext.argumentEdges and reuse AnnotatedProgramWitnesses.argument_member:171 at encodeTy typ. No uniqueness or universe premise is required. The argument-only companion uses an original `(name,scheme) ∈ lib.libraryArgumentOnly`, the same per-image admission, and `asArgument = true`; its current factory field supplies the third adapter branch.

## Exact reuse and limits beyond that leaf cut

`Context:56` has all required fields. `without:75`, application:47, ofType:52, termsRows:84, resolveArguments:108, and relevantRows:112 are ALREADY context-parametric. Selection closure and FirstOrderTotality.relevantRows_total_of_resolution:19 therefore apply immediately to currentContext, including all split/offset mapM branches. They give construction success, not inhabitance. A current firstOrderRaw wrapper only repeats the small outer signed-size/permutation/filter binding at FirstOrderConstruction:140, with currentContext and currentTypeNode queryGoal; its negative key uses currentContext.argumentEdges names, proved equal to original names by queryBindings_names. Do not invoke historical firstOrderRaw_total as if it returned the new expression.

The actual remaining generic-proof seam is `TermsTyping:79` / `RelevantTyping:116`, their membership laws (:234 / SourceRelevantTyping:61), and LeafEligible/ProgramEligible/UsesEligible. They hardwire context lib query, constructorCatalog lib query, and old rigidTerm. The established source-independent constructors remain reusable: AnnotatedProgramWitnesses.application_member:101 and ofType_member:130; TypeIn.member:35 and typeNode_member:97; ProgramTermSize.Projection/toProgram_eq:49/63. A future whole ordinary theorem must reindex the admission induction over currentContext/currentCatalog/candidateRigid, or extract the old induction with historical wrappers. The current-group leaf theorem above is the bounded next cut; do not duplicate the whole stack now or claim old uses_root_member:239 has already transferred.

Root coverage has one important fixed-input requirement. For `tokens.Perm query.queryArguments`, map tokens by the SAME fixed original query:

```lean
tokenRowCurrent query token :=
  (token.1, .mk token.1 top
    [currentTypeNode ((queryLookup query.queryArguments token.1).getD token.2)])
```

Then `covered.map (tokenRowCurrent query)` supplies a permutation of currentContext.argumentEdges. Do NOT call queryBindings separately on each permuted token list; permutations can change the last duplicate binding. Keep every original token multiplicity and retain names-only winner resolution. The existing singleton-resolver proof at RelevantSingletonLookup:174-201 is structurally reusable with encodeTy and the fixed query lookup; the old theorem itself names the old context.

No new blanket Program-name freshness, library/query name disjointness, or shadowing premise is justified here. OrdinaryTyping.Typed:39 explicitly records a group origin, argument-only origin, or last-query origin. Group origins do not require exclusion from the query table. The current Context retains those separate row pools and original representative labels. Same-name query coherence proved by PR211 is a property of query rows, not a new global lexical-priority theorem. Program names app/filter also need no freshness for these positive results: component terms have ONE annotation child, while decoder applications/filters require FOUR/TWO children (ProgramTermSize:36-72; Haskell Synthesis.hs:963-966). Preserve the selected role and exact arity. A future GHC/name-resolution correspondence may need its own domain, but this audit establishes no new defect.

This cut is FirstOrder syntax and admitted positive membership. The factory represents that branch; a future Haskell branch correspondence must explicitly use lib.libraryEncoding = .firstOrder. The pure group-leaf theorem itself need not inspect encoding because the factory is already a FirstOrder definition. This cut does not implement Curried construction, establish the image of every accepted annotation, prove full ordinary soundness, connect Haskell Maps/native heaps, or establish default enumeration completion/order. Keep historical Context/firstOrderRaw and all old collision/Fun/duplicate counterexamples under their existing names and source versions.


### next-current-type-universe-contract.md

SHA256: e7ed1669feb4a7223e5900cc394b4c38d5d9be91b4d47e77e93f208f87f45388

# Current FirstOrder type-universe contract

Inspected 2026-11-12 13:36 CET after PR210 and PR211 integration. This is a
read-only source audit. The prospective headers below are not checked laws.
Historical Lean encoders and their counterexamples retain their old meaning.

## Exact current source data

`cfta-generator/src/Data/CFTA/Gen/Synthesis.hs:337-340` defines `queryBindings`.
It preserves every name, position, and repeated occurrence. Each payload is
the last raw type for that name. Checked counterparts are
`SourceSynthesisPr211QueryBindings.lean:36,43,48,62,79,87`.

Write `C t` for the CURRENT `constructorsOf t`, not the historical Lean
function with that name. Its source equations at `Synthesis.hs:515-519` are:

```
C (TVar _)                  = []
C (TFun a b)                = C a ++ C b
C (TCons "Fun" [a,b])       = C a ++ C b
C (TCons name arguments)    = (escapeConstructor name, length arguments)
                              :: concatMap C arguments
```

Write `K lib query` for this exact current catalog:

```
eraseDups (flatMap (C . groupType) lib.libraryGroups
        ++ flatMap (C . snd) lib.libraryArgumentOnly
        ++ flatMap (C . snd) (queryBindings query)
        ++ C query.queryGoal)
```

This follows `Synthesis.hs:846-851`. The FirstOrder branch at 842-844 is
`allTypes K`. Curried uses a different universe. Shadowed original query
payloads do not contribute signatures unless another current source type
contains those signatures. Repeated canonical bindings remain in the list.

`Synthesis.hs:475-481` leaves the universe grammar unchanged. Its alternatives
are arrows, exactly the four leaves `var1` through `var4`, and each catalog
signature with recursive children at its exact arity. The arrow marker is
a fixed child. It does not need a catalog entry or its own TypeIn witness.
The finite catalog generates arbitrarily deep finite type trees.

Current `typeNode` escapes constructor names at `Synthesis.hs:416-420`.
Only Fun/2 denotes an arrow. Fun/0, Fun/1, and Fun/3 remain constructors.
Constructor names `->`, `(->)`, `var1`, and `var_...` get escaped symbols.

## Smallest exact structural contract

Use the checked `candidateRigid` from
`SourceSynthesisPr210TypeReflection.lean:53`. Its unconditional reflection
law is at 171: tree equality is exactly ordinary `Equivalent` raw types.
Its decoder round trip is at 166. Neither law assumes universe admission.

After adding the small current catalog factory, propose this public law.
Here `C` and `K` are the source functions specified above:

```lean
theorem current_typeIn_iff (lib : Library) (query : Query) (typ : Ty) :
  TypeIn (K lib query) (candidateRigid typ) ↔
    (∀ raw ∈ typeVariables typ, raw ∈ ["a", "b", "c", "d"]) ∧
    (∀ signature ∈ C typ, signature ∈ K lib query)
```

`C typ` is equivalently the escaped constructor signatures of `normalizeTy
typ`. Fun/2 contributes only its children's signatures. This criterion does
not count the internal arrow or marker as raw constructors. It permits every
raw constructor name and every arity. It restricts catalog membership at
each demanded occurrence. The criterion does not require signature uniqueness
or remove repeated query tokens.

Prove it by nested raw Ty induction and inversion of the three `TypeIn`
constructors at `SourceSynthesisFiniteTypeWitnesses.lean:23-32`. Each entry
of K has an escaped constructor name, directly from C. Use
`SourceSynthesisPr210ConstructorEscape.lean:79,99` to exclude a catalog row
that matches a variable or arrow tag. Use variable-symbol injectivity from
`SourceSynthesisEncodedSubstitutionLift.lean:69` for the four variable cases.
Catalog membership and child-list length give each constructor case.

The catalog-range fact must be derived from C. The iff is false for an
arbitrary unconstrained catalog: a catalog entry `("var_e",0)` could admit
the encoded variable e as a constructor. No such entry occurs in K.

## Existing semantic admission and its one missing converse

`SourceSynthesisFiniteTypeWitnesses.TypeIn.member:35` already proves
TypeIn implies actual `allTypes` syntax membership. It uses the checked
variable, constructor, and arrow laws at
`SourceSynthesisTypeUniverseMembership.lean:69,80,98`.
Those files provide no converse. A small reusable converse can establish:

```lean
theorem allTypes_member_iff_TypeIn
    (holds : Guard → Term Symbol → Bool)
    (topHeld : ∀ term, holds top term = true)
    (catalog : List (String × Nat)) (term : Term Symbol) :
    evaluate holds [] (mapSyntax literal (allTypes top catalog)) term ↔
      TypeIn catalog term
```

For membership to TypeIn, use `BinderLanguage.least_le:29` with candidate
language `TypeIn catalog`. Invert the three body alternatives and the finite
forest of recursive children. This requires no catalog separation. Combine
that direction with the existing `TypeIn.member`. No termination, lookup,
native-result, or future membership supplier is needed.

The `topHeld` condition is necessary for the generic iff. For the actual PCS
guard evaluator it follows from `SourceEqualityPCSConstructors.top_true:15`.
All universe edge guards are top. Universe admission adds no application
equalities or pruning conditions. Smart-binder semantics already follows
`InternedGuardedSyntax.binder_unfold:107`.

Combining the two proposed laws gives membership iff the displayed raw-type
criterion. Identifying this with the actual `typesOf` branch requires
FirstOrder encoding and the new current K factory. The historical
`SourceSynthesisFirstOrderConstruction.lean:32-40` still uses unescaped
constructor discovery, skips every Fun arity, and reads original query
payloads. It must not be relabelled as the merged source. Generic universe
construction already accepts any catalog through
`SourceSynthesisUniverseNativeInput.allTypes_closed_verified_complete:84`.
Runtime correspondence and machine Int arities remain separate obligations.

## What completeness admission actually needs

An arbitrary rigid variable such as e or x remains distinct under the
unconditional reflection theorem. Its encoded leaf is `var_e` or `var_x`.
The actual universe has neither leaf, and its escaped catalog cannot add
one under that symbol. Reflection therefore does not imply admission.

Do not infer that every query type must satisfy the criterion. Query rows
use rigid `typeNode` directly (`Synthesis.hs:788`). The final goal uses it
directly too (779). `SourceSynthesisFiniteTypeWitnesses.typeNode_member:97`
requires no TypeIn. A rigid query leaf can carry e successfully without
placing e in the universe. In contrast, every application result occupies
the `types` child at source position 0; see
`SourceSynthesisFirstOrderConstruction.application:47` and
`SourceSynthesisAnnotatedProgramWitnesses.lean:108-125`.
An application that must return rigid e therefore has a different admission
obligation from a size-one query leaf of type e. This is a source consequence,
not a new executed Haskell counterexample.

For a constructive ordinary derivation, require the criterion only for each
demanded per-use substitution image and each application result type.
Do not require it for every raw substitution value, every library scheme,
every query type, or every annotation. Polymorphic scheme variable names may
be arbitrary: generalization recognizes `var_...` as well as the first four
symbols (`Synthesis.hs:467-470,524-530`). Their selected images must meet the
universe criterion when that occurrence demands them.

The historical admitted leaf and Program certificates already use exactly
these sites (`SourceSynthesisOrdinaryLeafCompleteness.lean:35-47` and
`SourceSynthesisOrdinaryProgramCompleteness.lean:32-44`). They remain pinned
to the old catalog and encoders. A current bridge needs the new factory and
encoded substitution compatibility; raw AliasSafe must not silently become
a new public input restriction after escaping. Roles, avoid rules, marked
query-use coverage, duplicate multiplicity, and root admission remain
independent of this type-universe criterion. Curried is outside this audit.


### next-default-marker-model-wrapper.md

SHA256: a4ca73245bfd0c721f24a6b00b3fc5439bd6c0036e140dc6766549b198c69b2b

# Model and resource attachment for the same default observations

Frozen: 2026-11-12 13:24 CET. READ-ONLY audit. The proposed helper and wrapper below are UNPROVED PLAN. No new source or compilation.

The checked R240 agreement source is 389 lines, SHA fd281edef9382688b1a5b8cb08146b0c5b8b7a2e625378e0bdeca43984978ca0. ROOT reported strict PASS. It has one concrete finished producer and one tagged root producer. Their call sites are SourcePruningEnumerationDefaultPartialAgreement.lean:328-332. Its public receipt at296-320 retains both endpoints and the existing openProgram true root/ordered-attachment equations.

## Recommended route

Unpack CURRENT OutputResources and call default_finished_render_partial ONCE. Do not call OutputResources.root_partial_complete. The agreement producer already constructs its one actual tagged root. Derive the old full root receipt from THAT observed root execution. This requires a small observation theorem, not another completion producer or a public comparison callback.

OutputResources is an abbreviation in SourcePruningEnumerationSharedPreparedHookCertificates.lean:52. The underlying exact fields are SourcePruningEnumerationSharedHookCertificates.lean:110-119:

- next Inventory, final FULL EndpointMemoGateTrace.Memos, and metadata;
- Post formulas solver next original output.caller final;
- final.query = output.queries;
- Packet formulas solver next output.caller final metadata output.cache;
- output.metadata = none OR some metadata;
- Fits seed.2 output.caller.checked;
- physical annotation Heap (fun guard => guard ∈ seed.1) at the SAME caller heap.

Keep all these witnesses and conjuncts unchanged. Rendering changes enumeration compression only. It does not create another native caller, memo state, inventory, guard pool or Post. Canonical, ReferencesCarry, root CarriesGraph, inside and actual finished selection remain explicit CURRENT inputs. OutputResources alone does not derive them.

## Smallest useful observation helper

A proposed new-file public header is:

```lean
theorem rootPartial_observed
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel : Nat) (before after : EnumerationState.State Symbol EnumGuard)
    (taggedRoot : SourcePruningTemplates.PartialTerm)
    (safe : EnumerationSchedule.Safe before) (inside : 0 < before.counter)
    (actual : Success (SourcePruningEnumerationPartialOutput.rootPartial heap fuel)
      before taggedRoot after) :
    (∀ extra,
      Success (SourcePruningEnumerationPartialOutput.rootPartial heap (fuel + extra))
        before taggedRoot after ∧
      ExceptT.run (SourcePruningEnumerationPartialOutput.rootPartial
        heap (fuel + extra) before) = [.ok (taggedRoot, after)]) ∧
    EnumerationDriver.RenderStable before after ∧
    EnumerationCompressionFrame.Frame before after ∧
    ∀ language meaning assignment,
      Satisfies language meaning assignment before →
      Satisfies language meaning assignment after ∧
      SourcePruningPartialMatch.Completes assignment taggedRoot (assignment 0)
```

This observes an ALREADY RETURNED Success. The final resource producer derives that Success internally by decomposing the agreement receipt. It must not expose a future render/model/totality supplier. No additional model is constructed.

The exact closed proof ingredients are:

1. Decompose rootPartial using success_bind. EnumerationRootObservation.rootFragment_success:20 identifies the actual value read and root fragment. EnumerationDriver.getValue_storage:682 derives RenderStable and SlotBound for this read from CURRENT Safe/inside. The observed fragment is allocated: an enumerated fragment follows from SlotBound; every other rootFragment case is hole zero and follows from inside and the read's unchanged counter.
2. Unfold only SourcePruningEnumerationPartialOutput.expandPartial in the observed continuation. Its actual private boundary graph is inferred from that observation; no new graph or graph interpretation is supplied. EnumerationPartialBounds.expandPartial_bounded:62 derives the continuation RenderStable. Compose the two stable receipts. EnumerationPartialRoot.rootPartial_frame:22 supplies the full frame. R240's checked private partial_frame:40 already uses this anonymous-graph inference pattern successfully.
3. Raw singleton exactness follows from EnumerationPartialExact.getValue_exact:41, rootFragment_success, bind_single and EnumerationPartialExact.expandPartial_exact:51. Existing native private root_read_exact/root_exact at SourcePruningEnumerationPartialOutput.lean:111-127 contain this same short proof, but are not a public API. Do not invoke a second complete producer to obtain exactness.
4. EnumerationPartialRoot.rootPartial_moreFuel:50 raises the SAME observed root/after. Apply the exactness observer to each raised Success. This preserves one root endpoint for every larger fuel.
5. YES: conditional completion follows directly from SourcePruningPartialRenderingSemantics.expandPartial_completes:39 on that actual continuation. Transport the supplied CURRENT assignment through rootFragment_frame and satisfies_frame. For an enumerated root use its stored equation and original union-find class equation; for the other cases rootFragment is hole zero. This is exactly the proof already private at SourcePruningEnumerationPartialOutput.root_completes:129-156. Generic satisfies_frame is SourcePruningEnumerationNativeLanguage.lean:113. The new helper can expose this observed-run fact without naming the private boundary graph or invoking rootPartial_complete.

## Same global resource wrapper

The next producer should be OutputResources.default_finished_render_partial_models, with resources plus the same current canonical/references/root/inside/finished header. Its exact sequence is:

1. Unpack resources ONCE. Retain next/final/metadata/post/querySame/packet/metadataSame/fits/known.
2. Call checked default_finished_render_partial packet canonical references root inside finished ONCE. Retain its ENTIRE concrete/tagged receipt, including both successful all-larger-fuel executions, both RenderStable/Frame receipts, concrete Canonical, and both ordered projection equations.
3. Decompose the tagged execution at extra zero. This supplies the SAME tagged root, its actual intermediate rootAfter, the unchanged get, and actual ordered residual traversal to partialAfter. Use rootPartial_observed on this root Success. This retains every root-specific field from the old OutputResources.root_partial_complete:33-61: all-fuel raw singleton/Success, root RenderStable/Frame, root stratification, framed Packet, and its universal conditional completion observer. It does not call that old producer.
4. Use packet.ordered and EnumerationOrder.stratified_read:147 for rootAfter, concreteAfter and partialAfter. Use SourcePruningEnumerationRecursive.callback_frame:51 at those SAME states. Preserve metadata pending bounds by each frame.counter, exactly as the old wrapper does at SharedPreparedPartialOutput.lean:71-74.
5. Return the untouched original global fields, the entire agreement receipt, and the recovered full root receipt at rootAfter. The universal model observer can retain Satisfies at rootAfter, concreteAfter and partialAfter by their original-to-endpoint Frames. Retain Completes assignment taggedRoot (assignment 0) from the root observer.

rootAfter is distinct from partialAfter, which also includes residual compression. Neither is required to equal concreteAfter. The root's all-fuel raw singleton can identify its intermediate state inside later tagged runs if that strengthened trace statement is needed. The current cut does not need to reconstruct a second root to prove it.

## Alternatives and boundaries

Calling new default_finished_render_partial AND old OutputResources.root_partial_complete would create two independently chosen tagged roots. Reject that composition even though existing rootPartial_agrees could compare their syntax. If exact retention of an already supplied old resource-root receipt is required instead, the private root_agrees/pending_agrees/packet_boundary helpers at R240:135/180/269 need an observation-level public attachment. That route is larger and unnecessary when starting with current OutputResources.

The recommended route preserves the old receipt SHAPE and all its global/model facts for the one root chosen by the new agreement producer. It does not claim equality to an independently chosen existential root or endpoint from another invocation of the old wrapper.

Completes.truncated allows any assigned ground term (SourcePruningPartialMatchSemantics.lean:21-23). Thus root syntax agreement plus conditional Completes does not give markerTerm = assignment 0, a model's existence, ground language membership, typing, or guard truth on projected marker residuals. It proves no whole-driver completion, prior-hook completion, source reduction/refold correspondence, stream order or deduplication. Full memos and physical annotation Heap remain separate from these syntax/model observations. No Haskell fix or defect is established. No claim is made about current main merge status.
