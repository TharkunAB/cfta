# Current strict results and retained source boundaries

All four exact source modules pass strict own-source checks. Public names,
namespaces, exact hashes and standard axiom sets are verified. The four core
helper definitions are proof-visible; their bodies and public branch theorem
contracts remain unchanged. No production Haskell or Liquid Haskell changes.

The native completion theorem derives a single stable reader cutoff from only
current readiness, root availability and closedness, with an empty initial memo.
It retains the same full result/heap/memo and cache/readiness postconditions.
It does not yet prove exact bounded language or full runtime correspondence.
The arrow collision is proved in the source encoder, with no new Haskell run.
The duplicate-query candidate remains UNVERIFIED and is not a new defect claim.

- SourceSynthesisInternalArrowEncodingCollision: 58 lines, 1 laws, SHA 68b95541acb9813f00190f486eba4997cc2dfb17e3daf7f5e0d06f76e30ce7b1
- SourceNativeBoundDepthChildArity: 42 lines, 1 laws, SHA e07800754e4445ea7ef6ee90e25f7d1ac8cc6eb3944fd6bbe63f106abbba37cd
- SourceNativeBoundDepth: 179 lines, 9 laws, SHA 54f13279b8d3621fbc05bc143d19cd291789179f62dcad025dfc3dc70ddbce4d
- SourceNativeBoundDepthCompletion: 256 lines, 1 laws, SHA ee8ea989d5accc8667bdbe710e5971f33fd8b5443a5d85719728885e77b81706


## native-bound-depth-note.md

# Native bounded-depth operational model

Frozen: 2026-11-12 10:15 CET. Source-only draft. No compiler, Git, repository source, or Haskell changes.

Source: `SourceNativeBoundDepth.lean`.
SHA-256: `f6b6e4a5515b7bdfc16cd4190f37bc02781620bf32a57f58860d8c29611b6fc0`.
179 lines; nine public branch laws. Strict checking is pending with ROOT.

Public operational definitions: `SourceNativeBoundDepth.Memo`, `Result`, `retained`, `atHeight`, `run`, and `boundDepth`. `run` takes the actual current local memo. `boundDepth` starts the local memo empty. No public execution accepts a future reader, copier, heap, row, or completion supplier. Private ordered traversal callbacks are bound internally to the recursive worker.

Public laws: `run_empty`, `run_reference`, `run_negative`, `run_nat`, `atHeight_node_hit`, `atHeight_mu_pending`, `atHeight_union_exhausted`, `atHeight_union_unresolved`, and `retained_zero`.

The model reuses `MergedSourceComparison.Result/Fault`, `InternedConstructorTemplates.State/Value`, and `Cache.Table/put`. Each result is paired with the local memo. Failure retains both the actual native endpoint and all prior memo entries. The worker calls the actual repaired `MergedFreshOrdinaryExposure.nodeEdges`, processes retained rows and children in source order, rebuilds full constraints with `makeEdge`, calls `makeNode`, then inserts the parent memo entry. A child failure stops later siblings and parent insertion.

Empty input and raw Rec are handled before the negative exit. Raw Rec and unresolved reader references both use the existing `.unresolved name` Fault. This preserves failure and branch order but abstracts the different source exception strings. Pending and exhausted reader faults remain distinct. No new exception type is introduced.

The source depth is mathematical Lean `Int`. The source `Depth` wraps machine `Int`; a machine-word correspondence theorem is not proved. The worker uses Nat height `(depth + 1).toNat` only as a termination index. Positive-height memo keys are the actual corresponding signed depth. This is separate from `readerFuel`, which bounds each native exposure. The model neither derives a sufficient reader cutoff nor claims source failure from an exhausted proof cutoff.

The ordinary constructors use the same child count and retain the full old symbol and constraint. The formal child-list length proof and the explicit same-arity `setChildren` correspondence are not yet included. The native cache types differ from `EnumerationBuilderRuntime`; no unproved cache erasure or abstract-row decode is introduced. This is a native execution model, not another copied grammar.

Open: completion from current Ready/closedness, semantic/cache preservation, independent meaning, all-row output height, memo/cache realization, and whole Haskell correspondence. Reuse ROOT's `MergedOrdinaryHeight.height/child_lt/makeNode_bound`; do not add another height function. Reuse `SourceSecondaryGateHeadLanguage.nodeEdges_included/nodeEdges_sound` for independent meaning of the SAME actual read. WarmHead follows from current closedness. No full enumeration/pruning completion, OperationRows, AllocatedRows, or machine resource bound is claimed.


## proof-reuse-note.md

# Existing proof reuse and operational helper access

The four bounded-copy helper definitions are public in their existing namespace.
Their bodies are unchanged. Separate proof modules need their equations for
ordered traversal induction. Public execution and branch theorem contracts do
not change. The frozen original operational source remains in this runtime.

MergedOrdinaryHeight.height:16 already counts ordinary constructor layers.
Its child_lt:49 covers every actual ordinary child before guard evaluation.
Its makeNode_bound:66 covers actual canonical node construction from current
coherence, linked records and resident source edges. Reuse these laws after
excluding recursive/union boundaries. Do not add another height function.

SourceEqualityProjectionRead.Read.exact:71 already provides both directions of
independent native meaning for the SAME actual returned exposure rows.
Read.verified:61 retains the exact endpoint and provenance. Read.complete:43
derives the observed read from current semantic readiness, availability and
closedness. No new leastness or extra semantic producer is required.

Whole native copy completion, common reader cutoff and memo invariants remain
separate from these operational branch laws. Exact Haskell exception strings
remain abstracted by the existing unresolved fault.


## native-bound-depth-child-arity-note.md

# Native child arity

Frozen: 2026-11-12 10:28 CET. Source-only repair for R236.

Working source: `SourceNativeBoundDepthChildArity.lean`, 42 lines.
SHA256: `e07800754e4445ea7ef6ee90e25f7d1ac8cc6eb3944fd6bbe63f106abbba37cd`.

The single public law is `MicroCFTA.SourceNativeBoundDepth.children_length`. It takes an arbitrary copy callback and the SAME complete successful traversal equation. It proves that the returned list length equals the input list length. The equation retains the full final native heap and memo. The proof follows the exact intermediate callback and tail results.

The first strict check failed only in two impossible failure branches. Simplification retained a pair equality whose first components were `failed` and `done`. Each branch now applies `congrArg Prod.fst` to that equality and uses constructor disjointness. The public statement and successful proof branch are unchanged. The initial 40-line draft is preserved separately.

The repair has not been compiled by the source owner. Root owns strict verification and publication. This law adds no callback-success, coherence, language, or source-correspondence premise. It does not claim that rebuilt native edge fields are correct without their existing current heap invariants. No repository, Haskell, Git, or evidence files were changed.


## internal-arrow-encoding-collision-note.md

# Internal arrow encoding collision

Frozen runtime draft, 2026-11-12 09:56 CET. Pending ROOT's strict kernel check.

Source: `/tmp/mcfta-native-admission-20261112-0927/SourceSynthesisInternalArrowEncodingCollision.lean`.
SHA256: `9a2cb98ba9d5bd5bdf1edd329c1f23faaf68b12442f428d087a999fb2749036e`.
Size: 53 lines, 2380 bytes. One public combined law.

The sole import is the existing `MicroCFTA.SourceSynthesisOrdinaryTyping`.
Its dependencies supply the actual raw `Ty`, `AliasSafe`, `rigidTerm`,
`Equivalent`, and `normalizeTy`. The draft defines no new type syntax,
normalization relation, safety predicate, library, query, or public input
contract.

Public law:
`MicroCFTA.SourceSynthesisInternalArrowEncodingCollision.internal_arrow_constructor_collision`.

It has no parameters or hypotheses. Its literal raw types are:

```text
TFun (TCons "A" []) (TCons "B" [])
TCons "->" [TCons "(->)" [], TCons "A" [], TCons "B" []]
```

The combined conclusion states that both satisfy the current `AliasSafe`,
their actual `rigidTerm` values are equal, and they are not ordinary
`Equivalent`. The private constant-leaf helper checks the existing
`isVariableSymbol` result. The constructor proof checks the literal marker,
A, and B children. Existing encoder and normalizer equations supply the
remaining two fields.

If the strict check passes, this disproves reflection under `AliasSafe` on
both compared types. It explains why a namespace repair must cover complete
internal arrow layouts as well as reserved variable leaves. The draft does
not claim actual source root acceptance or Haskell runtime reproduction for
this second collision.

The optional substitution-closure law is omitted. That observation concerns
the proposed reflection-domain predicate in the frozen read-only audit.
That predicate is not an existing source definition. This draft must not
imply that the existing `AliasSafe` predicate itself fails closure under
safe raw substitution. The one concrete law is the bounded useful cut.

No axiom, admission, linter suppression, future acceptance, membership,
successful output, semantic model, or source supplier is used. No compiler,
Git, repository source, root documentation, evidence, Haskell, or external
service operation was performed.

The strict-PASS R235 collision source remains unchanged at SHA256
`a329c85eeecaad277d0b21b68eceb592239e4eb5528b757593b0ed52f73d82d6`.


## internal-arrow-encoding-collision-repair-note.md

# Internal arrow collision: focused marker recognition repair

Frozen runtime draft, 2026-11-12 10:14 CET. Pending ROOT's next strict check.

Source: `/tmp/mcfta-native-bound-depth-20261112-1008/SourceSynthesisInternalArrowEncodingCollision.lean`.
SHA256: `68b95541acb9813f00190f486eba4997cc2dfb17e3daf7f5e0d06f76e30ce7b1`.
Size: 58 lines, 2611 bytes. One public combined law.

The first strict check found one error: reflexivity did not reduce
`isVariableSymbol "(->)" = false`. The rest of the draft elaborated.

The only source edit replaces that reflexivity argument. The new proof uses
`String.startsWith_string_eq_false_iff` to reduce the prefix question to the
literal character lists. `decide` proves that v,a,r,_ is not a prefix of
(,-,>,). Simplification then applies the actual `isVariableSymbol` equation
and its reserved-key membership test.

The public zero-hypothesis law remains exact:
`internal_arrow_constructor_collision`. Both literal raw types satisfy the
existing `AliasSafe`; their existing `rigidTerm` encodings are equal; their
existing ordinary `Equivalent` relation does not hold. No new safety
predicate, source acceptance, Haskell runtime claim, or input restriction
was added.

Historical arrow draft remains unchanged at SHA256
`9a2cb98ba9d5bd5bdf1edd329c1f23faaf68b12442f428d087a999fb2749036e`.
R235 full reserved-collision acceptance source remains unchanged at SHA256
`a329c85eeecaad277d0b21b68eceb592239e4eb5528b757593b0ed52f73d82d6`.
No compiler, Git, repository source, root documentation, evidence, Haskell,
or external service operation was performed.


## next-native-exposure-meaning.md

# Existing native exposure and independent meaning

Frozen: 2026-11-12 10:16 CET. Read-only audit after checkpoint `ff7555ea6c246bfed6335cfa4c67b02e363ab645`.

The requested one-step native meaning law already exists. No new semantic bridge is needed. Use `SourceEqualityProjectionRead.Read.exact` on the SAME actual read receipt. This law includes the independent meanings of the actual returned edge children. It does not replace them with graph acceptance at an unrelated heap.

## Shortest existing API

All paths below are under `lean/MicroCFTA/`.

`SourceEqualityProjectionRead.lean:18` defines `Read.done fuel completed` from the literal equation `MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done edges after`. Wrap the existing successful read with this constructor. Do not call a second read producer.

`SourceEqualityProjectionRead.lean:71` provides this exact public statement:

```lean
theorem Read.exact [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard}
    {edges : List (EdgeValue Symbol Guard)}
    (trace : Read value before edges after) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = [])
    (holds : Guard → Term Symbol → Bool)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    (∃ edge ∈ edges,
      MergedColdInterpretation.EdgeMeaning
        (InternedGuardedLanguage.meaning holds ambient) holds edge term) ↔
      InternedGuardedLanguage.meaning holds ambient value term
```

The namespaces opened in that source supply `State`, `Value`, `EdgeValue`, `SemanticReady`, and `Term`. Apply `.symm` if the caller needs whole meaning on the left. `InternedGuardedLanguage.lean:128`, `edgeMeaning_all`, converts each returned edge predicate to `InternedGuardedLanguage.edgeMeaning holds ambient edge term`. Its forest conversion at line 110 supplies `All₂ (meaning holds ambient) edge.children terms`. The symbol, ordered child list, and complete guard are those of this SAME edge record.

`Read.verified` at line 61 returns `Keeps before after`, `SemanticReady after`, `Edges after edges`, and `ClosedEdges edges` for this SAME receipt. `Keeps` includes the returned ready cache, cache growth, and issued-node history. `Edges` gives physical residency of these exact records. The nested provenance facts give availability of their children. Thus the independent meaning law and the child provenance attach to the actual returned heap.

When no read has yet been derived, `SourceEqualityProjectionRead.complete:43` derives one from current `SemanticReady`, availability, and closedness. It retains the same four outputs. Alternatively, retain the full `MergedFreshOrdinaryColdTermination.read_closed:211` output, including every larger-fuel equation, and wrap its ONE returned success with `Read.done`. The latter route preserves the literal fuel and stability packet without another producer.

## Requested same-read inclusion and soundness APIs

These existing laws independently confirm the direct API:

- `SourceSecondaryGateHead.lean:27`: construct `support : WarmHead before value := .closed closed` from current closedness. No false-gate trace is needed.
- `SourceSecondaryGateHeadLanguage.lean:171`, `nodeEdges_included support semantic available actual holds ambient term accepted`: whole independent meaning gives an edge in the SAME returned `edges` with independent child meanings.
- The same file at line 269, `nodeEdges_sound support semantic available actual edge member holds ambient term acceptedEdge`: this actual edge meaning implies the original whole meaning.
- The same file at line 158, `nodeEdges_verified support semantic available actual`: retains `Keeps`, `SemanticReady`, and `Edges` at the actual endpoint.

Use these APIs directly when they fit an existing proof. Do not add a duplicate law or a new semantic producer.

## Current invariants and existing proof route

The sufficient current invariant is `SourceEqualityRequiredSemanticCache.SemanticReady before` (`SourceEqualityRequiredSemanticCache.lean:18`). It contains ordinary `Ready` plus both independent probe-language heaps. Ordinary `Ready` (`SourceEqualityRequiredCache.lean:19`) contains `SemanticHeap`, `Covered []`, and `InternedOpenDepthReadback.Heap`. Also retain current `Available before value` and `value.free = []`. These are generic native-cache conditions. There is no synthesis admission, program-size, profile, word-capacity, origin-policy, or future read/meaning hypothesis in `Read.exact`.

The proof at `SourceEqualityProjectionRead.lean:79` constructs a proof-level `Head` from this exact read and deterministic `makeNode edges`. It composes `MergedColdInterpretation.makeNode_exact:59` with `SourceEqualityRequiredHeadLanguage.head_exact:20`. The latter already derives one common future cache for the root and its actual exposed children through `SourceEqualityRequiredFuture.exact:16`. It then replays the SAME successful exposure and transfers the graph languages to cache-independent native meanings. This future cache is an internally proved witness. It is not a public supplier or another runtime operation.

`SourceFreshOrdinaryColdGuardedExact.graph_exact:21` proves independent least-language correspondence for a replayed, resident, closed, supported finite row table. Its stronger table premises must not be silently attached to the immediate read heap. For one-step rows, `Read.exact` already performs the required composition without this assumption.

`MergedFreshOrdinaryExposureLanguage.actual_exact:75` alone compares actual rows with repaired epsilon-graph acceptance. `MergedFreshOrdinaryGuardedSoundness.nodeEdges_sound:129` alone supplies only soundness. The legacy `MergedExposureOriginalLanguage.nodeEdges_exact:15` uses the other reader and physical graph language. The lexical `LexicalExposureLanguage` laws use another syntax. None requires replacement or a new completeness proof for this task because the native `Read.exact` API already closes the requested seam.

## Remaining work

The missing work is operational composition for the SAME native bounded-depth execution: current memo invariants, the actual read cutoff, and the returned recursive-boundary exclusion. Root also identified existing `MergedOrdinaryHeight.height:16`, `child_lt:50`, and `makeNode_bound:63`; no new constructor-height definition is needed. Their use must retain each law's actual hypotheses.

This audit does not prove the bounded-depth copier, all prior sibling completion, total worker runtime, global work bounds, or Haskell correspondence. It does not claim that ordinary `Ready` alone suffices for the independent meaning theorem, or that an arbitrary open root satisfies the closed-read entry conditions. It identifies no Haskell defect. No source was changed and no compiler was run.


## next-duplicate-query-domain.md

# Duplicate query names and ordinary last lookup

Read-only audit, 2026-11-12. The candidate has a concrete path through the
actual source definitions. No new kernel counterexample, source acceptance
theorem, runtime result, or production defect is claimed here.

## Literal candidate

Use raw nullary constructors A, C, and R. The library has one monomorphic
group representative g with type `A -> C -> C -> R`, no argument-only entries,
empty avoid, and FirstOrder encoding. Its group members can be `["g"]`.
The query is `[("x", A), ("x", C)]` with goal R. The Program is
`App (App (App (Var "g") (Var "x")) (Var "x")) (Var "x")`.
It has four components.

None of these type names overlaps a variable tag or the internal arrow
constructor layout. The intended discrepancy uses the same Program name x
at different *distinct* annotations. A repair limited to type-tag separation
would leave this mechanism if it preserves the present query/table rules.
This is not an executed claim about a future repaired version.

## Exact current source path

Write `rowA = .mk "x" top [typeNode top A]` and similarly `rowC`.
`SourceSynthesisFirstOrderConstruction.context` at line 64 retains the literal
argument list:

```text
argumentEdges = [("x", rowA), ("x", rowC)]
```

The following existing checked laws apply directly. Do not prove new versions:

- `SourceSynthesisSelections.duplicate_pair` at line 233 resolves `["x","x"]`
  to `[("x", rowC), ("x", rowA)]`. The actual winner is reversed; it is not
  the caller's earlier list or a list with both payloads already replaced.
- `SourceSynthesisSelections.duplicate_singleton` at line 228 resolves
  `["x"]` to `[("x", rowC)]`.
- `SourceSynthesisSelections.resolveSelection_empty` at line 208 resolves
  `[]` to `[]`.
- `SourceSynthesisRelevantSingletonLookup.queryLookup_resolve_singleton`
  at line 188 agrees with actual ordinary last lookup. It preserves the
  later payload C when names repeat.

The complete source construction plan is:

| Cell | Required names and actual winner | Chosen split | Program/result |
| --- | --- | --- | --- |
| root relevant, true, size 4 | `[x,x]`, winner `[x:C,x:A]` | left 3, offset 1 | `(g x x) x : R` |
| function relevant, false, size 3 | `[x]`, winner `[x:C]` | left 2, offset 0 | `(g x) x : C -> R` |
| function relevant, false, size 2 | `[]`, winner `[]` | delegates to unrestricted terms | `g x : C -> C -> R` |
| final argument relevant, true, size 1 | `[x]`, winner `[x:C]` | singleton | `x : C` |
| middle argument relevant, true, size 1 | `[x]`, winner `[x:C]` | singleton | `x : C` |

The root take/drop lists contain one entry each. Their payloads differ, but
both child calls use only names `[x]`, so both resolve again to the later C
singleton. In the size-three function, offset zero gives the empty names key
to its size-two function and `[x]` to its argument. All split sizes are
positive and strictly smaller. Both offsets are in the actual winner bounds.

The empty-required size-two function delegates through `RelevantTyping.empty`
to actual `termsRows`. Its fallback chooses the library component g and an
unrestricted argument x at the earlier A row. This earlier row remains in
the literal size-one pool:

- `SourceSynthesisSourceTermsTyping.oneRows`, lines 44-47, includes every
  `context.argumentEdges` row, not only the last named binding.
- `LeafTyping.argument`, lines 74-76, has no last-lookup premise.
- `SourceSynthesisTypeSubstitutionWitnesses.query_argument_terms`, line 187,
  already derives size one from *any* literal query binding. The earlier
  `("x", A)` membership is enough for this producer.
- `fallbackFunctionRows`, lines 63-64, includes g because avoid is empty.
  `TermsTyping.fallback`, lines 97-105, applies g to that actual x:A leaf.

The g scheme is monomorphic. Its discovered substitution keys are empty, so
the existing component producer needs no image-admission supplier. Its type
contains only A, C, R, and ordinary arrows. The actual constructor catalog
contains A/0, C/0, and R/0. Structural `TypeIn` witnesses cover the result
annotations `C -> C -> R`, `C -> R`, and R. No unproved blanket rigid-query
universe premise or tag collision is needed.

At the root choose the actual context argument list and use existing
`self_mem_permutations`. A completed `RelevantTyping` receipt then feeds
`SourceSynthesisFirstOrderTotality.firstOrderRaw_member_total` once at signed
size four. Its constructor success follows from the already-checked source
totality result. Actual root *acceptance of this candidate* still needs the
new concrete source receipt and kernel check. This audit did not construct
or execute that theorem.

## Ordinary last lookup disagrees independently of encoding

`SourceSynthesisOrdinaryTyping.queryLookup`, line 35, reads `arguments.reverse`
with `List.lookup`. Here x has only the last raw type C in that judgment.
`Typed.queryArgument`, lines 46-48, requires that lookup.

The only component named g has a monomorphic `A -> C -> C -> R` scheme.
Every raw substitution leaves it unchanged. The query has no g binding and
the argument-only library is empty. Thus an ordinary derivation of the first
application `g x` would require x at a type ordinarily equivalent to A while
its query binding is C. Normalization keeps these distinct nullary
constructors. The remaining applications cannot repair the first application.

The proposed formal rejection statement is `∀ typ, ¬Typed lib query program
typ`. It needs conversion-aware variable/application inversion, as in the
existing ordinary encoding-collision proof. The existing fixed badQuery law
does not instantiate to this different library/query. No new ordinary
untypability theorem was proved in this audit.

## Public Query route has no uniqueness gate

The actual public Haskell module exports `Query(..)` at
`cfta-generator/src/Data/CFTA/Gen/Synthesis.hs:50`. Lines 315-319 define an
unrestricted list field and goal. It is not a hidden smart constructor.

`rawSearchSpace` at lines 733-744 directly maps all supplied query entries to
`argumentEdges`; `anyArgument` contains all those rows. `buildTerms` at lines
756-765 retains this pool in size one and the size-two fallback. The actual
relevant table at lines 774-791 uses `LazyMap.fromList` with names-only keys,
enumerates the literal selections, and re-reads child names. No validation,
normalization to unique names, or rejection runs before those operations.
`searchSpace` at lines 644-645 composes reduction/refolding after the raw
constructor; it has no Query uniqueness check.

This direct exported Query/rawSearchSpace route already establishes source
reachability. A helper or another frontend cannot impose a universal
uniqueness invariant on it. It does not establish runtime acceptance of the
candidate or preservation through all native reduction stages.

Other inspected owned routes do not supply a missing raw-API gate:

- `Synthesis/Hybrid.hs:152` maps Liquid query arguments directly to `Query`.
  Its separate program checker at lines 120-134 may reject candidates; no
  claim is made that this hybrid outcome returns the candidate.
- `Synthesis/Walk.hs:268` and line 277 build the Query from required leaves.
  A common name prefix is applied; that alone does not establish uniqueness.
- `Synthesis/Liquid.hs:214` exports a separate list-valued `LiquidQuery`.
  `parseQuery` at line 225 collects parsed parameters. These are different
  algorithms and do not validate the direct plain Query constructor. No
  global uniqueness theorem about those frontend inputs was found or assumed.

## Existing proof boundaries are consistent with the candidate

The actual source `TermsTyping`/`RelevantTyping` rules permit the path above.
They do not assert ordinary typing. The singleton resolver agreement proves
the later payload and is an ingredient in the path, not a rejection of it.

The ordinary-to-source `UsesEligible` certificate at
`SourceSynthesisOrdinaryRelevantCompleteness.lean:38` requires ordinary
`ProgramEligible` for unmarked subtrees. Its marked query case at line 43
uses actual last lookup. The first unmarked x:A use cannot satisfy that
ordinary certificate under this query. Therefore the existing forward
completeness law neither proves nor contradicts generic accepted-to-ordinary
soundness here. It cannot be used as a supplier to prove this candidate's
source membership.

The bounded search found checked generic duplicate-winner laws, but no
concrete full source acceptance and ordinary-untypability theorem for this
four-component example. The checked reserved-variable collision and internal
arrow collision concern different mechanisms. This candidate does not rely
on either collision.

## Smallest next formal cut and contract choices

A next source module can keep literal lib/query/Program definitions and prove
one combined law with this shape:

```lean
theorem duplicate_query_source_counterexample [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
  ∃ expression term,
    firstOrderRaw lib query 4 = .ok expression ∧
    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) term ∧
    Projection literal Prod.fst term program ∧
    toProgram literal Prod.fst term = program ∧
    (toProgram literal Prod.fst term).components = 4 ∧
    ∀ typ, ¬Typed lib query program typ
```

This is an unimplemented proposed header. Use actual source constructors,
the checked duplicate/empty resolution laws, and one derived root .ok.
Do not use `UsesEligible`, future membership/success, a semantic model,
encoded reflection, or a runtime acceptance supplier.

For a conditional last-lookup soundness domain, distinct query names are a
simple sufficient row-origin condition. A weaker useful condition permits
duplicates when every earlier type is ordinarily equivalent to the last:

```text
for each (name, original) in queryArguments,
there exists last with queryLookup queryArguments name = some last
and Equivalent original last
```

This row-origin condition is separate from encoding namespace safety and
the finite source universe. Per-use compatibility can be weaker still if
only used unrestricted rows are checked. None is an existing public API
invariant. Adding it as an assumed Liquid Haskell contract would narrow the
proved domain and would not repair unrestricted Query behavior.

If conventional last-binding semantics is intended for all public inputs,
the actual algorithm must make unrestricted query uses agree with it, or
explicitly reject/validate incompatible duplicate input. Preserve the
separate required-token multiplicity: simply deduplicating the Query list
also changes how many required uses the current source enforces. Another
possible specification is overload-like lookup from any binding; that would
change the ordinary judgment and needs an explicit decision. This audit
chooses no API or semantic change.

Only this runtime note was written. No Lean/Haskell source, compiler, Git,
repository documentation, evidence packet, or external service was changed
or run. The 58-line internal arrow source remains frozen after its strict PASS.


## Completion proof repairs

The initial 244-line draft needed private Cache.put reductions, correct nil
conjunctions, membership substitution, explicit local constructor reductions
and fully determined Symbol/Guard parameters. The final 256-line source
preserves the exact public complete header. No premise or axiom was added.
The original ca5 and intermediate 52da drafts remain in the runtime.


## next-source-arity-bound.md (next-cut audit/draft; not a new checked result)

# All-row arity from current source data

Frozen: 2026-11-12 10:44 CET. Read-only audit. No source or compiler changes.

## Existing computed current-inventory bound

Use `SourceRecursiveIntersectionSourceProfile`; no new maximum function is needed. Paths below are under `lean/MicroCFTA/`.

- `SourceRecursiveIntersectionSourceProfile.lean:36` defines `edgePayloads` by reading all actually issued edge identities below `source.edges.next`.
- `limits:45` computes `.arity` as the sum of the child counts of those payloads. This conservative cap includes every stored row before guard evaluation.
- `edge_read_bound:108` bounds an actual edge read by this computed cap.
- `resident_read:120` derives that read from `Facts source` and `EdgeResident source edge`. Compose these two laws to bound every current resident edge. No `SizeOf` instances are needed for this route. `resident:145` also packages a syntax-size bound but adds `SizeOf` instances.

For a SAME actual `SourceEqualityProjectionRead.Read value before edges after`, `Read.verified:61` gives `SemanticReady after` and `Edges after edges`. Thus these existing profile laws already give `edge.children.length ≤ (limits after).arity` for every returned edge, including rejected and dead rows. If a read has not been obtained, `SourceEqualityProjectionRead.complete:43` derives it from current readiness, availability, and closedness. This introduces no future arity supplier. It gives a cap computed from that internally derived endpoint; it does not yet give a cap fixed at the original input.

The larger `InternedValueMassHeap.initialBound:39` also bounds initial complete records through `initial:54`. Prefer the direct profile cap for arity. Neither statement fixes the original payload mass through later allocation.

## Original FirstOrder expression

The source row forms are explicit:

- `SourceSynthesisFirstOrderConstruction.application:47`: four ordered children.
- `ofType:52`: two children.
- `component:43` and the rigid query argument rows in `context:64`: one child.
- `SourceSynthesisTypeSyntax.arrowMarker:77`: zero children; `arrowType:80`: three children.
- `typeNode:84` and `allTypesBody:93`: constructor rows have their declared argument count. The two-argument `Fun` alias becomes the three-child arrow row.
- `SourceSynthesisGeneralizeSyntax.replace:94` substitutes the type universe for variable leaves and preserves each other literal row's arity. `finish:104` changes the outer symbol and guard but retains the children. `generalize:109` adds no wrapper child.
- `termsRows:84`, `relevantRows:112`, and `firstOrderRaw:140` in FirstOrderConstruction compose these forms with unions and ordered lists. Those lists can grow with the requested size. Their lengths are not constructor child arities.

`max 4 catalogArity` is not a valid unrestricted raw-input theorem. `constructorsOf:70` excludes every `Fun` name, while `typeNode` retains `Fun/n` for `n ≠ 2`. For example, a rigid `Fun/5` goal contributes an original five-child row even when its own name contributes nothing to the catalog. This concerns rows before acceptance or pruning. It does not assert that the resulting program query accepts a term.

A safe prospective FirstOrder syntax cap is `max 4` of the maximum **raw constructor argument count in all original library and query types**, including excluded `Fun/n` occurrences and nested types. Arrow conversion needs only three. The catalog universe uses those same inputs. A proof of this syntax cap was not found. `InternedStoredEncodingWidth.Width:19` bounds rows and union lists as well as child lists. Its `encode_width:92` concerns stored-value encoding and payload mass. It does not prove this original-expression cap. This audit does not cover the separate Curried domain input.

## What later operations preserve

`InternedStoredSubstitutionScope.encodeMany_length:51` and `encodeEdges_length:58` already retain literal list lengths. `SourcePruningEnumerationArityOrigins.buildMany_length:136` gives actual constructor child-plan length preservation for its constraint specialization. The heap laws at lines 167, 315, and 323 preserve **projected guard arity** through construction, stored substitution, and unfolding. That heap predicate (`Heap:31`) is not a numerical maximum-child-count predicate. It cannot be substituted for one.

`MergedPhysicalGroupEdges.makeEdge_fields:27` gives exact returned children under current `Facts` and child availability. `largeEdge` and `columns_length:128` retain the selected group's child count. `EqualityLeafProjectionSetChildren.same_arity:24` selects the direct edge constructor under an actual length equality. The new strictly verified `SourceNativeBoundDepth.children_length` supplies that equality for a SAME successful depth-copy traversal. It does not supply edge fields without the current physical invariants.

`SourceRecursiveIntersectionCompile.compileEdge:46` checks equal input arity before the child walk. The equal branch reconstructs the zipped child count. The mismatch branch constructs the empty sentinel with **one child**. `SourceRecursiveIntersectionKernelReadback.edge_readback:71` exposes the equal-arity walk and rebuilt fields. Closure must account for the sentinel ceiling, conservatively `max cap 1`. The existing private `SourceCurrentAllocatedFiniteOrdinaryParentShapes.rejected_shape:51` uses that ceiling. Its ordinary-domain premises do not establish a recursive-source heap invariant. Arbitrary external constructor templates can introduce arbitrary arity. Include their literal rows before claiming closure.

## Smallest genuine missing cut

The useful next law fixes the cap at the current input and proves that the SAME actual closed read retains it in every stored edge. The existing laws above already establish the initial premise with `cap := (limits before).arity`. An observer can have this shape, with `Read` denoting the existing receipt:

```lean
theorem Read.arity_heap
    (trace : Read value before edges after)
    (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = [])
    (initial : ∀ key edge, before.edgeRecords key = some edge →
      edge.children.length ≤ cap) :
    ∀ key edge, after.edgeRecords key = some edge → edge.children.length ≤ cap
```

Retain the normal `DecidableEq (EdgeKey Symbol Guard)` instance. This is a proposed theorem, not an existing checked declaration. Its missing ingredient is numerical child-count preservation through the actual fresh constructor/substitution/unfold chain. The existing projected-arity proofs identify the proof route, but do not prove this numerical result. A public closed-input producer should call `Read.complete` ONCE, retain its ENTIRE actual read/Keeps/SemanticReady/Edges/ClosedEdges packet, and append this property with the initial cap derived internally. Do not add a future heap or future arity premise.

After that cut, the SAME bounded-depth copier can preserve the cap using child-length preservation and exact edge fields. Intersections require their own sentinel-aware closure. None of these arity facts bounds row count, union size, native heap mass, guard syntax, total reader fuel across the whole copy, all prior siblings, or whole enumeration runtime. Those obligations remain separate. This audit identifies no additional Haskell defect; the `Fun` catalog behavior is the already recorded source boundary.


## duplicate-query-acceptance-note.md (next-cut audit/draft; not a new checked result)

# Duplicate query source acceptance draft

Frozen runtime draft, 2026-11-12 10:45 CET. Pending ROOT's first strict check.

Source: `/tmp/mcfta-native-bound-depth-20261112-1008/SourceSynthesisDuplicateQueryAcceptance.lean`.
SHA256: `ca579e2611d23bea3499610737c5ff44c8e860adecd95511bbb7ac2ce60bdfcc`.
Size: 271 lines, 13813 bytes. One public combined law and five literal data
or witness definitions. The only imports are `SourceSynthesisOrdinaryTyping`
and `SourceSynthesisFirstOrderTotality`.

Namespace: `MicroCFTA.SourceSynthesisDuplicateQueryAcceptance`.

## Exact public data and statement

- `library`: one group representative g at monomorphic `A -> C -> C -> R`,
  members `[g]`, no argument-only entries, empty avoid, FirstOrder.
- `query`: the original ordered entries `[(x,A),(x,C)]`, with goal R.
- `program`: `App (App (App (Var g) (Var x)) (Var x)) (Var x)`.
- `duplicateBody`: a literal joint term whose first x annotation is A and
  whose next two x annotations are C.
- `duplicateWitness`: the literal filter node with query goal R and that body.

The public zero-supplier law is `duplicate_query_source_counterexample` at
line 250. Its only parameters are the existing formula and solver interfaces,
with their usual `DecidableEq FullSyntax.Formula` instance. It returns one
actual expression satisfying all of:

1. `firstOrderRaw library query 4 = .ok expression`.
2. Actual guard evaluation of that expression accepts `duplicateWitness`.
3. The same witness has `Projection` to the literal `program`.
4. The existing `toProgram` decoder returns that same Program.
5. The decoded Program has exactly four components.
6. For every raw type, ordinary `Typed library query program` does not hold.

The raw type tags are only A, C, and R plus the raw function constructor.
The source proof uses no encoded equality between different raw types. There
is no reserved variable tag or ordinary raw arrow-layout constructor in the
literal input.

## Source proof

Private literal resolver facts at lines 79-91 directly reuse
`resolveSelection_empty`, `duplicate_singleton`, and `duplicate_pair`.
The full actual winner is `[x:C,x:A]`. Each child singleton re-resolves by
name to `[x:C]`.

The monomorphic g leaf uses actual `LeafTyping.component`. Its discovered
variables list is empty, so the source image requirement is vacuous. The
earlier x:A leaf uses the existing `query_argument_terms` producer with its
actual first-entry membership. `first_terms` then chooses g from the actual
empty-avoid fallback pool and applies it to that earlier unrestricted row.
The source result is `C -> C -> R`.

`second_relevant` uses actual size three, left size two, and offset zero.
Its function receives the empty required key and delegates to `first_terms`.
Its marked argument resolves to x:C. The source result is `C -> R`.

`source_body` uses actual size four, left size three, and offset one of the
resolved `[x:C,x:A]` winner. Both child names lists are `[x]`, and the final
argument uses the actual last x:C singleton. The result is R. Structural
`TypeIn` witnesses derive from actual C/0 and R/0 catalog membership and the
existing arrow constructor. There is no future universe supplier.

The public proof chooses the actual context argument list and the existing
self-permutation law. It calls `firstOrderRaw_member_total` exactly once,
deriving both .ok and root acceptance. Existing projection supplies decoder
identity, and the literal Program supplies component count four.

## Independent ordinary rejection

`variable_origin` retains conversion and establishes that an ordinarily
typed variable here is either g at a type equivalent to its monomorphic
scheme or x at a type equivalent to C. Query origins use actual last lookup,
not arbitrary input-list membership. Group substitution cannot alter the
monomorphic scheme.

`no_first_application` shows that any ordinary derivation of `g x` requires
the same normalized domain to equal both A and C. Their distinct ordinary
constructor names give a contradiction. The private `application_function`
helper preserves the function premise through conversion. Applying it twice
to the full Program reduces any proposed ordinary type to the impossible
first application. The final public field quantifies over every raw type.

No ordinary `UsesEligible`, encoded reflection, new typing relation, semantic
model, source membership, acceptance, or successful output supplier is used.
The public header adds no uniqueness or type-domain premise. The draft has
no axiom, admission, or linter suppression.

## Limits and preservation

This is a pending kernel-ready draft. It makes no runtime acceptance or new
Haskell defect claim. Such a claim needs ROOT's separate runtime probe. It
changes no query semantics or public API and proves no generic all-source
ordinary soundness theorem.

The checked 58-line arrow source remains SHA256
`68b95541acb9813f00190f486eba4997cc2dfb17e3daf7f5e0d06f76e30ce7b1`.
The checked full reserved-collision source remains SHA256
`a329c85eeecaad277d0b21b68eceb592239e4eb5528b757593b0ed52f73d82d6`.
Only this new runtime draft and note were written. No compiler, Git,
repository source, root documentation, evidence, Haskell, or external service
operation was performed.
