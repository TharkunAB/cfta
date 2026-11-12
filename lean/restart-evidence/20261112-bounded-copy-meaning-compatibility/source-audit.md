# Native bounded-copy language and query coherence

The persistent goal is ACTIVE. This checkpoint does not complete that goal.
The base is 073737c31d9049751b9add5350d29559d86f3876.
Integrated main is dedd47da878e78aa5be9947247d8156675956b59.
The main and formalize references were refreshed at 11:21 CET on 2026-11-12.
No production Haskell or Liquid Haskell code changed.

## Verified source

Three new modules contain 1,188 lines and four public theorems.
Every own-source strict check passes. Every public theorem has an explicit
#check and an axiom report. Only the standard propext, Classical.choice, and
Quot.sound axioms are allowed. All existing public theorems remain present.

- SourceSynthesisDuplicateQueryAcceptance: 280 lines; 1 public laws; SHA256 c4beea0d68c8f4cb5330e9633c2c22ba18fb1be5ce2e8391cf27280bbfee837e.
- SourceNativeBoundDepthMeaning: 515 lines; 1 public laws; SHA256 5e2b94180117c4feb839961032c41f548e87db2225e29043fc247555aaa1ef07.
- SourceNativeReadArityHeap: 393 lines; 2 public laws; SHA256 84b566beeddc09d415d6153b0fdbd94f906faf6e7b8d41e008a6f2f10e3dde73.

## Strongest new positive result

One existing native bounded-copy completion producer supplies one stable
cutoff, value, returned heap, and memo from current SemanticReady, Available,
and root closedness. The same receipt retains all old physical facts and all
larger-fuel endpoint equations. Its result is recursively ordinary.
Its existing ordinary height is at most `(depth + 1).toNat`.
For every guard interpretation, ambient environment, and term, its independent
meaning is exactly the input meaning restricted by signed term height
`term.height <= depth + 1`. Negative depth has no accepted term.
No second copy or future successful read/meaning/memo supplier is used.

The numerical read-cap theorem starts with an actual current heap cap.
It observes the SAME ProjectionRead.Read. The cap holds at the SAME returned
heap and at every returned row. The initial cap comes from the existing
current issued-inventory arity sum. Guard/path Fits is a different predicate.

The earlier ordinary admitted-Program completeness and original native startup
results remain. They retain required-token multiplicity, exact annotations,
projection, decoder, component count, worker packets, the same assignment,
and computed Room conditions. The prior fixed-Program unbounded-annotation
counterexample also remains. Whole annotation size is not Program size.

## New Haskell contract finding

The literal library has g:A->C->C->R. The literal query has x:A,x:C and goal R.
The source accepts the exact four-component annotation of g x x x.
Independent ordinary last-binding typing rejects it at EVERY raw type.
A separate Haskell packet reproduces raw acceptance and the generated Program.
All five controls finish within their ten-second limits:

| Query | Raw acceptance | Output |
| --- | --- | --- |
| x:A,x:C | True | g x x x |
| x:C | False | none |
| x:C,x:C | False | none |
| x:C,x:A | False | none |
| a:A,c:C | True | g a c c |

Required singleton uses resolve the LAST x type. Unrestricted query rows retain
BOTH original entries. The earlier unmarked x:A fills the first slot, followed
by two required x:C uses. The decoder retains only the repeated name x.
The public raw API has no established uniqueness or coherence validation gate.
This finding concerns ordinary last-binding typing. Parser and refinement
routes are not covered by this execution packet.

The external repair must state the query-name contract. Same-name ordinary
Equivalent types suffice for this row-origin typing obligation. Unique names
are stronger. Raw syntactic equality is stricter than ordinary Equivalent.
Encoded equality is unsafe because the known encoding collisions remain.
One consistent lookup rule is another repair route. Keep duplicate required
token multiplicity if it remains part of the API. Do not silently discard it.
The static audit below also records differing lookup policies in Liquid.hs.
It establishes no new runtime failure in that refinement route.

The reserved variable/constructor collision and Fun-non-two discovery defect
remain independently reproduced and unfixed. The AliasSafe internal-arrow
collision remains kernel checked. A namespace repair alone does not address
the duplicate-query case. No production repair is applied by this checkpoint.

## Validation and retention

The full import graph is acyclic. It has 5,784 live modules and four affected
modules. Audit directly imports 4,781 modules. All 259,273 previous Audit bytes
remain after three new imports. The full Audit build passes with 93,431 axiom
reports. This count does not establish full-system correspondence.
All five portable checks pass from /tmp. They cover three proof packets,
the new Haskell reproduction, and the Audit frontier. All runs use the existing
serial four-GiB memory.max and memory.high, zero swap, and one Lean thread.
No queue, cap, heartbeat, or production Haskell setting changed.
The /tmp runtime is /tmp/mcfta-bounded-copy-meaning-20261112-1051/.
At 11:21 CET it used 324 KiB. The filesystem had 187.6 GiB free at 11:16 CET.
The runtime preserves failed proof drafts, diagnostic logs, and repairs.
No binary evidence archive is required by these source checkers.

## Remaining full objective

Attach a full-guard row view to the SAME native copied result. Prove the actual
operation, allocation, and compiler correspondences. Preserve the fixed input
arity cap through the whole SAME copy. Derive original-input work and depth
bounds across earlier hooks, retained caches, all siblings, and all alternatives.
Retain the distinction between P, expandable flags A, and logical W_B=(B+1)P+A.
This logical measure is not a runtime claim or a Program-size bound.
Prove both signed API directions and both inverse contracts with order and
multiplicity. Preserve source errors, actual Word/Int limits, lazy demand,
full guards, refinement checks, and training boundaries. The main eager order
and formal deferred order still need their own correspondence.
The counterexamples and positive admission results must both remain visible.

## Next source audits

These notes are implementation plans. They add no theorem or execution result.
Their proposed future statements must be proved from current inputs.

---

# Query coherence contract after the duplicate counterexample

Read-only audit, 2026-11-12. The exact size-four source counterexample passed
strict checking at SHA256 `c4beea0d68c8f4cb5330e9633c2c22ba18fb1be5ce2e8391cf27280bbfee837e`.
The separate packet `lean/restart-evidence/20261112-duplicate-query-runtime/checked.json`
records all five runtime controls passing with the same literal g library.
No production repair or public uniqueness contract is established.

File references below use HS for `cfta-generator/src/Data/CFTA/Gen/Synthesis.hs`
and LQ for `cfta-generator/src/Data/CFTA/Gen/Synthesis/Liquid.hs`.

## Minimal raw-type condition

Unique query names are sufficient for the row-origin mismatch, but stronger
than necessary. The weaker whole-query condition is:

```text
For each (name, original) in queryArguments:
  lastLookup(queryArguments, name) = Some last
  and normalizeTy original = normalizeTy last.
```

An equivalent data-only formulation requires ordinary `Equivalent` types for
every pair of entries with the same name. Lookup existence follows from
actual list membership; it is not a future lookup-success supplier. The minimum
condition uses ordinary Fun/2 normalization. Raw Haskell `Eq Type` is stricter;
encoded equality is insufficient because the checked collisions preserve it.
Keep rigid query variable names distinct under ordinary equality.

Why this suffices for this gap: the existing last query rule types name at
last, and ordinary conversion types it at original using the symmetric
equivalence. Thus every earlier unrestricted query row has compatible named
typing. The checked `equivalent_rigidTerm` law also equates their annotations.
This does not supply namespace reflection, accepted-row origin extraction,
or whole-system soundness. Those remain separate obligations.

Exact formal references: `SourceSynthesisOrdinaryTyping.lean:23` (normalizer),
`:35` (last lookup), `:46` (query rule), `:53` (conversion), and `:99`
(`equivalent_rigidTerm`). The checked counterexample is
`SourceSynthesisDuplicateQueryAcceptance.lean:259`.

## All query routes must agree

| Route | Actual source | Required agreement |
| --- | --- | --- |
| Original rows | HS:743 maps every query entry; HS:744 forms anyArgument | Every retained payload must agree with the chosen named typing policy. |
| Unrestricted startup/fallback | HS:757 and HS:765 reuse anyArgument | An earlier conflicting row must not remain usable independently of that policy. |
| Required table keys | HS:775-781 uses names-only keys and last Map insertion | Preserve actual multiplicity and winner order; do not assume earlier payload identity. |
| Required children | HS:783-790 delegates empty keys to unrestricted terms and re-reads split names | Singleton, pair, and take/drop calls must use compatible payloads. |
| Goal/catalog | HS:734 and HS:796-806 encode the goal and discover constructors | Apply the same type representation; catalog admission alone proves no name coherence. |
| Program decoding | HS:917-921 drops annotations and keeps only names | Decoding cannot recover which duplicate binding an x occurrence used. |

The exact singleton/last-lookup correspondence is already checked in
`SourceSynthesisRelevantSingletonLookup.lean:168` and `:188`. Exact duplicate
singleton and reversed full-pair winners are already checked in
`SourceSynthesisSelections.lean:228` and `:233`. Reuse them.

Coherence keeps repeated required tokens. Even `[x:C,x:C]` has two original
entries, so the required count remains two. Their equivalent payloads can be
interchanged for ordinary typing without removing either entry. Do not
deduplicate queryArguments or selection keys as an incidental repair.
The runtime C,C control is a negative control for the particular g domain A;
it is not a generic coherent-query soundness theorem.

## Public API and higher callers

HS:50 exports `Query(..)`; HS:315-319 stores an unrestricted list. The direct
HS:733 rawSearchSpace route performs no uniqueness/coherence validation.
HS:645 adds reduction/refolding afterwards. This raw route is the reproduced
counterexample boundary. A caller convention cannot restrict all public uses.

LQ:225 builds LiquidQuery from parsed parameters; LQ:971 simply collects arrow
parameters in order. No freshness check occurs in those functions. This audit
did not execute a duplicate parser input; the runtime packet explicitly keeps
parser-route impact unestablished. `Synthesis/Hybrid.hs:152` forwards the
Liquid argument list to plain Query. `Synthesis/Walk.hs:268` and `:277` add a
common prefix and build Query; that transformation alone does not prove
distinct names.

There is a further static policy difference for the external repair agent:
LQ:668 uses Haskell `lookup` on liquidArguments, so it reads the first match.
LQ:671 also uses first lookup on heads; LQ:557 uses Map.fromList for functions,
which keeps the last match. LQ:569-573 conjoins all input refinements under
their names. These are source facts, not a new reproduced Liquid defect.
Ordinary base-type equivalence makes first and last base types compatible;
it does not identify different refinements or resolve their binder scope.
The Liquid frontend needs its own full refinement/name policy or a validated
uniqueness condition. Do not claim this plain Type audit proves that policy.

## Reviewable repair choices

- Validate uniqueness, or the weaker ordinary coherence condition, explicitly
  at the public boundary. Document the restriction and invalid-input behavior.
  A Liquid Haskell precondition alone narrows the theorem domain while raw
  Query remains constructible; it does not repair unrestricted behavior.
- If last-binding semantics is the intended unrestricted contract, canonicalize
  query payloads consistently for all pools/lookups. Preserve original token
  multiplicity separately. This is an explicit semantic decision for earlier
  conflicting payloads, not an automatic list deduplication.
- Distinct binding identities or overload-like lookup require a different
  reference/output specification. Do not change ordinary Typed to arbitrary
  input membership merely to certify the current decoded output.

The external Haskell/Liquid Haskell agent should state the chosen policy,
enforce it on every path above, and retain both the mixed-duplicate regression
and coherent/distinct-name controls. Namespace repair remains independent.
Only this note was written. No source/proof, compiler, Git, repository docs,
evidence, or Haskell changes were made. The verified duplicate source is frozen.

---

# Same returned native copy to finite rows — unproved next cut

Frozen: 2026-11-12 11:19 CET. Read-only audit. No source, compiler, Git, Haskell, or root-document changes.

The shortest bridge uses the existing `SourceInternedRows` adapter on the SAME returned component. Do not run `EnumerationBuilderRuntime.fastBuild` again. R237 already proves exact bounded native meaning; another copier adds an unnecessary endpoint correspondence obligation.

## Closed primitives and the exact missing attachment

- `SourceNativeBoundDepthMeaning.complete_exact:489` retains the entire old stable result/value/heap/memo and adds DeepOrdinary, existing ordinary-height bound, and exact bounded independent meaning. Use its current-input producer ONCE, then derive the row view of that exact returned value and heap.
- `SourcePreparedSharedRows.reference:18`, `read:26`, and `exposure:30` ALREADY handle arbitrary Guard and real native IDs. Empty uses `none`; native node identity zero uses `some 0`, so there is no collision. `read_available:76`, `read_identity:82`, and `reference_bounded:94` use CURRENT Facts and Available, without a prepared cache premise. Current Facts is `semantic.ready.semantic.1.normal.facts` at the returned heap.
- Its `heap:70` is unsuitable as the immediate shortcut: it uses `rows` and GLOBAL Context/Prepared to expose arbitrary Mu/union records in a fixed cache. The returned heap retains old source Mu and unrelated records. DeepOrdinary of the returned value does not imply global Prepared or global ordinary rows.
- `SourcePhysicalSharedRows.heap:35/read_node:45/heap_node:56` and `SourcePhysicalSharedRowsLanguage.language_exact:34,toRows_language:69` already prove the ordinary physical snapshot pattern, but their Guard=Unit and Plain premise cannot be applied to arbitrary full native guards. `SourceInternedIntersectionRowsPhysical.Plain:16` has the same Unit restriction. Do not erase the full constraints to reuse these statements.

The missing small attachment is a full-Guard ordinary snapshot readback and its language theorem on CURRENT available DeepOrdinary values. Define only this snapshot, using the existing generic accessors:

```lean
-- Proposed helper, not yet implemented.
ordinaryHeap state identity :=
  ((SourcePreparedSharedRows.read state identity).toList).flatMap fun value =>
    (InternedEdgeResidency.nodeEdges value).map SourcePreparedSharedRows.exposure
```

This is a view of actual immutable native payloads. It performs no read/unfold/copy/allocation. Outside the returned component, Mu/union records contribute no ordinary rows. Claim source-language correctness only for the available DeepOrdinary component. Do not identify this whole snapshot with full native recursive semantics.

For Empty the encoded state has no rows. For an actual ordinary node, `read_identity` gives the identical complete canonical payload at its actual ID, and the snapshot returns its exact ordered rows. Available.children plus facts.cached/linked supplies each child. DeepOrdinary supplies the same component condition recursively. An induction on the accepted term, using `InternedGuardedLanguage.laws`, gives the full-guard analogue of existing `SourcePhysicalSharedRowsLanguage.language_exact`. No future rows/heap/source meaning premise is needed.

## Finite table and rank are derived from the same current heap

`SourceInternedRows.Heap:36` is already a full-constraint snapshot. Its `collect:48` and `toRows` visit actual child references and retain first exposed rows. Derive ClosedDomain for `List.range after.nodes.next`: every snapshot row comes from `read_available`, and every child `some id` is bounded by `reference_bounded`. This derivation does not require every final-heap record to be ordinary. A Mu record omitted by ordinaryHeap has no snapshot successors. The returned root's reference is bounded by the same existing law.

Then invoke `SourceInternedRowsFinite.toRows_finite:128` once on this DERIVED domain. It returns one table at all larger traversal cutoffs. `SourceInternedRowsLanguage.toRows_language:105` identifies that same returned table's interpreted language with the snapshot graph. No second bounded copier, warmed native heap, or independently produced bounded result is used.

Reuse `MergedOrdinaryHeight.height`, `child_lt:50`, and the current readback for a snapshot-state rank. Empty has rank zero; `interned id` has the ordinary height of `read after id` (default zero if absent). Each actual ordinary row child has strictly smaller rank. In particular, the returned component has the already proved root height bound `(depth+1).toNat`. Canonical sharing causes no difficulty: identity determines one immutable payload, while many depth keys may point to it. There is no physical-ID inverse returning a unique `(depth,id)` key.

A minimal new public `complete_rows` header should keep exactly the CURRENT original `depth/root/before/SemanticReady/Available/closed` inputs and return the SAME entire `complete_exact` receipt, plus:

```lean
-- Proposed result additions; ordinaryHeap is the helper above.
∃ rowCutoff raw,
  (∀ fuel, rowCutoff ≤ fuel →
    SourceInternedRows.toRows (ordinaryHeap after) fuel
      (SourcePreparedSharedRows.reference result) = some raw) ∧
  ∀ holds ambient term,
    Language.Accepts (SourceInternedRows.graph (ordinaryHeap after) holds)
      (SourcePreparedSharedRows.encode result) term ↔
      InternedGuardedLanguage.meaning holds ambient root term ∧
        (term.height : Int) ≤ depth + 1
```

Use the snapshot-language lemma followed by the SAME R237 result's bounded-meaning law. The old raw native cutoff and this finite row-traversal cutoff are different resources. A graph rank/table-language corollary is useful if small; do not turn it into a future supplier in this public header.

## What this does not supply

- `EnumerationBuilderFastPaths.fast_requested_from_state:190` assumes a source-row function and its scoped cache validity. Its exact bounded language and memo-sharing laws are closed, but a byte/identity/cache simulation with native caches is still an extra obligation. It is not needed for the direct same-result row adapter above. The abstract row reader's empty-zero convention must not be confused with native ID zero.
- `SymbolicGraphView.OperationRows:120` and `SymbolicProductRows.ClosedOperationRows:132` need actual intersection, projection, condition, template identities, normalization, and the self-intersection shortcut on the SAME graph/family. A finite current row table and rank do not prove those operation correspondences.
- `SymbolicAllocatedGraph.AllocatedRows:51` requires actual permitted constructor histories from the empty allocation state. The final native heap contains old Mu and independent caches. Neither DeepOrdinary of the returned component nor its height bound supplies that history. The derived ordinary-height rank can be used directly where GraphBudget.ofRank accepts a rank; do not add AllocatedRows as a new premise.
- `SourceFiniteAutomaton.Rows:18` and `exact_index_api:393` still require the source Symbol/constraint decomposition, actual indicator/compact/symbolic compiler behavior, operation laws, and preserved errors. Arbitrary Guard in R237 cannot itself provide sourceEqualities/projectability or a compiled indicator score equation. Preserve actual full guards in the snapshot.
- `SourceInternedRowsValidated.toFTA_finite:113` preserves a possible validation error. Do not claim unconditional `.ok`: valid table closure/no-empty-below and arity behavior need their existing exact source conditions or a derivation from the actual constructor history. The unvalidated finite table and its interpreted language do not require that extra claim.

This next cut establishes a finite full-guard row view of the already verified bounded native result. It does not complete native operation/compiler correspondence, machine capacity, the full retained-heap language, earlier enumeration hooks, or whole Haskell equivalence. No defect or Haskell fix was established.

---

# Fixed arity cap through the same bounded copy

Frozen: 2026-11-12 11:16 CET. Read-only plan. The verified read-cap source stays unchanged.

The next cut is an observer of an already successful `SourceNativeBoundDepth.boundDepth` equation. It needs no new completion producer. Apply it to the ONE receipt returned by `SourceNativeBoundDepthMeaning.complete_exact:489` and append the resulting heap cap to that same packet.

## Proposed observer

Paths below are under `lean/MicroCFTA/`. `Heap` means the numerical `SourceNativeReadArityHeap.Heap`.

```lean
theorem boundDepth_observed_heap [DecidableEq (EdgeKey Symbol Guard)]
    (readerFuel : Nat) (depth : Int) (root : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before root) (closed : root.free = [])
    (heap : Heap bound before)
    {result : Value Symbol Guard} {after : State Symbol Guard}
    {memo : SourceNativeBoundDepth.Memo Symbol Guard}
    (actual : SourceNativeBoundDepth.boundDepth readerFuel depth root before =
      (.done result after, memo)) : Heap bound after
```

These are current input conditions plus the actual equation being observed. There is no future heap, cap, read, model, or success supplier. The observer works at any successful reader fuel. It does not require a separately supplied adequate cutoff.

## Private induction

Use height induction on the actual `atHeight` call. A local observer must retain `SemanticReady`, `Keeps`, available closed results, and live memo entries together with the numerical heap cap. These physical fields justify later reads and constructor calls at their exact intermediate heaps. They are not new public premises. A live memo entry means only that its current value is available and closed. The public `boundDepth` memo is empty, so initial liveness is vacuous. No semantic memo assignment is needed for the cap.

1. Empty input and height zero allocate nothing. The successful result equation fixes the same heap and memo. A raw reference cannot produce this successful result.
2. A memo hit allocates nothing. Current memo liveness supplies its returned value's availability and closedness for the parent. Do not perform a row read on a hit.
3. On a memo miss, inspect the SAME actual reader result from `interned:61` in `SourceNativeBoundDepth.lean`. Failure results contradict the observed success. Wrap the done equation as `SourceEqualityProjectionRead.Read.done`. `Read.verified:61` supplies physical effects. `SourceNativeReadArityHeap.read_arity_heap:376` retains the SAME `bound` at that returned heap and bounds every returned row. Filtering with `retained` gives membership in this exact original row list.
4. Observe the actual ordered `children:37` traversal. Split its two binds and apply the smaller-height observer to the actual head call. Start the tail at the returned head heap and memo. Carry the untouched original children with `Keeps.available`. Retain the successful output list and full endpoint equation. `SourceNativeBoundDepthChildArity.children_length:7` supplies its exact input/output length equality.
5. In `edges:48`, combine that equality with the original row's numerical cap. The subsequent `makeEdge` therefore receives at most `bound` children. Retain current child availability and closedness. `SourceEqualityRequiredCache.edge:53`, `SourceEqualityRequiredSemanticCache.edge:32`, and `MergedPhysicalGroupEdges.makeEdge_fields:27` supply the exact constructor effects and fields. Continue the remaining rows at this actual returned constructor heap. Cache growth retains their original residency. Do not call the recursive copier or a completion theorem again to obtain a convenient endpoint.
6. `makeNode copied` changes no edge records. `SourceEqualityRequiredCache.node:91` and `SourceEqualityRequiredSemanticCache.node:39` retain the physical conditions. The final memo put changes only the local memo. Its new value is available and closed at that exact heap; old entries remain live by growth. Heap arity is unchanged.

This proof can use a small private bind-success inversion and local memo-liveness lemmas. `SourceNativeBoundDepthMeaning` already contains the corresponding observation structure at `bind_done:235`, `children_observed:245`, `edges_observed:294`, `interned_observed:362`, and `worker_observed:451`. Those declarations and their semantic carriers are private. They are proof routes, not a public API. Do not invoke `complete` or `complete_exact` for recursive subcalls. The new observer derives the physical intermediate conditions while following actual equations; it does not reproduce cutoff selection or language preservation.

## Public constructor visibility

The exact numerical constructor facts are already strictly proved in `SourceNativeReadArityHeap`, but private:

- `edge_heap:38`: `Heap bound before` plus `children.length ≤ bound` gives `Heap bound (run (makeEdge symbol guard children) before).2`. It needs no coherence or guard-fit premise for this table property.
- `node_heap:51`: `makeNode` preserves `Heap bound` without an edge-count premise.

These are the only constructor-specific numerical facts needed. Exposing these exact existing statements would avoid repeating their small proofs. Their bodies need no change. The constructor field and readiness laws remain public and require their existing current invariants. There is no missing mathematical primitive here, only a visibility seam. The private read/unfold machinery need not become public.

This copier uses raw `makeEdge` after a same-length child scan and creates no new empty sentinel edge. It therefore preserves `bound` exactly. The `max bound 1` ceiling from intersection mismatch handling is not needed for this operation.

## Append to the existing completion packet

The proposed public producer has the SAME current header as `complete_exact`, with no added cap premise. Its exact result is:

```lean
∃ cutoff result after memo,
  (∀ fuel, cutoff ≤ fuel → SourceNativeBoundDepth.boundDepth fuel depth root before =
    (.done result after, memo)) ∧
  SemanticReady after ∧ Keeps before after ∧ Available after root ∧ root.free = [] ∧
  Available after result ∧ result.free = [] ∧
  (∀ key value, memo key = some value → Available after value ∧ value.free = []) ∧
  DeepOrdinary result ∧ MergedOrdinaryHeight.height result ≤ (depth + 1).toNat ∧
  (∀ holds ambient term, meaning holds ambient result term ↔
    meaning holds ambient root term ∧ (term.height : Int) ≤ depth + 1) ∧
  Heap (SourceRecursiveIntersectionSourceProfile.limits before).arity after
```

Call `complete_exact` ONCE and retain its entire tuple. Derive the initial numerical cap from `SourceNativeReadArityHeap.initial_heap:366` using the current semantic facts. Select the SAME actual success at `fuel := cutoff` from its stable equation. Apply the observer and append its result. No independent value, heap, memo, model, or cutoff is selected or aligned by language equality.

The added fact bounds every physical edge record in this returned heap before guard evaluation. It does not bound allocation count, row count, payload mass, total runtime work, later arbitrary operations, all prior siblings, or whole enumeration. The existing `cutoff` remains a reader-fuel threshold for this bounded copy.

## Source commits

- SourceSynthesisDuplicateQueryAcceptance: 37a338ce356b181f8143b0c347bb281711699b42.
- SourceNativeReadArityHeap: cff0aa8dc2c56f589da4f1445e2bf93b8280b727.
- SourceNativeBoundDepthMeaning: 377ce2cc7162e18db383f2846146bdf060cf967a.
- Haskell duplicate query reproduction: 6630241dc01dbf61df87c36d76f54a12ac623f3a.
