# Whole enumerate-until model: source review and declaration schema

Source-only review at 2026-10-24 01:01 CEST. Repository HEAD is `790c39ce21f0be612fafcb6a36eb972ac5bf03f9`; imported main is `6b62b4afefca80bb05f5a37546212a99980aa3df`. H39 remains queued. No proof, compiler, prepared program, repository edit, Git mutation, network, or board operation was performed.

Recommendation: add one model module using the existing `EnumerationState.State`, `Graph`, `EnumerateM`, `Fragment`, `Suspended`, and `Oracle`. Include parameterized slot expansion, both shallow helpers, the complete until loop, and its partial-result wrapper. Keep every existing definition and theorem unchanged. The first model can retain the existing modeled scheduler for an exact additive bridge. That choice must be named: it does not yet give literal final-forest correspondence with the current Haskell cached scheduler.

## Read scope and identities

The complete relevant Haskell functions were read, including slot writes, allocation, ancestry, eager and shallow preparation, indexed selection, parameterized slot expansion, the whole driver, and partial rendering. The complete Lean state/execution definitions through `runs` were read. The index/selection and driver interfaces below were read with their stated conclusions. This is a bounded source/API review, not a manual read of every proof in their import closure.

Full-file identities and 25 exact byte-range identities are retained in `/tmp/mcfta-enumerate-until-20261024-source-cuts.json` (11 source files; SHA256 `16177ec806ac6fbd260a2cf3bc91017ab15bb634e4e90d0e11d95fc2621e7be9`). Ranges use inclusive source line numbers and retain the original bytes and line endings when hashed.

| Source | Relevant ranges |
| --- | --- |
| `cfta/src/Data/CFTA/Enumeration.hs` | 156–178; 184–475; 480–530; 658–709; 711–801; 807–1006; 1012–1046; 1154–1193 |
| `cfta/src/Data/CFTA/Interned/Type.hs` | 572–611 |
| `cfta/src/Data/CFTA/Internal/UnionFind.hs` | 111–137 |
| `lean/MicroCFTA/EnumerationState.lean` | 1–391; 393–451; 568–591 |
| `lean/MicroCFTA/EnumerationExpandableIndex.lean` | 1–112 |
| `lean/MicroCFTA/EnumerationWaitingIndex.lean` | 1–56; 93–108; 128–152 |
| `lean/MicroCFTA/EnumerationIndexSelection.lean` | 1–230 |
| `lean/MicroCFTA/EnumerationSchedule.lean` | 99–180 |
| `lean/MicroCFTA/EnumerationDriver.lean` | 396–441; 486–514; 565–578 |
| `lean/MicroCFTA/EnumerationCorrectness.lean` | 36–78 |
| `lean/MicroCFTA/EqualityTrie.lean` | 40–54; 617–640 |

The Haskell enumeration file SHA256 is `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07`. The existing Lean state file SHA256 is `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4`.

## Exact stop and scheduling behavior

The stop test uses `_expandableUVars`, before subtracting `_waitingUVars` keys. It checks all candidate slots, including blocked ones. It does not check only the ready list from `findExpandableUVars`. It also requires a nonempty candidate set. These distinctions are observable:

| Candidate slots | Ready slots | Rule on candidates | Required result before expansion |
| --- | --- | --- | --- |
| empty | empty | vacuously all true | Normal completion: `none`, not early-stop `some state` |
| nonempty | empty | all true | Early stop succeeds before the stuck check |
| nonempty | empty | at least one false | Scheduling reports stuck; reject the branch |
| nonempty | a proper subset | true only on ready slots | Continue; do not stop |

Pure equality slots, eliminated slots, and unconstrained recursive boundaries are excluded by the candidate predicate. An ordinary empty node is still a candidate. An always-true rule can therefore stop on an empty root and return a speculative hole. No validity, acceptance, or extendibility premise belongs in the operational definition.

On `some rule`, perform this test on the state at entry, before scheduler lookups or oracle calls. On `none`, omit the test. On normal completion return `none`; on early stop return `some oracleState`. Repeated-recursion truncation, pre-oracle rejection, post-oracle rejection, and stuck scheduling keep their distinct branches. Branch-local caller state must pass from the pre-oracle to the post-oracle and then to the recursive iteration.

## Whole expansion behavior

`enumerateOutUVarWith` is not just a call to an expander. It reads the selected representative slot, resolves the representative again, reads its stored ancestry, and sets `expansionAncestry`. A recursive boundary adds the key of the original node and original suspended tries. It then unfolds a Mu or materializes the outer edges of an InternedUnion before invoking the supplied expander. After success it clears `expansionAncestry` to empty, writes the produced fragment to the previously captured representative, and returns it. Do not restore an earlier expansion ancestry or resolve the destination again after the callback.

Both Mu and InternedUnion satisfy source `recursiveBoundary` (`Interned/Type.hs:608-611`). The existing graph view has one `.recursive body` case. Its realization must explicitly cover both boundary forms, with `body` denoting the correct ordinary outer expansion for that identity. It must not treat an InternedUnion as an ordinary node or an unresolved reference. The original boundary ID remains in recursion keys. If separate Mu-versus-union tags are required later, introduce an additive realization interface; do not change the existing `Node` constructors now.

`enumerateEdgeWith` must retain the inherited-path arity test, allocate one pure UVar for each edge equality class, descend inherited constraints before new constraints, prepare every child in source order, and prepend the residual obligation with the resulting fragment. Reuse `arityAllows`, `suspend`, and `descendScs`; do not replace equality handling with a new predicate. The existing arity equivalence requires valid tries (`EnumerationState.arityAllows_maximum`).

`enumerateShallowHere` and `prepareShallowChild` have different roles. Their exact matrix is:

| Input | Selected-root helper | Child helper |
| --- | --- | --- |
| Ordinary nonempty node; no terminal suspended trie | Choose one edge and use the shallow child preparer | Allocate `some node`, then raw-write the full original `scs`, and return its hole |
| Ordinary node with a terminal suspended trie | Existing eager `enumerateNode` | Existing eager `enumerateNode` |
| Empty, recursive boundary, or unresolved reference | Existing eager `enumerateNode` | Existing eager `enumerateNode` |

The child allocation inherits current expansion ancestry before its constraints are installed. The raw write must update the maintained waiting counts in a cache realization. The selected root must not be deferred into another fresh ordinary slot. Fallback means the existing eager function literally, including its current recursive-boundary behavior; do not claim that every fallback allocation stores arbitrary inherited `scs` when the eager implementation does not do so.

## Narrowing and writes

Use graph IDs as node identities. `narrow oracleState uv node` therefore has type `OracleState → Nat → Nat → Nat`. Do not use equality of graph views as the same-node test.

After the selected slot read and the repeated-recursion check: compute the narrowed ID; reject if its view is empty; if its ID equals the original ID, perform no extra representative lookup and no slot write. Otherwise resolve the representative and raw-write `.unenumerated (some narrowed) scs`, with exactly the original suspended list. Do not merge or intersect the replacement, clear its constraints, allocate a new slot, or inherit ancestry again. Then call the pre-oracle with the narrowed ID. The slot expander rereads the actual slot after the oracle, as the source does.

The repeated-recursion branch precedes narrowing. A repeated key clears only the selected slot's suspended list, keeps its node, and recurses with the same caller state. It calls neither oracle and does not apply narrowing. `EnumerationDriver.checkRepeated` already represents this operation for the existing graph view.

## Minimal proposed declaration schema

Names and argument order below are proposals for an exact declaration gate. They are not an accepted declaration package or a proof draft. A suitable additive namespace is `MicroCFTA.EnumerationUntil`.

```
NodeExpansion Symbol Guard :=
  List Suspended → Nat → EnumerateM Symbol Guard (Fragment Symbol)

enumerateEdgeWith
  (prepareAt : Nat → NodeExpansion Symbol Guard)
  (fuel : Nat) (scs : List Suspended) (edge : EnumerationState.Edge Symbol Guard)
  : EnumerateM Symbol Guard (Fragment Symbol)

prepareShallowChild (graph : Graph Symbol Guard) (fuel : Nat)
  : NodeExpansion Symbol Guard

enumerateShallowHere (graph : Graph Symbol Guard) (fuel : Nat)
  : NodeExpansion Symbol Guard

enumerateOutWith (graph : Graph Symbol Guard)
  (expandNode : NodeExpansion Symbol Guard) (fuel uv : Nat)
  : EnumerateM Symbol Guard (Fragment Symbol)

candidateSlots (graph : Graph Symbol Guard) (state : State Symbol Guard)
  : List Nat

enumerateUntil (graph : Graph Symbol Guard)
  (stop : Option (OracleState → Nat → Bool))
  (narrow : OracleState → Nat → Nat → Nat)
  (expandAt : Nat → NodeExpansion Symbol Guard)
  (order : OracleState → List Nat → Option Nat)
  (oracle : Oracle Symbol Guard OracleState)
  (fuel : Nat) (oracleState : OracleState)
  : EnumerateM Symbol Guard (Option OracleState)

rootFragment (fuel : Nat)
  : EnumerateM Symbol Guard (Fragment Symbol)

partialRunsUntil (...same driver parameters...) (fuel root : Nat)
  : List (Except Error
      (Term (PartialSymbol Symbol) × State Symbol Guard))
```

`candidateSlots` is the increasing raw-slot scan filtered by the existing `candidate graph`; it does not resolve representatives or subtract blocked references. The index invariant relates this list to the source cached set. A slot scan is used here because the existing core state has no stored index fields.

`expandAt` must be fuel-indexed. In an iteration with positive budget `k`, call `enumerateOutWith graph (expandAt k) k uv`, then recurse at `k-1` with the same policy. Eager specialization is `expandAt k = enumerateNode graph k`. This preserves the old modeled caller's exact policy: `enumerateOut graph k` reads representatives with `k+1` and calls the eager node action at `k`. A fixed callback closure retained across recursion would not give that same-fuel bridge.

Root's later exact convention gives the edge helper an explicit fuel counter. At positive edge bound `k`, the callback is `prepareAt (k-1)`; bound zero reports `.fuelExhausted`. This is exactly the old edge's positive-fuel decrease. The selected ordinary shallow node also descends to the predecessor edge bound. The shallow helpers use their current positive bound for eager fallback and report an explicit error at zero. They need not invent a new mutual recursion: child preparation falls back to the old eager function, not to the new shallow root helper. Driver fuel zero remains an explicit `.fuelExhausted` error under the established model convention, not an empty result or an early-stop success. This is a finite observation bound, not a new Haskell outcome. The no-stop branch omits the state read for the stop test.

`rootFragment` reads actual UVar zero with `getValue`, returns its stored fragment if enumerated, and otherwise returns `.hole 0`. It must retain the original hole ID. The public partial wrapper starts with `initial root`, discards the until status as Haskell does, reads this root fragment, and uses existing `expandPartial`. It does not render or discharge residual obligations. The model retains the actual state and explicit errors in its result rows; a public term-only projection can be defined separately.

Direct imports can be `MicroCFTA.EnumerationDriver` and `MicroCFTA.EnumerationIndexSelection`. They expose the existing state, graph, trie, scheduler, cache, repeated-key, and success interfaces. Follow the established local `Monad List` convention. No new state, graph, heap, acceptance oracle, or general framework is needed. Existing `setValue`, `allocate`, `getValue`, `representative`, `expandPartial`, and all old drivers remain unchanged.

## Exact cached-state boundary and assumptions

The current Haskell scheduler is a pure cached-set subtraction (`827-834`). The old Lean `findExpandable` scans suspended references and path-compresses them. `EnumerationIndexSelection.selection_exact` and `reachable_selection` prove equal offered results and preserved canonical Roots; they do not prove equal representative forests or equal full final states. A parent chain resolved by the old scan can become shorter while the source cached lookup leaves that chain intact. A later observing oracle can inspect this difference in the model.

Therefore use the existing `findExpandable` explicitly for the first additive core model and same-modeled-scheduler bridge. Do not call that bridge literal equality with the current Haskell cached implementation. If exact current Haskell core-state equality is required in this component, it additionally needs a read-only selector on the same `State`, derived from candidate slots and representative meanings, plus a cache realization proof. Such a selector must discard compression effects rather than call the old mutating scan. This is a real scope decision before declaration authoring, not an assumption that the current index theorem has already closed it.

For a source cache realization, require the actual expandable-set invariant, waiting-reference support by canonical representative, allocated-domain alignment, and the ordinary slot/representative validity needed by existing actions. `EnumerationExpandableIndex.Correct` and `Reachable.correct` provide existing raw-slot count/index results; source writes count canonical representatives, while that raw waiting model is related by `IndexSelection`. They are not a complete automatic lift of every source union, arbitrary oracle action, or full new driver into a cached monad. The shallow write and narrowed replacement must be attached to those actual updates.

No semantic premise is required merely to define the operational actions. A later safety theorem needs preservation conditions on an arbitrary expander/oracle; `Ready` protects the captured raw destination before the final write. A later language theorem needs intersection correctness and explicit caller narrowing/rejection conditions. It must not assume a partial hole has an accepted completion. No narrowing idempotence, successful-run, final-certificate, or empty-source assumption should be added to the executable model.

The graph realization must cover IDs produced by narrowing and intersection, preserve actual ordered edges (`_edgesOf`, including canonical fallback for newly built nodes), and identify both outer-boundary forms. Existing abstractions of interning, integer capacity, unresolved-reference errors, and constrained-recursion emptiness checking remain explicit source-refinement boundaries. This investigation does not close them or change their old theorems.

An honest first source-only size estimate is about 140–190 ordinary lines for these additive definitions and the partial wrapper, excluding proof bodies and a new cached-selector realization. Exact header/local inventories and a hard cap require a separate declaration gate. The old-driver bridge and all kernel checks remain separate future work.
