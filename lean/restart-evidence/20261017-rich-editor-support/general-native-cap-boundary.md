# General native cap boundary

Reviewed 2026-10-17 03:02 CEST. This is a bounded source review and an evidence prototype. No production source changed.

The next missing producer is a mixed positive-cap native result law at the exact actual return. Existing hereditary native laws cover both annotated operands. They do not yet prove this mixed law. No counterexample to general cap preservation or new Haskell defect was established.

## Source order and the binder boundary

`cfta/src/Data/CFTA/Interned/Operations.hs:484-548` checks empty, reset, closed self, operand order, and repeated numeric pair before exposing Mu, union, or references. `IntersectId` sorts the two node identities (`Interned/Type.hs:150-155`). `SourceRecursiveIntersectionControl.pair` and `decision` preserve this order. The pair does not include constructor tags. An ordinary operand and a bound reference can therefore select the same pair as the earlier ordinary/Mu call.

`SourceRecursiveIntersectionCompile.compileMu` enters the actual Mu bindings and the pair, queries the actual bodies, and applies optional binding to the returned body. The corresponding Haskell `maybeMu` tests whether its pair name is free in that body. A positive test invokes the bidirectional `Mu` constructor. It does not imply that the final result retains a Mu.

The actual constructor normalizes every callback before both probes and before its final body. `Interned/Type.hs:735-753` removes the callback's own **direct root-union member**. It does not remove references below ordinary children. In the model, `SourceRecursiveIntersectionMaybeMu.callback` performs actual stored substitution, then `withoutSelfReference`. `callback_eq` and `construct_eq` connect that operation to the lexical constructor schedule. `request true` subsequently applies `cleanup`: an unused binder returns its body; a bare self-cycle returns Empty. Constructor allocations from discarded probes remain in the returned heap.

`SourceRecursiveIntersectionMaybeMuFreeSupport.pair_absent` proves that the selected pair is absent from the **returned** value's free names. It does not prove absence in the incoming body, or that optional binding skipped its constructor path.

## Checked prototype

`general-native-cap-pair-probe.lean` imports the current constructor, compiler, and Cap modules. Its guard-independent branch tests use `Symbol = Nat`, `Guard = Bool`, and the predicate `guard = true`. This is a test of the shared control and constructor algorithm. It is not a test of the concrete equality allocator or GHC execution.

The final imported log is `general-native-cap-pair-probe-12.log`: exit 0, four full axiom/signature pairs, no warnings, errors, `sorryAx`, or truncated output. All failed attempts and exact draft sources remain separate. The proof uses kernel reduction for closed Boolean observations. The axiom lists contain only `propext` and `Quot.sound`.

1. `constructed_loop` builds the literal source expression `binder false (var 0)` from the empty constructor heap. It returns the actual raw Mu record with identity 0 and its exact heap.
2. `constructed_ordinary` builds a bad-guard nullary ordinary record in that same returned heap. Its node identity is 1. It is closed, satisfies `Cap P 1`, and is not hereditary `Annotated P`.
3. `mixed_pair_repeats` verifies that the first branch is `rightMu`. After literal domain extension, querying the unchanged ordinary operand against the Mu's bound reference selects the **same numeric repeated pair**. Thus a blanket pair-absence claim is false even for these actual source-built operands. The cutoff value is a reference and is hereditary. This is not a cap counterexample. This pair test checks the exact selector and domain extension, rather than constructing a whole native query trace.
4. `normalized_direct_union` executes the actual smart source construction of `binder true (union [var 0, bad ordinary])`. It returns the exact existing ordinary canonical record. The final node counter is 6, so the theorem also retains the discarded probe/body allocation effects. Direct self-union recurrence can therefore disappear during callback normalization and smart cleanup even when the retained ordinary branch is nonhereditary. This theorem executes the shared lexical callback schedule. It does not supply a native intersection body trace for that expression.

## Smallest useful next theorem

Keep the existing exact physical trace, scope, and Mu-store requirements. Add a causal returned-cell cap certificate, and produce it from the actual compiler body before installing a finish. A candidate node law is:

```text
forall depth,
  Bindings P source request.domain.key ->
  Cap P depth request.left -> Cap P depth request.right ->
  Cap P depth actualResult
```

The edge law uses `SourceCurrentConstrainedCap.Edge P depth`. A mixed `Cap P depth` operand and a hereditary operand then instantiate this law at the same depth. This proposed law is not yet proved. It also needs the concrete plain-conjoin closure at depth zero; an arbitrary guard predicate is insufficient there.

The proof must classify actual occurrences of the current pair, together with the normalized callback. A useful proposed invariant records that recurrence before consuming a constrained ordinary layer can occur as a removable direct union/self reference; recurrence retained below an ordinary layer must have hereditary body scope. It must exclude a retained pair occurrence below a nonhereditary ordinary layer at this binder. The domain's set of seen numeric pairs alone does not state this distinction. The bound must decrease when an actual ordinary child is selected. A union keeps the bound. Enter/read steps must retain actual annotated Mu bindings and original source readback.

This is a simultaneous compiler/request occurrence proof. A callback postcondition that simply assumes the desired cap, a future completed body law, or a set of future requests would leave the obligation open. Existing `physical_child_requiredFuel` gives a completion-based induction measure. It does not establish this occurrence invariant. It must not be cited as a cap theorem.

## Exact current reusable contracts

- `SourceCurrentConstrainedCap.Cap` and its `node_child`, `edge_mono`, `makeNode`, `makeEdge`, and `makeUnion` laws already close ordinary and union constructor cases. A Mu has a cap only through hereditary annotation.
- `SourceCurrentHereditaryNativeScope.Bindings.enter/read` retains local annotated Mu payloads at actual source bindings. It permits unrelated constrained records in the heap.
- `SourceCurrentHereditaryNativeEffectsCompile.node_certified` currently requires both operands to be annotated. Its Mu case uses `Construction.optionalBinder`, which also requires the actual incoming body annotation.
- `SourceCurrentHereditaryNativeCode.NodeLaw` has the same both-hereditary antecedent. The antecedent is false on a mixed nonhereditary operand. `NativeUniversalStore.Stored` therefore does not, by itself, constrain a pre-existing warm mixed result by a cap law. A new cap law must be installed causally at fresh finishes and read back at the exact stored owner, or a cold proof must derive it jointly during its actual execution. It cannot be obtained by rebasing the old conditional annotation law.
- `SourceCurrentHereditaryTargetQuery.step/receipt` already retain the full admitted actual return and causal native/Mu stores for **both-hereditary** inputs. The current rich editor/class proof uses initial hereditary leaf placement to satisfy that premise.

The current source refusal gate also permits finite ordinary nonhereditary endpoints. The rich editor leaf-placement family is thus an intermediate supported family. General approved-class closure, mixed-cap native preservation, whole-library completion, and GHC lazy/pending execution correspondence remain separate open obligations. This review changes no source refusal rule or payload semantics.
