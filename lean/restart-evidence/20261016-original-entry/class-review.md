# Original entry and prepared native history review

Reviewed 2026-10-16 06:43 CEST. This review read the current source only.
It did not build or edit the reviewed modules. No material defect was
found in the stated completed resident-model scope.

## Derived entry invariants

`SourceCurrentAllocatedNativeOriginalHistory` derives literal `Cached`
checks from the checks recorded in actual `History.construct` events
(lines 60–80). Its separate structural induction derives `SyntaxValid`
for the complete covered syntax (18–58, 82–89). It does not assume a
desired final field heap. Literal normalization remains a fact carried by
the History events; this is not a proof of an arbitrary frontend's
normalization or a theorem from a constructor equality alone.

`History.fields` (92–112) derives both normalized annotations and earlier
allocation origins through the actual original constructor run. For each
resident edge, `Origin.load` then supplies successful read-only lookup in
the same final interner. There is no allocation fallback at the lookup
site. The literal original guard is preserved by the allocated readback.

`OriginalHistory.constructed` (126–149) derives physical `Good`,
`SemanticReady`, root availability, closedness, and Original syntax. It
uses actual constructor facts, actual source-free metadata, the history's
operation validity, and its derived loaded fields. It assumes neither a
final native invariant nor a semantic query result. The initial machine
uses the exact constructed heap and an empty domain interner; native
request tables are initialized cold.

## Whole query integration

`ConstructedHistory.query_complete` derives every query operand's Original
syntax from the common heap's coherence plus the stated availability and
closedness (lines 43–48). It then invokes `ColdHistoryExact` on that same
heap and operation state. Its fixed model is derived for the full finite
operand list. It takes no model, model-validity callback, Contextual cache,
Scoped cache, per-query future-success callback, or desired result law.
The query operands must still be available and closed in this initial
constructed heap. This is not automatic admission of arbitrary later
generated values or operands from another source model.

`PreparedHistory.query_complete` derives its actual serial preparation
receipt and History with `prepare_complete`. The equality interner in its
query state is literally `(prepare literals initialCache).2`. The
`sameCache` equality comes from the actual preparation receipt (47–59).
It aligns both the range plan and returned query receipt to that exact
cache. It does not replace the returned cache with an unrelated valid
cache or require a supplied completed preparation.

The prepared wrapper still needs `Cached` for each literal raw payload,
actual original construction, current query operand availability and
closedness, a valid initial interner, and the actual whole-walk machine
range plan. These are explicit input conditions. The machine range plan
asks key checks along actual yielded prefixes; it asserts no successful
body or semantic answer.

## Preparation order, duplicates, and empty inputs

`SourceEqualityOriginalAllocationPreparation.prepare` (19–27) passes the
head constructor's returned interner into the suffix. A failed head
returns immediately. A failed suffix retains all earlier allocations and
its exact error. The completed list preserves source list order and
multiplicity via `All₂`, while every field receipt is transported to the
same final interner. The empty list returns the identical interner and
empty values. Duplicate literal fields require no distinctness premise;
interner hits may reuse the earlier identity.

The chosen literal list is `ConstraintOrigins.guards expression`. That
list includes each complete edge guard and the guards in all nested
children and stored binder bodies. It can include a guard that a later
smart constructor discards. It is a finite covered preparation schedule,
not a theorem that GHC demands every original guard or demands it in that
preorder. `History` also permits intervening atomic interner operations;
the serial `prepare` schedule is one concrete history.

## Initial operation tables and source boundary

All these endpoints use `MemoAllocation.initial finalCache`. It keeps the
whole final equality interner and initializes the modeled completed
combine/descent tables empty. `History.operations_valid` proves validity
of this cold projection. It does not prove validity of arbitrary warm
side tables or that production clears global caches. The PreparedHistory
header explicitly states this distinction. A literal runtime transfer
still needs the GHC demand/publication and concrete memo/interner bridges.

`Constraint.hs:129–135` implements the own equality accessor and its
stored-value shortcuts. `Equality/Operations.hs:160–168` passes that own
accessor and inherited payload into the child reduction while retaining
the original whole constraint on the rebuilt edge. Its precheck guard
order is physical both-empty, combined contradiction, refused-class
query, then required/narrowed children (206–240). The completed accessor
and precheck model retains actual allocations in that order. It does not
prove eager child-spine or original-field forcing in Haskell.

The separate new `SourceCurrentClassHistoryEntry` has a further explicit
boundary: its completed Scan is the historical native-intersection
decision graph. Current `Enumeration.hs:588–640` computes conjunction
tuples, requirements, a budgeted table, and a fixed point. The new class
adapter does not equate these two Boolean executions or heaps and does
not prove general class or constrained outer-caller completion. Its
conditional accepted-edge theorem is sound for the displayed graph.

## Reviewed source hashes

```
e15c43f3681aefaf0fce08d8ee8c579f537606a1002ae5361feeb0b8a8ff14d1  SourceCurrentAllocatedNativeOriginalHistory.lean
4aedd49089e2cb3c14ac382298636c788a6088568fb3ffce87d4028dce4f46a8  SourceCurrentAllocatedNativeConstructedHistory.lean
d435f96abd437841640a6b9ff40d2e64b324a125b7b35c176e6e966494ee96b8  SourceCurrentAllocatedNativePreparedHistory.lean
008c7078519b784c196aa241608e2eec4eb883b7648943fde0b89cd560d78727  SourceEqualityOriginalAllocationPreparation.lean
4524cb46bf8349a97c9c396a899075c33405499794d98ab2334f3ae0fcb3fccf  SourceCurrentClassHistoryEntry.lean
```

The root owns build and probe evidence for the first four modules. This
review adds no compilation result. The separate `class-validation.md`
records this task's focused build and probes for its owned class adapter.
