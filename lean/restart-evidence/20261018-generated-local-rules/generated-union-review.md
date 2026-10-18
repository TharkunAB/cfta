# Actual union and self-filter literal inclusion

Frozen on 2026-10-18. Source: `SourceCurrentGeneratedUnionCases.lean`, SHA256 `aa894cb760a5b7efb193dc49fee1eb322ac3b8e38cc59be145dfd6c76df69b47`.

## Proven source laws

`execute_below` preserves exact literal inclusion through two actual warm stored calls at one Ready reader under the same environment. `StoredLiteralExecutionParts.parts` gives each returned literal atom an actual original-atom call. It gives each returned row an atom call or a surviving full original-row call. Raw inclusion transfers that same witness to the second parent. Thus the theorem assumes neither a desired relation between the outputs nor a recursive child result law.

`filter_below` preserves inclusion through the two literal self filters. Its exact retention premise is `member != reference own OR parent = reference own`. A bare-self member keeps itself when filtered alone. A larger parent union removes that atom. The premise preserves this exception. Full ordinary rows survive both filters. Mu values remain complete opaque literal atoms. No binder or closedness restriction is present.

`retained_member` begins with actual available union inputs, selected member membership, an actual warm `makeUnion`, both actual warm filters, and both actual warm stored calls. It derives parent and filtered-value availability from actual constructor facts. It obtains raw inclusion from `SourceDirectedCases.union_member`, then applies the two laws above. Its conclusion is `Below left right`: exact literal atom and full row inclusion. It does not infer physical Empty agreement or all finite observation equality.

These one-sided laws do not change the cross-assignment aliases or self-tests in `RetainedMuDirectedCase.Generated`. They make no claim about removing those premises. They do not construct a Generated pair or prove Directed for the whole generated relation.

## Checked warm subgroup boundary

`GeneratedUnionKernels.warm_parent_cold_subgroup` constructs one actual closed source from the empty heap:

`binder false (union [union [var 0, leaf 0, leaf 1], leaf 2])`.

The source creates a Ready reader. Building the inner union with actual Depth reference is warm there. The parent union and its Depth filter are also warm. The fixture invokes `retained_member` on leaf 0 and derives its literal inclusion in the actual parent-filtered ordinary value. Both stored calls use the same empty map and are literal warm calls.

Nevertheless, filtering the inner union at that reader strictly increases `nodes.next`. The child filter must create the ordinary node for leaves 0 and 1. The parent filter used only the larger ordinary node for leaves 0, 1, and 2. Hence actual warm parent filtering does not entail warmth of this exact child filter, even at this source-built Ready heap. The theorem is a proof-contract boundary. It does not refute Generated membership through some other witness, a general semantic simulation, or Haskell correctness.

The fixture keeps the literal construction, reader, child-build equation, union/filter equations, actual stored calls, inclusion proof, and strict allocation inequality. A private kernel-checked witness and the public theorem have identical statements. The full public probe prints the exact alias.

## Validation

Production strict `generated-union-direct-1` passes with a literal zero-byte log. Canonical `generated-union-canonical-1` passes 609 jobs without warnings. Public `generated-union-public-1` contains all three full declaration/proof/axiom reports and passes the hardened checker.

Constructed strict `generated-union-kernels-1` passes with a literal zero-byte log. Constructed full group `generated-union-kernels-public-1` passes one complete report. All selected groups use the eight required print options and report only standard axioms. Every Lean job has verified memory.max = memory.high = 4294967296 and memory.swap.max = 0, with a five-minute cap and Lean 4.34.1. All first attempts pass. No attempts were discarded.

This component adds three public theorems and one constructed theorem, with no auxiliary pair. It edits no prior module or evidence. Its manifest excludes root mutable helpers, selections, fixtures, reports, and peaks.

## Remaining source-generation obligation

A source-union case for Generated still needs a decomposition that does not invent warm normalization of every source subgroup. One route must retain literal fragments of actual normalization and compose them with a supported generator relation. The exact bare-self retention condition must be transported across the existing aliases and self-tests. The current results supply the actual literal inclusion steps but do not assert that this route is complete.
