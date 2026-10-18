# Open selected native row integration

Frozen at 2026-10-18 10:28 CEST. This component contains one constructed proof. It changes no production source.

## Actual source and execution

`MicroCFTA.NativeOpenRowCheck.open_selected_row` builds the recursive source `mu x. (leaf | f[x])` and the ordinary source `f[leaf]`. The source constructor and original-field allocation derive initial physical `Ready`, native `Good`, source availability, and publication history. The actual closed outer query completes with the complete value `f[leaf]`.

The query enters the actual Mu binding domain. Both the self-reference versus leaf request and its canonical leaf versus self-reference request have actual returned cells for the nonempty ordinary leaf. The proof retains the entered domain, the bound name, the initial physical read, the swap and right-reference decisions, the selected physical leaf row at index zero, its complete guard, and its zero arity. It applies the reference writer producer to the actual returned cell. That producer retains the captured checked states, actual reference read, ordered child trace, and forwarding to the final reader. The existential complete value read at that captured state is retained as the actual read result; the statement does not identify it with a separate earlier complete value.

The proof also applies open forwarding normalization with computed codec witnesses. It retains the exact route, terminal returned cell, complete `Written` evidence, and the terminal branch exclusions.

## Actual open classifier call

The selected request has a nonempty free-name list. At the complete final reader, the proof derives its native input facts from the computed returned cell and final `Good`. It computes `KeySafe` from the numeric key bounds. It then proves the literal one-step checked warm trace and the corresponding `execute 2` equation. Both return the positive ordinary leaf at the same complete checked state.

`NativeOpenQueryRowOrigins.request` consumes that actual open warm trace, the causally derived native and publication histories, and the physical selected row. It derives `Resolved` at the same checked state. The call has no closedness, `Original`, `BinderFree`, finite-cap, or external codec input. The codec witnesses in the separate normalization call are not inputs to this request producer.

The closed-domain admission theorem is used only to derive the original closed outer trace. The final classifier call is explicitly open. This integration exercises the reference terminal branch and an earlier actual writer. It does not prove initial query-operand row ancestry, general native or outer completion, or general retained-used Mu correspondence.

## Selected validation

- Strict source: `open-row-kernels-direct-5.source.lean`, SHA256 `1a0ffac3f737b91c515ef3113bf5188cfad86ac3b472eb1c94960dade6d2ac0f`.
- Strict raw log: `open-row-kernels-direct-5.log`, terminal zero, actual zero bytes.
- Full selected group: `open-row-kernels-public-1`, one constructed pair, zero production pairs, zero auxiliary pairs.
- Full source SHA256: `d90d818859657a94a30c8ecc40f404cbb6fc0f1938f1c957594221a9ea5c39ec`.
- All eight explicit options, `#check @`, full proof print, and axiom print are present. The output has no omissions, printer failures, warnings, errors, or `sorryAx`. Its axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.
- Every selected Lean invocation uses pinned Lean 4.34.1, a five-minute cap, and effective cgroup values `memory.max=4294967296`, `memory.high=4294967296`, `memory.swap.max=0` read inside the worker.
- Four earlier prefix attempts passed with zero-byte raw logs. Every numbered snapshot and result remains immutable. No failed attempt occurred.

This evidence-only component has no independent canonical production target. The production owners supply canonical build receipts. The manifest pins their final source bytes and this component's own files. It does not pin mutable root evidence or count other components' probes.

## Main final production pins

- `SourceCurrentNativeOpenQueryRowOrigins.lean`: `2afdaa7eb4288cd9526ee3c8bf0c71490e2148d6ad0d4bf287172a02b8ac3e7c`.
- `SourceCurrentNativeRowKeyable.lean`: `28f4ebdc51a5e122043b955a14f7313823b91d1f35418a0da4873f7bce452e54`.
- `SourceCurrentNativeOpenRequestResults.lean`: `c6867dcc4d58b33cbf27a6df96b08401e969e2e5a27da326fe7a635d3baecd51`.
- `SourceCurrentNativeOpenQueryForwarding.lean`: `dd863d7d5e1e483c1b916dc076ed9a05d33016ae50ac3d30a87f6b758c18a8d7`.
