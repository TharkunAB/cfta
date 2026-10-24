# Independent review of partial-render transport version 3

Status: CLEAR. Reviewed 2026-10-24 at 02:33 CEST. I read the complete 155-line candidate, its original self-review, all predecessor deltas, both failed raw logs, and the successful third check's source, report, receipt, limits, and usage record. I did not run a compiler or change a repository file.

Selected source: `/tmp/mcfta-partial-congruence-20261024-transport-3.lean.txt`, SHA `cfb86bcdf59c125625bb78f0fea7da467789adc162f27c4f1a4e45f630b5674c`. The saved `transport-check-3/checked.lean` has the same bytes and hash. The saved report records exit 0 with an empty raw log, `warningAsError=true`, and `linter.all=true`. The outer capped receipt records exit 0; effective memory.max/high are 4294967296 and swap.max is zero. These are Root's actual check records, not a new run by this reviewer.

I authored the separate paired-congruence candidate and part of the imported observation/frame foundation. I did not author this transport candidate or Root's two repair deltas. This review covers the transport construction and its use of those APIs; it is not an independent reproof of my imported foundation. The transport proof does not invoke paired partial congruence.

The sole public statement has one actual left render as its execution premise. It constructs `rightFuel`, `rightAfter`, an actual successful right render of the same partial term, and the complete `Frame leftAfter rightAfter`. There is no right-success, desired-output, Safe, Finished, semantic acceptance, readable-slot, or completion oracle premise. The source render's fuel decreases at each recursive call.

In the node branch, the local list induction constructs every right child and its actual intermediate state in source order. It constructs the tail from that state. The common child bound is `firstFuel + restFuel`: the head is raised by `restFuel`, and the entire tail traversal is raised by `firstFuel` with `retains_mapM`. Both fuel extensions retain the exact already constructed final states. The empty traversal uses zero without calling a zero-fuel child; its enclosing node uses a positive bound. Child order and multiplicity remain exact.

In the enumerated-hole branch, `getValue_transport` constructs the real matching right read before the recursive render is constructed. The outer bound is `readFuel + tailFuel + 1`. The read is raised to that complete outer bound. The recursive render is raised to its predecessor, using associativity and commutativity of addition. The constructed read's right final state is exactly the recursive render's right input. Totality at the left continuation follows from its actual read frame.

Each terminal hole branch uses `readFuel + 1`, an actual extended right read, and a pure result. Pending nodes with absent node IDs or nonempty suspended constraints retain the original queried hole ID. Eliminated slots also retain that ID after a successful value read. Only a recursive graph view with empty suspended constraints produces truncation. No representative ID replaces a visible hole label. Missing slots are not invented.

The final relation is always the complete installed frame, including both ancestry fields and exact root/size paths. The proof makes no literal final-forest equality, equal-fuel transport, error equality, resource bound, or unconditional partial-render termination claim.

The predecessor sequence is preserved and accurately explained:

- The 137-line pre-lawful draft gained the existing 17-line named List law instance, yielding the 154-line original. Its self-review remains unchanged.
- Check 1 failed with two names removed by preceding `rfl` eliminations and two ambiguous dotted `.node` uses. Version 2 changes only `leftLast` to the surviving `leftAfter` in the tail call and `leftMiddle` to `leftAfter` in the node traversal call. These are the same states after the actual pure-success equalities.
- Check 2 failed only on the two ambiguous dotted constructor uses. Version 3 qualifies `Term.node` and `PartialSymbol.concrete` in that change expression. It adds one rendered line and changes no statement, state, branch, bound, or execution.
- Check 3 passes on the exact selected source. No failure or repair is hidden by the final success.

Exact retained identities:

| Artifact | SHA256 |
| --- | --- |
| Original transport154 | `aee95131327723f0e757b69aa2e9fcea9f7a30b67dc1db0b8daf0e6aee5fbdd0` |
| Version2 transport154 | `38a1a55a2abfd21939b626fa630b9470ca139fea0795dc1fe4f4538aaa6127ae` |
| Check1 raw failure | `cbfd5964c6373878802d06cef2aff05e1773edb3133c51557e3e4091aba8c47e` |
| Check2 raw failure | `76e01cab7cb7acde105ab8b1a8370a4845a71bd7aa113c74ce9072e473c565de` |
| Check3 report | `1dee71e42c1e805bd3f29e8273944e79bb7b70349e40b8ec0f786bc53a182171` |
| Check3 empty raw log | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| Installed partial-frame/fuel module | `e407fa36087e6f5521dbd2da098aa49d1fe37817f16a2c9d32227d56153e67bc` |
| Installed primitive-observation module | `ebc891e8461c7b545d55f6823322789f19635e2d1c58a5551307b621079ba0ab` |

No mathematical or scope blocker was found. This clearance covers the selected transport theorem and preserved repair history. It does not claim checkpoint installation, aggregate Audit, sealing, or publication.
