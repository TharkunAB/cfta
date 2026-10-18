# Union-body Head row origins

Reviewed on 2026-10-18 at 03:12 CEST.

The production source is `SourceCurrentRecursiveHeadUnionRows.lean`.
Its SHA256 is `a0a3bcfb515fd955838c62121d78bfa632547da048bce618535d860571bf5700`.
The four public heads are `MemberRows`, `Rows`, `complete`, and `actual`.

## Producer and exact scope

`complete` starts with `Ready`, physical availability of a Mu whose literal stored body is a union, and closedness of that Mu. It constructs an actual Head. It does not consume a Head, member schedule, row-origin certificate, or output relation. `actual` aligns this constructed Head with a supplied actual Head by exact result and heap uniqueness.

The receipt retains the first actual repaired execution of the stored union body. It also retains the ordered member calls from the same initial heap. Actual execution uniqueness aligns the body execution with the member producer. The receipt records growth from the member return heap to the body return heap and then to the actual final Head reader. The member outputs replay at that final reader.

For every selected Head row, `Rows` gives an original union-member index and its actual returned value. The row has an Origin at that returned value. If the original member is a literal stored node, `MemberRows` gives its earlier original row index, an ordered `All₂ RowCalls` schedule, the exact output row, and survival of that row. Each RowCalls retains the complete symbol, complete constraint, ordered children and actual warm repaired child executions. This applies to both open and closed source nodes. The closed-union branch uses the stored free-name invariant to derive closedness of every original member. It does not assume canonical original row order.

The additional indexed-member clause applies to any actual member return and any of its final-reader Origin rows. It does not depend on the existential member chosen by the Head row proof.

## Constructed integration

The single constructed endpoint has no premises. It builds its own retained Mu from syntax, obtains source Ready and availability, and runs an actual Head. Its literal stored body is a mixed union. Member zero is an open ordinary node. That node has a nontrivial equality-bearing full constraint and two ordered children. The second union member is a retained nested Mu. The fixture proves that a selected final Head row has the exact full constraint and child count two. It also proves the new MemberRows receipt for the open original node member and the complete Rows receipt. The private checked witness keeps the public proof print finite; the public alias has the same explicit statement.

The receipt already includes final-reader warm member calls. The integration does not assert a second full Head call or a full-state identity obtained by evaluator normalization.

## Residual boundary

The other member cases are explicit. An empty, reference, union, or Mu member retains its indexed actual returned-value Origin but has no additional MemberRows condition. The module does not claim that every selected Head row has an earlier literal node member. A literal stored body whose root is Mu is also outside this theorem. Those cases require a genuine reconstruction/unfold or selected-writer alignment argument. This theorem does not identify native compileMu rows with original request operands, prove physical substitution fusion, provide a global execution trace, or prove outer termination.

## Validation and attempts

The final production direct check and imported printer-free integration check have empty logs. The canonical target succeeds with 1429 jobs. It replays the unchanged `InternedFreshOrdinaryClosedCompletion` unused-input warning. The new production and selected direct integration have no warnings.

The selected imported groups check, print, and print axioms for all four public heads and the one constructed endpoint. Each source states linter.all and all seven proof-print options. Each source uses `#check @`. The verifier rejects printer omission or failure text and any axiom outside propext, Classical.choice and Quot.sound.

Every attempted source and raw log remains in this prefix. Draft attempt one failed because a local identifier was a reserved parser token. Draft attempts two and three succeeded. The combined isolated draft fixture succeeded before production writes were allowed. The final selected integration imports the canonical production module. Each heavy attempt ran the immutable numbered snapshot itself. The inner worker read and checked effective memory.max and memory.high at 4294967296 bytes and memory.swap.max at zero.
