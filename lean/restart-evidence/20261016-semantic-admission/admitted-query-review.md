# Review of actual next-query admission and contextual rebasing

Read-only source review on 2026-10-16. No Lake process, Haskell execution,
or proof-source edit was performed by the reviewer.

Reviewed source hashes:

* `SourceCurrentAllocatedNativeContextRebase.lean`:
  `dba21c2a73176cb6d898eb77817ec760e2c6e7f423d264bd4c3ea4c80de74726`.
* `SourceCurrentAllocatedNativeAdmittedQuery.lean`:
  `c908056843957d5e6c84fdca258aba59365aa8d4408c41b7ec01a31915731e5b`.

No material semantic defect was found in these bytes. This review is not
an independent compilation receipt. The root owns the canonical build and
public probes.

## ContextRebase

`Agreement` states old-valid inclusion and exact old-input rank agreement.
It does not assert equality of total views or rank families.
`Agreement.language` correctly erases the identical rank witnesses.
`NameCovered` requires an old-valid **nonempty** representative of the
identity. Its nonempty condition prevents use of `.empty` to infer any
unrelated identity's rank language.

`SeenAdmitted` covers the literal `domain.seen` pairs in returned original
requests. The transport does not infer that coverage from `Contextual`.
The soundness direction converts a new sound environment to an old sound
environment and converts the old common-language conclusion back to the
new interpretation. The completeness direction converts old bounded pair
terms into new bounded pair terms before using the supplied new complete
environment. Exact child ranks pass through `row_rank` without increasing
the bound. The two directions are consistent with `NodeLaw` and `EdgeLaw`.

`contextual` consumes old request admission and old seen-pair coverage for
each literal returned cell. Thus a previously vacuous conditional cell law
cannot acquire meaning through a new admission. No semantic result law is
inferred for a previously unadmitted original request. `rebase` transports
the same tables and their old coverage certificates; it does not run a
cache operation.

## AdmittedQuery

`inventory_agreement` derives both agreement fields through the actual
source/target inventory construction and actual heap/issued growth.
Target original syntax is derived from target coherence, current resident
values, and their closed free fields.

`query_complete` (lines 58–123) has the intended one-next-query scope:

1. It sets `target` to `state.native.machine.heap` and obtains its `Facts`
   from the current `Good` invariant.
2. It constructs the literal finite root list `roots ++ [left, right]`.
   Old root availability follows actual growth and issued history. New
   root availability and closedness are explicit current input facts.
   Empty roots or duplicate operands cause no missing case.
3. It derives the target finite inventory, old-domain agreement, and the
   contextual laws for the **same** current native memo cells. Old
   `Admitted` and `SeenAdmitted` remain explicit independent premises.
4. It derives both new operand `Original` and model validity from their
   actual target-root occurrence.
5. It invokes `WarmQuery.query_complete` on the original full checked
   `state`, with the current heap as the fixed source and reflexive source
   growth/history. No native or equality-operation cache is reset. The
   returned receipt uses the actual returned full checked state.

No future ready state, successful body, result-language receipt, or final
model-validity callback is supplied as a premise. `WordRanges` remains an
explicit reached-prefix machine-key condition. Its definition ranges over
actual checked `Steps`; it does not require completed native execution
(`SourceCurrentAllocatedNativeRequestBounds.lean:125–136`).

## Exact remaining scope

The result supplies actual finite checked completion, closedness, and exact
intersection language for one next pair of closed resident operands.
The returned finite model is constructed before that checked query starts.
The current `Good`, `Scoped`, semantic readiness, idle state, and actual
word-range premises remain explicit.

Neither endpoint derives old request or seen-pair coverage from physical
cache validity alone. The output receipt does not derive admission and
seen-pair coverage for every newly completed internal cell. A causal
preservation proof for those new cells is required before iterating this
adapter over generated fold tails. No full dynamic fold, class-scan
semantic composition, outer constrained caller completion, or GHC cache
publication/forcing claim follows from these files alone. Their headers
state this boundary accurately.
