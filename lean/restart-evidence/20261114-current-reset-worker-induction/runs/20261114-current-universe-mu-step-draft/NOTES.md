# Original Mu selected step from the lower-fuel mixed call

Status: UNCOMPILED CANDIDATE. Source inspection only. This packet does not claim
the full closed generated-Type theorem or the simultaneous A/M theorem.

## Exact step

The candidate keeps the SAME accepted source, native build, stored original Mu,
current `Facts` and `Grows`, and current domain cache. Its operand `P` is an
available closed node or union with only the original U atom. Its selected
native decision is literal `leftMu` or `rightMu`. The Boolean side parameter
selects which operand is U. This is one selected-step theorem for both orders.

Its single induction premise is the exact actual body call at fuel `n` in

    entered(U,P) = enter domains emptyKey U P Uid Pid.

The outer selected call has fuel `n+1`. The premise is M at this strictly smaller
fuel, in this original entered domain and its exact machine. It is not A in an
arbitrary domain and does not supply an arbitrary future-result provider.

The proof follows these actual operations:

1. Allocate `entered(U,P)` with the existing `Kernel.entered` resource law.
2. Use the actual Mu selected branch of `Kernel.execute` and `onNode`.
3. Expose body(U). Node and union operands expose themselves.
4. Apply precisely that smaller-fuel M call in the same original domain.
5. Its returned value is closed. `MaybeMu.unused` therefore makes the actual
   optional-binder continuation return that literal value and heap. The complete
   returned machine, including the domain cache, stays exact.
6. Compose the actual domain-allocation extension with the checked body result.

The reversed Mu entry is equal to `entered(U,P)`: P is not a Mu, so its binder
list is empty, and the pair key is symmetric. This is an equality of the full
domain entry and domain cache, not only their denotations.

## Native ordering and the two original operand orders

The theorem requires the ACTUAL selected branch. It does not bypass a swap.
The source tags are node=1, Mu=2, union=3. In the empty domain:

| P | Direct selected Mu call | Opposite original order |
| --- | --- | --- |
| node | P/U selects `rightMu` | U/P first selects `swap`; its next call is P/U at one less fuel. |
| union | U/P selects `leftMu` | P/U first selects `swap`; its next call is U/P at one less fuel. |

Thus the direct selected call reaches M after one fuel step. The opposite order
reaches it after two steps if enough fuel remains. An exhausted intermediate
call remains a checked failure; it is not replaced by Empty.

Both swaps must still be assembled into the complete A induction. This candidate
does not assert the Mu payload before the source's empty, reset, self, ordering
or repeated-pair guards. Its selected hypothesis is the same local boundary
used by the existing selected ordinary-node atom step.

## Existing producers and missing scope

`Kernel.mu_checked` already proves availability and actual endpoint resources.
It does not preserve the original boundary atoms or the required closedness.
`MaybeMu.unused` already supplies the exact continuation equation after M gives
closedness. No exact public original-U atom bridge was found in the inspected
modules. The candidate composes these existing laws for that one selected step.

The closed-Mu classifier was reported STRICT PASS by Root at 18:41 CET. It is a
separate prerequisite: it identifies a closed only-U Mu operand as the full U.
It does not itself prove this selected native step.

`CASE-LEDGER.md` records the remaining assembly without assigning percentages.
The preserved original full and coupled headers are byte copies. They remain
open and unchanged. No compiler, live file, Git, board or child operation was
used for this packet. No Haskell change or fix was established.
