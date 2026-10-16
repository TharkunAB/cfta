# Finite declaration discovery for typing ranks

Source main `885a446e` merges PR 51. Local merge `aa981389` preserves the
previous checked query checkpoint. Upstream repairs the helper constructor
order. The preserved Z/A reproduction now gives `[Lit Z,Lit A]` through
both `fromDatatype` and `fromTypingRules`.

## Newly reached source failure and repair

The upstream ordering table walks every constructor field description.
Its visited set stops repeated full TypeRep values. It does not stop a chain
of distinct growing types in an unused field. A legal Generic example is:

```haskell
data Growing a = End | More (Growing [a])
data Root = One | Two | Unused (Growing Int)
```

Typing rules for only `One` and `Two` form a finite two-leaf graph.
The singleton control returns `[One]`. Adding the second leaf forces the
ordering map and the unused Growing chain. Complete rendering hits the
reproduction's two-second timeout. The source recurrence has no repeated
TypeRep on that chain. The timeout alone is not a proof of GHC divergence.
`deriveFTA` separately rejects the full description with NonRegularRecursion.

The local repair builds a finite needed-type set from the constructors in
the actual typing rows. Metadata discovery skips an algebraic type if it is
not needed or already seen. Every admitted type keeps all of its constructor
alternatives and local declaration indices. It then visits fields before the
old pending suffix. The order callback captures this map once. It retains
the original label and the default-zero literal key.

The repaired reproduction returns exactly `Right [One,Two]`. Both the Z/A
helper order and standard Bool False/True order remain unchanged.
The Bool documentation is corrected: the standard HasFTA Bool description
is algebraic and has declaration positions. Atomic literals still use label
order, which need not match an arbitrary supplied fromDatatype domain.

## Checked models

`SourceTypingHelperOrder` retains the literal upstream finite traversal,
local row indices, last-label-winner map, and zero fallback. Its completed
traversal relation does not assert discovery termination. This historical
phase remains intact.

`SourceTypingRelevantHelperOrder.reachable` computes the repaired walk.
Lean checks termination by the lexicographic pair of unseen needed-list
occurrences and pending length. Fresh needed types decrease the first part.
All other branches decrease the second. `reachable_trace` derives the exact
completed traversal. No completed-discovery premise or global finite state
universe is supplied. The emitted-row count is bounded by the initial unseen
needed inventory. An infinite-key unused description chain is a checked case.

Returned positions have their original needed declaration and local index.
Lookup equals the last matching entry of the exact emitted comprehension.
Absent labels keep literal zero and their original text.

## Remaining source adapters

The logical descriptor function has finite completed heads and field lists.
It does not prove that arbitrary Haskell callbacks or bottom values can be
forced. The runtime needed set still needs exact readback from row symbols.
Sufficient needed-only ancestor coverage follows from the intended coherent
Generic and fixed-term representation, but that bridge remains unproved.
Arbitrary inconsistent descriptions can change which metadata is found.

Retain constructor-label identity, complete local alternatives, exact Set/Map
and String/Text representation, Int bounds, and native Flat/Automaton order
as separate obligations. The new walk does not prove whole Typing semantics,
codec inverses, complete value/rank equality, or arbitrary literal-domain
ordering. Existing supplied-rule language proofs remain unchanged.

## Validation and artifacts

The upstream strict all-component Nix build and 225 generator examples pass.
The local repair has a focused strict generator build and Fourmolu check.
Its existing generator suite and focused source reproductions are recorded
in the final validation report. Other five suites are reused from the previous
source checkpoint because only Typing changed. No local test file is changed.
The four package descriptions are unchanged and retain their Cabal-gild check.

Both helper-order model builds pass. Each has seven public axiom/signature
probes and ten literal kernel examples. Aggregate checks are in the restart
package. Evidence uses `/tmp/mcfta-helper-order-*`,
`/tmp/mcfta-typing-helper-*`, `/tmp/mcfta-typing-relevant-*`, and
`/tmp/mcfta-typing-unused-growing-*`. The preserved Bool and growing-type
source probes are new marked external drafts. Older probes remain intact.
