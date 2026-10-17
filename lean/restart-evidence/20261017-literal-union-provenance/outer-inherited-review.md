# Immediate inherited descent and outer keys

The new production module is `SourceCurrentOuterInheritedDescent`.
Its checked source has 118 lines and six public declarations.
`pathHeight` is the longest path in the complete inherited class records.
It is zero on contradiction and on a live empty record list.

## Actual producer

For any valid equality-operation state, any Ready LIVE NONEMPTY inherited
payload, and any child index, actual `ConstraintMemoAllocation.descend`
strictly lowers pathHeight. The premises refer only to the input state.
The proof uses the actual trie `record_pairs` law and actual sort permutation.
It uses the initial nontrivial-class invariant to derive positive path height.
It does not assume normalization output, a successful future graph, or a rank.

`descend_correct` includes cold computations and completed warm hits.
It supplies the returned Ready payload, exact source payload, valid state,
and canonical-interner growth. Canonical identity equality would imply full
ready payload equality in that returned interner. Strict path descent rules
that out. `descend_identity_ne` is the resulting physical identity inequality.
`node_key_ne` applies it to two requests for the SAME complete node value.

This law covers immediate descent without new local combination.
It does not prove that every returned parent child has a smaller rank.
It does not exclude keys of all active ancestors or prove general completion.
Local combination can add paths before descent. The existing inherited-growth
boundary remains applicable. Empty inherited payloads also remain fixed points.

## Constructed integration

`actual_cold_warm_descent` builds an ordinary source root with a productive raw
Mu child from an empty constructor heap. Ready, availability, and closure follow
from that actual source build. The equality interner is also constructed.
Its input class is [[0,0],[0,1]]. Actual descent gives [[0],[1]] and changes the
path height from 2 to 1. The proof invokes the new generic producer.

The fixture performs literal `beginNode`, actual indexed `Graph.descend`, and
another literal `beginNode` for the same complete source value.
The first owner remains evaluating at handle 0. The second owner evaluates at
handle 1 with a different inherited key. A repeated actual descent is an exact
warm hit and retains the complete caller, including both evaluating owners.
This is a constructor/descent/demand protocol prefix. It is NOT a proof that
these two requests arise along a completed general outer parent/row execution.

`empty_inherited_fixed` continues the same actual operation schedule to Top.
Its empty record list has path height zero. Further descents at indices 0 and 19
retain both its identity and the full operation state. This checks the need for
the LIVE NONEMPTY hypothesis instead of assuming every descent is strict.

## Full progress strategy and remaining proof

Mu and union outer node bodies are terminal. Only ordinary rows and indexed
walks recurse. Edge owners finish before that child recursion starts.
A possible full certificate must separate two obligations:

1. Nonplain returned guards must have proper ordinary source-occurrence origins
   below the active constrained owner. Accepted recursive exposure is plain.
   Native products and selected old winners still need composable literal origins.
2. When a plain recursive exposure repeats an existing complete node value,
   inherited descent can separate its physical key by the checked law here.
   The full proof must derive the required nonempty payload and control each
   intervening local combination. It cannot assume them for future children.

These are proposed next obligations. The new module proves only the local law.
No Haskell defect, cycle, divergence, or new runtime correspondence is claimed.

## Validation

Direct source attempt 3 has exit 0 and an empty log. The single canonical target
passes 1395 jobs. Its log replays the old InternedFreshOrdinaryClosedCompletion
unused-input warning. The new source and selected imported probes have no warnings.
All six public signatures, complete proof terms, and axiom lists pass.
Both constructed theorem signature/axiom pairs pass in kernels attempt 3.
The printer-free fixture check is empty. All imported probes set the eight flags.
Every check uses Lean 4.34.1 and actual max/high=4 GiB with zero swap.
All failed attempts retain their exact numbered source, log, metadata, and limits.
No old proof, old evidence, Audit, Haskell source, or Git state was edited.
