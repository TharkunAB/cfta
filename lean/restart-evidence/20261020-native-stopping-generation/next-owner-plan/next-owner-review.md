# Next compiled optional-owner producer

Status: PROPOSED AND UNPROVED. This report adds no proof or production declaration. Reviewed at 2026-10-20T18:35:35+02:00. Zero new Lean jobs and zero proof pairs.

## What is now available

The official `NativeTracePrefixBind.bind_prefix_cases` retains the SAME physical unfinished call or the SAME completed call and continuation suffix, with exact fuel sums. Pure returns cost zero steps.

The official `NativeWalkPrefix.walk_prefix_cases` additionally retains the ORIGINAL input index, actual earlier `Walk` over `take index`, its ordered results, and the unfinished callback. Its continuation retains `drop (index + 1)` and `earlierResults ++ value :: tail`. No new walk induction or desired provenance hypothesis is needed for union members, joined row pairs, or zipped edge children.

These two lemmas close the physical splitting gap identified in the earlier audit. They do not yet prove compiled control provenance. The earlier audit remains an unchanged historical design document.

## Minimal public target

One proposed theorem, `request_optional_owner`, consumes only this SAME recovered physical prefix:

```text
site : Trace siteFuel
  (.code (requestNode root.domain root.left root.right)) before
  (.code (.optionalBinder pair siteBody siteNext)) siteBefore
```

It derives ONE tuple `queryFuel, childFuel, queried, queryNext, queryBefore, handle, chosen, running, captured, first, second`. Put:

```text
compilerBefore = {queryBefore with native := running}
K value = .finishNode handle value (queryNext value)
entered = Environment.enter compilerBefore.native.machine.domains
  captured.domain.key captured.left captured.right first second
childBefore = {compilerBefore with native := advance compilerBefore.native
  {compilerBefore.native.machine with domains := entered.2}}
```

The tuple must retain:

- `siteFuel = queryFuel + 2 + childFuel`.
- The actual prefix from the SAME root call to `.code (.node queried queryNext)` at `queryBefore`.
- Actual `lookupNode queried = (.memoized handle, chosen)` and `demandNode handle chosen = (.evaluate captured, running)`; full suspended/evaluating captured cells; and the exact yielded node step to `(compileNode captured).bind K` at `compilerBefore`.
- The actual captured decision is a Mu branch, both captured identities are `first/second`, and `pair = Control.pair first second`.
- The exact enter step and its physical Inputs. These yield the captured domain and captured operand availability at `compilerBefore`.
- The actual UNBOUND child `Trace childFuel (requestNode entered.1 (body captured.left) (body captured.right)) childBefore (.pure siteBody) siteBefore`.
- `siteNext = K`, or equivalent exact whole-control equality. The child return is EXACTLY the given `siteBefore`.

No target-cell locator is run again. The existing locator's operation, selected full cell, prefix, and suffix remain in its SAME existential. No owner/root return or desired owner is an input. Initial Good, Fields, native writer History, or an empty heap are not proposed core premises. Core feasibility without those extra invariants remains to be checked.

## Smallest remaining proof structure

Use three private, mutually recursive prefix readers. Their inputs remain actual physical traces with explicit appended continuations. An internal typed continuation stack is optional; it must be DERIVED from the root prefix, never supplied as desired provenance.

1. **Node-request reader.** Invert the actual first yielded `.node` step. A memoized evaluate selects the FULL captured request and installs its evaluating handle. Register its protected continuation `fun value => finishNode handle value (queryNext value)`. A ready hit continues the actual caller continuation. A direct lookup retains its exact request and state, but has no memo handle. Carry its compiler prefix until the selected branch is known.
2. **Compiled-node reader.** Inspect the actual `compileNode` decision. Reset/swap/reference branches continue through their actual new request. Reference lookup retains the actual read outcome. Union and ordinary-row branches use the new indexed walk splitter. Work and pure branches can only reach a later site through their actual outer continuation. A Mu branch uses `enter_prefix`, then the physical bind splitter on the body request and its optional continuation.
3. **Edge reader.** Invert the actual `.edge` lookup/demand. An evaluate branch starts the ACTUAL captured `.edgeBody`; it does not assume current request equals captured request. Inspect that checked body's actual yielded branch. Sentinel paths have work and continuation only. Accepted paths emit `children` with the actual allocated conjunction, then use the indexed walk splitter over the ORIGINAL zipped child operands. Do not replace this code with the older eager edge compiler by assuming an unproved field/conjunction equation.

No fourth walk induction is required. The existing walk theorem retains the exact earlier calls, selected position, and remaining ordered continuation needed by readers 2 and 3.

Protected `finishNode` and `finishEdge` are deterministic one-step boundaries. Crossing a finish retains its exact handle/value/current state and resumes its actual outer continuation. There is no need to finish an active owner in the future. The root continuation is `.pure`, so a site cannot enter from an arbitrary caller continuation after the root returns.

At every bind split, retain which arm occurred. In the unfinished arm, binding a NONPURE control preserves its instruction constructor. Equality with the given optional control therefore identifies an actual optional instruction inside that same call, rather than a pure return that started an outer continuation. In the completed arm, keep the actual middle state and continue its actual suffix.

## Critical continuation cases

A completed Mu BODY is not enough to attach the CURRENT site to that Mu. Its returned optional continuation may already have executed, and the current site can lie later in an outer continuation. Attach the owner only when the suffix is at THAT registered optional instruction with zero further steps. If the suffix crossed it, retain its actual yielded optional step and continue outside it. A blocked optional cannot be crossed by a yielded Trace prefix; it can still be the current site of an all-outcome locator.

The same distinction applies after a completed node/edge body and its finish frame. Do not choose the earlier completed query merely because its pair, body, handle, key, or result matches the current site.

Prefix factors must compose to the given root prefix with the exact fuel equation. When an inner source query receipt is lifted through a surrounding bind, lift its actual prefix by `Trace.bind` and compose continuations using `Control.bind_assoc` / `Code.bind_assoc`. Retain the WHOLE continuation equality; do not assume bind is injective on arbitrary functions or full code.

## Memo and support limits

A final successful Mu owner cannot be a direct lookup: direct lookup has no request key, while both successful identities give `sourceKey_complete`. Direct non-Mu calls can still contain a deeper Mu site and must be traversed.

The captured request is the one returned by the ACTUAL demand. Keep `queried` and `captured` distinct. Their equality is a separate `node_started` application needing physical cache Valid plus the query's actual NodeReady/KeySafe checks. Matching a truncated key or native Shape does not prove it.

If the endpoint later needs the owner still evaluating at `siteBefore`, initial native Shape suffices for an additional retention result: propagate it along the exact prefix, then use the actual completed clean CHILD trace with `DemandRunning.trace_retains`. This is stronger than completed-cell `Retained`. Do not invent History at the active entry or site.

The registered compileMu owner identifies an actual native query and exact stored operands. Its optional operation's generated rooted writer describes the encoded stored construction. Neither receipt identifies original program source syntax or original capture binding ancestry. General renewal and whole-model termination remain separate.

## Suggested proof order

First prove private node/edge start and protected-frame prefix cases from actual Trace constructors and `bind_prefix_cases`. Then prove registered Mu enter/body/optional prefix cases, including the crossed-optional case above. Finally combine compiled-node and checked-edge branch readers; `walk_prefix_cases` supplies all list-indexed recursive descent.

Use induction on finite ACTUAL prefix fuel, with structural branch/walk analysis where no instruction is consumed. Zero-cost pure returns must not be used as a claimed strict fuel decrease. This is a proof about an already given finite prefix, not a termination theorem.
