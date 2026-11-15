# Closure of the actual native Returned law

Status: SOURCE DESIGN AUDIT. No new Lean code, compiler credit, or runtime
counterexample. The earlier empty-domain A plus original body/ref M law is
NOT closed under the actual reference adapter. The public empty-domain A
statement must stay unchanged.

## Confirmed closed-request gap

`compileReference` emits `requestNode domain bound other` or
`requestNode domain other bound`. It preserves the SAME original domain.
For the original U binding and closed Profile Q, the resulting request is
`(D,U,Q)` or `(D,Q,U)`. Both operands are closed and only-U. Neither operand
is the open body/ref alias. The original mixed domain D is nonempty. Thus
this request satisfies neither empty-domain A nor original M.

`requestNode` is a `.node` instruction. The actual native step performs its
lookup and demand BEFORE it compiles the requested body. A ready result runs
the supplied continuation directly. Reset has not run. Only a real evaluated
miss or nonmemoized direct body reaches `compileNode` and its reset branch.
It is therefore insufficient to say that the next closed request eventually
resets to A. A warm hit must already carry the closed result property at its
EXACT original SAME-D request.

The same issue appears for the canonical closed marker self call in an open
body row. Reset precedes self inside the body, but ready lookup precedes BOTH.
The ordered raw request key retains its domain and operand order. Neither
sorting nor reset normalizes the cache key before that lookup.

## Minimal closed reset extension

Keep public A exactly at emptyDomain. Internally use the existing Returned
predicate with the following additional conditional clause. This is only a
mathematical specification of its law argument, not a new predicate framework.

```
Profile(v) = v.free=[] and every boundary atom of v is mu uid

C(r) = Profile(r.left) and Profile(r.right) and
       (r.domain = emptyDomain or r.domain.key.free.isEmpty = false)

C(r) -> Profile(result)
```

C includes the old A qualification. At a genuine nonempty-free domain, Empty
still returns first. Every other closed request resets to the EXACT smaller
empty-domain call. The reset adapter must store its derived C property at the
original nonempty-domain finish as well as preserving the child A property.
A later hit consumes C directly. This adds no arbitrary-domain A public theorem,
no new caller premise, and no change to the supplied fuel or actual request.

The literal original mixed domain has nonempty free bindings by the EXISTING
`SourceSynthesisUniverseClosedResetSteps.mixed_entry_nonempty_free_map`.
That fact does not depend on the pattern's payload or later effects. The
existing kernel closed-reset equations describe the mathematical branch. They
do not themselves prove the checked native warm-cache preservation law.

A slightly narrower equivalent implementation may qualify closed requests by
their actual source-derived resettable-domain origins. It must still include
all same-D reference results, open-row marker calls, and their raw swapped
keys. Do not require a new future supplier for those origins.

## Why unqualified ANY domain is unsafe

Physical Domain validity alone allows a canonical typed represented key

```
free = []
seen = [pair(qid,rid)]
```

with qid and rid distinct. Choose two closed nonempty available ordinary
values Q and R in increasing source order. Their atoms can be empty, so both
have Profile. Empty, reset, self, and swap all fail. The repeated branch returns
an OPEN `reference(intersection qid rid)`. Profile of that result is false.
AvailableBindings is vacuous when free=[]; it does not forbid this key.

This is a counterexample to a proposed unrestricted Domain-conditional law.
It is not an accepted-source failing trace. A handwritten raw `.enter` with
non-Mu operands can allocate this shape, but a genuine compiled Mu branch
has a real Mu operand and inserts its binder. The real source origin is
therefore essential. Empty NODE/EDGE memo initialization alone also says
nothing about an arbitrary preexisting DOMAIN cache.

For the actual source domains, the intended case invariant is emptyDomain OR
a nonempty free map. Actual Mu entry and reset can establish that case split
from the real initial domain. Its whole-source producer remains an obligation.
C states the exact sufficient cases and avoids an unsound blanket claim while
that source-origin proof is composed.

## Concrete same-D warm test

Let D be the literal original entry for U and an ordinary/union P. Let Q be
a closed ordinary only-U value below P's strict ref height. The already-derived
mixed-reference control reads original U and emits `(D,Q,U)`.

Suppose that exact request already has a ready cell from a legitimate earlier
reset evaluation. Its key contains D and ordered Q/U references. The next
actual `.node` hit returns its payload immediately. No empty-domain request
is made on that hit. The old A/M Returned law gives NO result condition for
this cell. The new C clause does.

This is a missing induction case, not evidence that the payload is wrong.
At the abstract invariant level, the old law would also permit an Available
open ref payload for that cell because both A and M antecedents are false.
A source history must exclude that state by proving the C law at the actual
producer finish. Weak physical validity cannot supply it.

## Open alias replay is a different required closure

The source-specific canonical-U branch has other internal requests beyond C
and original single-entry M. They intentionally return OPEN payloads. Adding
a general Profile obligation for all of them is false.

Write B for the original open body, b for its node identity, R for ref uid,
d = pair(uid,uid), and e = pair(b,uid). Let D be the original mixed domain
with singleton seen pair(uid,pid). The existing source facts separate pid from
uid and b. The exact source branches create these two routes:

- Starting at `(D,B,U)`, Mu entry adds e. Its child is `(D+e,B,B)`. The body
  rows call marker/marker and R/R. The off-diagonal R/R route reads U, enters
  diagonal d, and returns repeatedValue(e). The body product is OPEN with
  cutoff e. The outer optional binder e reconstructs original U.
- Starting at `(D,R,U)`, swap gives `(D,U,R)`. Mu entry first adds d. Its child
  `(D+d,B,R)` reads U and emits `(D+d,B,U)`. A second Mu entry adds e. Its
  child is `(D+d+e,B,B)`. The R/R rows now hit repeated d. The product has
  OPEN cutoff d. The inner optional binder e is unused; the outer binder d
  reconstructs original U.

The single-entry original M qualifier does not cover these enlarged domains.
B/B and R/R also do not have a closed opposite operand. Their actual warm hits
can bypass precisely the control/read/row computation that proves the expected
cutoff. The existing kernel proofs explicitly retain these OPEN values.
They cannot be turned into Profile results merely by changing their names.

## Recommended minimum law closure

Use the SAME existing Returned law parameter, with the following precise
properties. No new cache structure or ledger is needed.

1. C implies Profile for closed requests at empty/resettable domains.
2. Genuine original M, BOTH operand orders, implies Profile under its unchanged
   original domain, full P, and weak/strict height conditions.
3. Literal canonical-U auxiliary replay requests carry their exact expected
   cutoff or source-body readback. Include the actual enlarged domain and
   each raw swapped request that the native code can memoize. Preserve the
   diagonal-first and body-first routes above. The expected value may be open.
4. Edge cells retain the property needed for their actual ordered child calls.
   Ordinary M products use C/M child profiles. Canonical-U self products use
   the exact transformed row children/key, including their legitimate open
   cutoff. Do not demand Profile for those open row children.

Alternatively, derive the same auxiliary facts from an existing genuine
warm-producer replay theorem with complete native history. That theorem must
cover ready hits and the ACTUAL allocated checked edge body. The inspected
kernel replay equations do not establish that correspondence. No such complete
native warm replay producer is credited in this audit.

## Other adapters checked

`FAMILY-LEDGER.md` records every branch of compileNode and the memo/constructor
adapters relevant to the original C/M proof. Swap needs no extra abstract
family when C/M and auxiliary clauses include both raw orientations. Union
members preserve the same genuine M witness with smaller height; they do not
justify rebasing its original P. Empty and unsupported failures do not create
a missing closed-success family. Generic pure/finish/bind and optionalBinder
are continuations or effects, not extra cached request qualifiers. Their
all-outcome preservation obligations still remain.

This audit does not claim that these clauses already prove the whole history.
They identify the concrete missing closure cases. All source/root identity,
original fuels, native outcome tags, noStop behavior, and earlier emissions
after a later stop stay in scope. The full SAME original partial-root finite
accepted-completion under ONE assignment remains unchanged and open.
No Haskell fix was established.
