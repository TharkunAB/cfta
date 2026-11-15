# Proposed fixed-reader theorem shape

Status: DESIGN ONLY. This file contains no Lean declaration or proof credit.

Fix the SAME accepted library/query/source expression and successful original
build. Fix its original stored FULL value `U = mu entry body depth ordinary`.
Write uid for entry.identity. These source parameters never change.

For a supplied actual checked trace `T : Trace n C0 S0 Cf Sf`, set

```
F = Sf.native.machine.heap
Profile(v) = (v.free = []) and (forall a in atoms(v), a = mu uid)
A(r) = (r.domain = emptyDomain) and Profile(r.left) and Profile(r.right)
```

C0 is the genuine original compiled request control. It is not arbitrary Code.
The original root, operands, caller state, and supplied bounds remain exact.
For the empty-cache derivation, S0's two physical memo tables are the literal
empty initial tables. Other initial source facts stay those of the full target.

An authentic M witness is ordinary quantified DATA about T, not a proposed
new ledger or public predicate. Retain actual existing equations/traces:

- A literal prefix from C0/S0 to the queried Mu owner, its lookup/demand and
  actual compiler entry; use an existing owner Origin where it applies.
- The exact full entered U and P, real control identity equations, original
  domain argument emptyDomain, P.free=[], and P's node/union tag. P has NO
  only-U assumption.
- A literal prefix to `.code (.enter emptyDomain U P uid pid k)` at entryBefore,
  plus the actual one-step transition and actual suffix to Cf/Sf. Both operand
  orders are retained. The entry is in T, not a fictitious same-key event.
- `E = Environment.enter entryBefore.native.machine.domains emptyKey U P uid pid`
  and the exact entered machine `{entryBefore.native.machine with domains=E.2}`.
- Available F P. Derive it from the real entry check and suffix. Do not add a
  whole-goal future-pattern availability supplier.

For each witness w, M_w(r) states the ORIGINAL request qualification:

```
r.domain = E.1
r's operands are exactly (openAlias,Q) or (Q,openAlias)
openAlias = body or openAlias = reference(interned uid)
Profile(Q)
height(Q) <= height(P)
openAlias = reference(interned uid) -> height(Q) < height(P)
```

The conditional result law is the following mathematical function:

```
law_(T,F)(r,v) =
  (A(r) -> Profile(v)) and
  (forall authentic w in the SAME T, M_w(r) -> Profile(v))
```

Use it directly in the EXISTING predicate:

```
SourceCurrentAllocatedNativeContextCache.Returned law_(T,F) state.native.nodes
```

The corresponding edge law uses actual ordered child pairing and the same
A/M qualifications. Its result requires Profile for every returned child.
It is passed to the SAME existing Returned predicate for state.native.edges.
This audit does not add a second cache framework.

Desired derived conclusion for every actual split of T:

```
forall k <= n,
  exists Ck Sk,
    Trace k C0 S0 Ck Sk and
    Trace (n-k) Ck Sk Cf Sf and
    Extension Sk.native.machine Sf.native.machine and
    Returned law_(T,F) Sk.native.nodes and
    Returned edgeLaw_(T,F) Sk.native.edges
```

Quantifying over an actual split can instead be an induction-local statement.
The existential intermediate state is determined by T. It is not a future
heap/model provider. The literal suffix supplies all forward extensions.

This full Returned conclusion is NOT currently proved. `returned_empty` proves
its base for the FIXED law; existing lookup/demand/finish laws prove the cache
steps once local producer laws are established. Every native outcome and
supplied fuel must preserve it. The last non-yielded effect needs the existing
actual step invariant, as described in AUDIT.md.

The outer public native source A/M and whole Source output targets keep their
original source/root/fuel/entry parameters. An internal fixed-reader proof must
specialize back to those exact targets. It must derive witness existence and
actual height descent at use. It cannot replace these targets by conditional
Returned or assume all actual requests have a future witness.
