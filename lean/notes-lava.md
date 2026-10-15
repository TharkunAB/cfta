# Lava and the cfta proof boundaries

Source: Colin Rothgang, Loïc Peyrot, Yannick Forster, Michael Greenberg,
and Niki Vazou, *Lava: Foundations for Liquid Haskell via Translation to
Rocq*, arXiv:2610.14092v1. Matti supplied the local PDF at
`/home/tritlo/Code/microecta/lava.pdf` on 2026-10-14.
SHA-256: `5d298362a55c4e2dbed97ca9ac35328c74fc93b2e840503f32d7eb24c32516e4`.
Page references below use the printed page numbers in that PDF.

## Complete filter specification (2026-10-15 03:28 CEST)

The actual required-path worker now satisfies its independent node and forest
filter specification. This theorem is separate from function/graph agreement
and finite completion. Actual closed-source selection derives the next
worker's cache premises and both required-operation laws. Read
[the current note](notes-required-filter.md). The native edit/narrowing and
full pass correspondence obligations remain. No Lava or Rocq dependency is
added. The supplied local PDF still has the recorded SHA-256.

## Independent head-language application (2026-10-15 03:13 CEST)

The completed head graph now has an independent guarded least-language theorem.
A finite future cache supplies exact physical alternatives and independent
child readback without a runtime conversion. Actual source construction derives
all initial premises. The full required-path graph retains both semantic probe
heaps. Read [the current note](notes-required-head-language.md). The complete
required-node filter specification still needs its separate theorem.

## Complete required-path graphs (2026-10-15 03:00 CEST)

The physical required-path worker now has graph/execution agreement in both
directions and unique complete returned caches. Original source construction
derives finite stable execution. Worker and head-read proof bounds remain
separate from source errors. Independent output-language equality remains the
next theorem. Read [the current note](notes-required-execution.md). This keeps
the paper's executable/graph distinction explicit without treating a graph
agreement theorem as a complete semantic specification.

## Required-path application (2026-10-15 02:30 CEST)

The actual Needed compiler now has independent complete-path term semantics.
The ordered child fold composes explicit per-node contracts into its exact
forest meaning. Actual arity checks derive all normalized child positions.
The physical recursive node must still prove its contract. A separate kernel fixture checks actual constructor-row exposure of the closed
raw self binder. Independent least-language semantics proves that replacement
by empty preserves its language. Eight native traversals now use that exposure;
the existing finite cold-reader proofs remain available for the general path
worker. Read [the current note](notes-needed-head-repair.md). Compiler meaning,
finite physical worker execution, and complete native pass correspondence stay
separate claims. The latter two remain the next proof work.

## Physical caller application (2026-10-15 02:13 CEST)

The physical class sort and early guards now connect to the complete memo
selection graphs. Actual array normalization supplies the guard result.
A source and kernel check finds a closed raw self binder that unfolds to
itself after the gate clears it. Thus completed gate correspondence still
does not establish progress of the following required-path worker. Read
[the current note](notes-physical-class-order-entry.md). Preserve this
distinction when deriving the next function/graph correspondence theorem.

## Complete selection application (2026-10-15 01:52 CEST)

The ordered class filter now has separate finite execution and receipt graphs
with both actual memo tables. An independent source induction derives exact
gate replay in caches that retain all completed work. This supplies pure
selected-class readback in the final cache without a whole-gate observation
premise. Read [the selection note](notes-ordered-class-selection.md).
Physical class sorting, caller prechecks, native primitives, and extraction
remain separate obligations.

## Current application (2026-10-15 01:40 CEST)

The actual visited fold now has an exact physical reachability theorem.
The complete gate graphs now contain both actual memo runner equations and
their exact finite source readback. The predicate graph extends the already
proved unfolding graph. This reuses correspondence proofs instead of taking
a whole-callback law. Read [the current proof note](notes-source-crush-both-memos.md).
The remaining selection caller, native scheduling, and extraction boundaries
stay explicit. The earlier termination discussion below records the boundary
that existed before the independent general unfolding-rank proof.

## Useful method

Lava translates executable definitions and logical refinements into Rocq.
It distinguishes a refined executable function from an unrefined inductive
graph relation. It proves that the function satisfies its graph relation.
Higher-order arguments carry the function, its graph relation, a proof of
functionality, and a proof of agreement (§1.3, pp. 3–4; §2.6 and §3.3).
Implicit subtyping becomes an explicit cast with a proof obligation (§3.5).

This distinction applies to the cfta proof structure. A logical guard meaning
does not establish the behavior of the executable solver adapter. A model
of a constructor callback does not establish the behavior of the stored
executor. Each needs a separate correspondence theorem. Actual cache effects,
errors, and callback completion must remain in that theorem.

`SourceClosedSized` already follows this method. Its reference and optimized
paths derive actual construction and query execution, then identify their
successful API with the independent expression language. Its solver-decided
path also retains external attempt completion and response correctness as
explicit contracts. Lava supplies useful prior art for these separate claims.
It does not discharge those contracts.

For future source translation, retain a relation for each actual operation,
prove agreement with its semantic specification, and derive public results
through those agreement theorems. Check generated proof terms in the target
kernel. Do not accept an SMT verdict as a replacement for a checked proof.
This is a possible method for reducing the remaining source-correspondence
boundary. No translator or new proof system is introduced here.

## Limits that matter here

The supported fragment is monomorphic. It excludes non-structural recursion,
partial applications and lambdas in refinements or reflected functions, and
constructors with higher-order parameters (§3.1.1, p. 10). It therefore does
not directly cover the cfta interned core or the repeated open-Mu gate.

The evaluation theorem uses a call-by-value calculus (§4, p. 20).
Appendix C.1 assumes termination of that calculus because Liquid Haskell
checks termination (p. 34). This does not prove Haskell lazy scheduling or
finite execution of the remaining required-path and fixed-point workers.
The open-Mu gate now has an independent rank proof. Do not use the paper's
termination assumption to close any remaining worker obligation.

The translation maps Haskell `Int` to unbounded Rocq integers and treats
overflow as undefined (pp. 4–5). It does not replace the existing native
word, tag, counter, and capacity proofs.

Theorem 4.1 relates the declared reflected functions to their graph relations
for the stated elaborated calculus. Its additional executable equality uses
the checked coherence lemma in the translation output. The paper does not
claim that every accepted Liquid Haskell program produces a successful Rocq
proof (§4, pp. 20–21). It is not a verified translation of arbitrary GHC Core.

The automation can leave proof obligations for manual inspection (§5, p. 21).
Only a fully checked result can count as a completed certificate. A generated
file or a translation success alone is not proof evidence.

## Effect on the current plan

Keep Lean, the existing optimized interned core, and the exact Sized sequence.
Keep external solver contracts and runtime/extraction limits explicit.
Continue the repaired physical required-path proof. Use this paper when designing
any later source certificate path. Do not add Lava or a Rocq dependency to
the current project without a separate decision.

## Current use of the function and graph method

The ordered gate checkpoint `512a386d` has a separate logical execution graph.
It proves graph/execution correspondence in both directions. It also proves
uniqueness of the Boolean result and complete final cache. The source gate
can share constructor effects across sibling edge and path queries.
These are Lean proofs of the modeled source worker. They do not add a Lava
translation, a Rocq dependency, or a verified GHC extraction claim.

Checkpoint `c087a4ed` extends the logical graph method to actual unfolding
memo calls through complete node and class scans. Each readback follows
from canonical cache coherence and the checked memo runner. No whole-callback
or whole-gate observation law is supplied.
