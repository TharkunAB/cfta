# Exact original input languages and semantic schedule termination

Proof checkpoint: `7387845d`. Upstream: `f59c198d`, 2026-10-14.
Source: original physical payloads and `Interned/Operations.hs:intersectOpen`.
Read [physical input view](notes-recursive-intersection-input-view.md) first.

## Canonical physical identities

`SourceRecursiveIntersectionInputIdentity.representative` reads the actual
original payload at an issued identity. `closed_representative` proves exact
canonical identity readback for every input reachable from a closed original
root. A recursive reference selects its actual Mu record. Constructor tags
cannot provide incompatible valid representatives at the same identity.

`Reachable` uses the actual input relation from either of two roots. Body,
reference, row-child, and union-member steps retain this valid domain. The
finite tagged carrier remains a superset. Unused tags do not become valid.

## Independent copied-language equivalence

`SourceRecursiveIntersectionInputLanguage` retains exact ordered forest,
guarded node, union, body, and row readback. `InputLanguage` is the independent
finite input derivation relation with its unfolding bound erased. It does not
refer to an intersection result or native execution.

`Original.copy_sound` proves that copied syntax accepts only independent
finite input derivations. Open free environments retain an explicit soundness
condition. Recursive binder soundness uses the least-language inclusion law.

`Original.copy_complete` proves the converse through each finite derivation
rank. Free environments contain reference derivations through that rank.
The proof uses original syntax induction. At a Mu, rank induction proves
membership in every language closed under the actual body transformer.
This supplies the least binder without a finite-unrolling assumption.

`copy_exact_original` combines both directions for closed original inputs.
The free-environment conditions are empty. The result holds for every
environment, complete executable guard, and symbol type. No copied-language
contract is supplied. `Original` and actual availability remain explicit
input premises. General source construction has not yet been proved to
supply `Original` for every result.

## Full finite input interface and schedule execution

`finiteInput` now derives every field of the existing `FiniteInput` interface
from two closed original roots and the actual physical cache. It uses actual
canonical representative readback, reachable input closure, and the proved
independent copied-language equation. It does not use an empty copy or an
assumed equivalent language contract.

`inputBounds` derives all required bounds from the actual issued carrier,
actual physical payload sizes, and original closed-root reference scope.
No allocation-order assumption or intersection execution is supplied.

`schedule_total` proves one finite bound and a stable result at every larger
bound for the semantic schedule on these actual inputs. The result has
exactly the common independent input language. `source_schedule_total`
starts with actual closed original physical records and states the result
as the product of their original copied least-language meanings.

This is semantic schedule termination. It is not a sufficient bound for the
native memo driver or the physical guarded kernel. It does not establish
`ProductReadback.members` or `.rejected` for a native returned row table.

## Original inputs through actual source growth

`SourceRecursiveIntersectionInputGrowth.payload_grows` retains original tagged
payloads through actual record and reservation growth. It derives exact
body, row, member, cached free-name, and copied-syntax equality on the old
available input domain. `OriginalInput.grows` retains the input invariant.
New allocations can change unused total defaults. No equality of the entire
old and new total view is asserted.

## Next obligations

Use these derived original input facts and finite semantic execution to
connect the native request tree to the schedule. Preserve actual constructor
and domain effects, both memo families, publication before demand, and the
original completion frames. Derive sufficient first-run native bounds.
Do not assume a completed native trace or use larger-bound stability as an
existence proof. Carry the explicit checked machine-word ranges.

General completion of new optional binders and preparation of their actual
bodies remain open. The original input view remains fixed on its valid
domain through growth. This fact does not complete new output construction.
Intermediate native recursion placeholders retain their separate path.
Do not apply the original complete-reference codec to those placeholders.

Use actual child/row traces and canonical returned rows to derive
`ProductReadback.members` and `.rejected`. Then apply `product_exact`.
Do not replace these obligations with supplied product-row or language
contracts. Preserve older constructor/equality results and all marked drafts.

## Validation at this checkpoint

The six new modules pass focused checks. The aggregate pinned Lean 4.34.1
build passes 1,263 jobs and 41,364 theorem dependency checks. Only `propext`,
`Classical.choice`, and `Quot.sound` are used.
Log: `/tmp/mcfta-input-exact-20261014-audit.log`.
No Haskell source changed. Prior Nix and formatter results remain the source
validation checkpoint. Earlier proofs, marked drafts, and the counterexample
retain their original bytes. All work remains local.
