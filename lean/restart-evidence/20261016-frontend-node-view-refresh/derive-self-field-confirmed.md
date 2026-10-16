# Confirmed recursive field-atom behavior

Recorded on 2026-10-16 at 13:11 CEST. No source repair was made.
The intended policy remains unresolved.

## Executed evidence

Root executed this exact command in the project Nix environment:

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc -package=cfta -package=cfta-generator lean/restart-evidence/20261016-frontend-node-view-refresh/derive-self-field-draft.hs' > lean/restart-evidence/20261016-frontend-node-view-refresh/derive-self-field-retry.log 2>&1
```

Tool process 73352 reached terminal exit 0. The output is:

```text
(field holds, type-wide holds, independent all-node invariant):
(True,True,False)
High-level field-local derivation status:
Right ()
High-level type-wide replacement status:
Left (UnknownConstructors ["End","Next"] [])
Field-local generated values and independent validity:
Right [(End True,True),(Next (End False),False)]
```

The first attempt failed because the sandbox could not open
`/nix/var/nix/db/big-lock` on its read-only mount. The retry obtained access
and succeeded. That first failure is an environment error, not a source or
reproducer failure. Both raw logs remain.

The frozen draft SHA256 is
`aca168328f288fedf671fc30a535bf5d4643aeaed1662f3bd214936f663ee8ac`.
The successful raw-log SHA256 is
`634dfe6fb19f22766aa07eb3feb2e7a70bf0df6f94e4d8394666d4d9deb47c75`.
The earlier audit and draft remain unchanged. Their historical statement
that the draft had not run was correct when written; this note records the
later execution.

## What is confirmed

The invariant requires `End` to contain True and accepts each `Next` node.
The independent recursive predicate rejects `Next (End False)`. The current
public derivation nevertheless generates that value and `holds` accepts it.
This is a concrete mismatch with an unrestricted reading of the documented
contract at every node of the datatype (`Derive.hs:699–701`).

The behavior follows the implemented atom boundary. A field pool is chosen
before the derived generator (`Internal.hs:339–345`). During value checking,
the selected field is assigned `below=True` and its Literal integer; its
subtree is not evaluated recursively (`Derive.hs:757–763`). The supplied
Chain Literal encoding is injective and has a round trip on its declared
nonnegative range. The counterexample does not depend on a broken codec.

This does not establish that opaque replacement is unintended. Type-wide
atoms already replace derived types (`Internal.hs:178–182`), and old `holds`
also skips their children. The new field-local path leaves the root datatype
derived. The old type-wide root replacement cannot be used with this
high-level invariant: its Constructor annotations become unknown. These
are different accepted API domains, as the output demonstrates.

## Minimal choices for an external repair

1. **Keep the all-node contract; reject direct self-type field pools.**
   This is the smallest validation change that excludes this example and
   preserves ordinary Int field pools. Validate the field's actual type
   against the root datatype. Do not call it a type mismatch: the supplied
   type is correct. A separate unsupported-recursive-pool diagnostic would
   describe the issue. Validate at the derivation boundary too if direct
   construction of the exposed internal Atoms record remains in scope.
   Align `holds` validation or state the same input restriction for it.
   This deliberately removes a currently accepted opaque-pool use.
2. **Keep self-type pools and enforce all-node validity recursively.**
   Filtering supplied members requires a separate recursive evaluator that
   does not skip the same pool boundary. It must also retain the supplied
   pool's membership, order, symbolic constraints, and error behavior.
   Filtering with the current `holds` function does not repair this example.
   For measured invariants, mere predicate filtering is insufficient:
   the Literal integer at the boundary must agree with the required child
   measure. Named measures require their own readback law. This is a larger
   semantic change, and termination/counting of symbolic pools needs proof.
3. **Keep opaque replacement; narrow the advertised contract.**
   State that contracts apply at derived nodes and that selected atom
   subtrees are opaque. Describe their Literal integer as distinct from
   recursively computed measures. This is the smallest implementation
   change, because it needs no runtime change. It changes the stated
   all-node guarantee. It must be an explicit policy decision, not a proof
   that the current output satisfies the original independent predicate.

No option is selected by this note. If the all-node contract is retained,
option 1 is the smallest defensible code change for the direct self-type
case. If constructed-type pools are deliberately opaque, option 3 describes
the observed policy. Option 2 preserves the broadest API but requires the
most new behavior and proof work.

## Explicit proof domain until policy is resolved

A small adapter can retain the existing all-node theorem on a restricted
input domain: the root datatype has no type-wide atom, and no selected
field atom replaces a recursive field of that root datatype. This is a
checkable input restriction, not an assumed result-language theorem.

For an all-node claim across arbitrary helper datatypes, a direct self-type
restriction alone is insufficient. An opaque helper may itself contain the
root datatype. Require that no root-type occurrence is reachable below an
opaque field, or prove a local independent admissibility contract for each
supplied pool. If self-type pools remain allowed, such a pool contract also
needs Literal/measure readback compatibility. These are external input laws;
the current source does not derive them.

An alternative Lean model can specify opaque-boundary semantics directly.
It must name that semantic domain. It cannot present the unrestricted
all-node invariant as established by this repro or by the existing tests.

## Handoff status

Source main: `999c04a5`; field-atom introduction: `d0966953`.
Affected implementation: `cfta-generator/src/Data/CFTA/Gen/Refinement/Derive.hs`
and `Derive/Internal.hs`. Existing Int-pool regressions remain valid.
Behavior confirmed by the standalone repro. No implementation patch, test
patch, commit, or upstream issue is created here. Root owns the FINDINGS.md
entry and any later policy or source-change handoff.
