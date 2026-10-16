# Derive frontend refresh at 78618ea2

Upstream main `78618ea26f186aa4768b4b854e9664ca2680bdf1` merges PR 50.
Local merge `454753832614470f382f50a5a675af749bca43c8` retains the existing
proof history and equality repair. Native intersection, conjunction emptiness,
Typing, and `Derive.Internal` source files are unchanged by this refresh.

## Current source behavior

`literal` now has type `(Literal a, Num e) => a -> e`. It still computes
`fromInteger . toLiteral`. Its `Expr` specialization is unchanged. Integer
values can use the same literal as symbolic invariant expressions.

`deriveLTARooted` and `deriveLTAFromRooted` add a root condition after successful
derivation. They use `satisfying` with `condition . rootMeasures rules`.
`Measured` exposes `Single value`, `Contracted` exposes `NoMeasures`, and
`MeasuredBy` exposes `measuresAt value`. `holdsRooted` first checks `holds`.
Only a successful check evaluates the root condition on concrete measures.
Logic classes, operators, helpers, and `literal` are re-exported by Derive.

`checkNodeView` retains constructor-count and field-shape validation first.
It checks every shape before the new name phase. That phase requires the
node-view constructor name at each position to start with the datatype's
constructor name. It reports the first mismatch in declaration order.
The rule is a case-sensitive string prefix. It has no delimiter condition.
`AnyNode` has no shape and bypasses the validation.

## Checked new phase

`SourceDeriveNodeViewNames` models the final name phase over its original
ordered name pairs. The character prefix test is equivalent to independent
suffix extension. Success requires every supplied pair to satisfy that law.
Failure retains its exact position, earlier passing pairs, and literal source
diagnostic. `afterShape` preserves every earlier shape error.

This does not extract Generic metadata or derive the earlier shape result.
It does not prove `nodeShape`/`buildNode` coherence, schema meaning, codec
inverses, or rooted symbolic/concrete measure agreement. Prefix acceptance
alone does not establish unique constructor association. The checked pairs
`A`/`AB` with `ABC1`/`ABC2` both pass. This is a scope boundary, not an observed
source correctness defect. The separate `AnyNode` branch is not modeled here.

The previous measure evaluator and folding laws remain useful components.
The new rooted entry still needs the measure, root-condition, and codec laws
that connect its symbolic and concrete interpretations. General `Num`
embedding and Haskell defaulting also retain their representation boundaries.

The typing helper-order disagreement remains in main. The fetched
`fix/typing-helper-order` branch is separate and has not been merged here.

## Validation

The strict Nix build passes for all components, tests, and benchmarks.
All six existing suites pass: 320 core, 224 generator, 167 refinement,
34 GHC fit, and 22 decision-model examples, plus the hole-fit golden check.
Fourmolu checks all four changed Haskell files using the updated fixities.
Cabal-gild checks the four active packages. No new test file is committed.

The new name-phase focused build and eight axiom/signature probes pass.
Eight direct kernel examples check first mismatch, diagnostic text, valid
suffixes, case sensitivity, earlier shape errors, overlapping prefixes,
repeated names, and the empty list. Aggregate validation is recorded in
[the query checkpoint note](notes-current-allocated-query-memo.md).
