# Solver name encoding and quantified capture

The liquid review found a soundness defect in the external name boundary.
Liquid Fixpoint 0.9.6.3.7 prefixes nonalphabetic names before it escapes unsafe
characters. Raw names `1` and `fix$1` both become `fix$36$1`.
The source adapter previously passed raw names directly to that function.

Declare `1 : Int`, then ask whether `Top` entails:

```text
forall fix$1 : Int. 1 = fix$1
```

Here `1` denotes the named variable, not an integer literal. The formula is
false: choose the bound integer to be the free integer plus one. Historical
serialization gives both occurrences the bound name. The submitted formula
is then true. A correct external `Unsat` response to its negation becomes an
incorrect source `Yes`. Renaming the binder to `independent` gives `No`.
The native reproduction returned `(Yes,No)` before the repair.
Log: `/tmp/mcfta-solver-name-collision-20261013.log`.

## Current source encoding

Upstream `1a083040` (PR #117) retains injectivity with a shorter plain-name
branch. ASCII letters, digits, and underscores keep their text after `m_`.
Every other name uses decimal Unicode tokens after `mx`. The second prefix
character distinguishes the branches. All declarations, variables, function
heads, quantified binders, and the default value name use the same map.

`SourceSolverNameFastEncoding` models both source branches. It derives their
exact concatenation equation, complete injectivity, safe characters, keyword
exclusion, and unchanged Fixpoint serialization. The historical numeric name
`1` becomes `m_1`. `fix$1` takes the decimal fallback. Their complete serialized
names differ. ASCII character classification, native Text operations, and the
external symbol implementation remain primitive correspondence boundaries.

`SourceSolverNamePreparation` and `SourceSolverNamePublic` now use this current
encoder. Their generic quantified semantics and preflight proofs retain the
original meaning and all stopping outcomes. `SourceSizedFiniteKeysNativeLiquid`
therefore uses the current actual encoded calls for its exact language, finite
class, order, and both inverse laws. External solver correctness and completion
remain explicit. Checkpoint: `98f633fa`.

## Historical decimal repair

Commit `73223201` encoded each name as `microcfta_name_` followed by its
Unicode character codes in decimal, with an underscore after each code.
The prefix starts with an ASCII letter. Each suffix character is a digit or
underscore. The result avoids reserved keywords and additional escaping.
Declarations, variables, function heads, quantified binders, and the default
value name use this same encoding. No public formula name is changed.
The earlier ambient fresh-name rejection remains in effect. The decimal-only
worker and its proofs remain as historical evidence and supply the current
fallback's token-injectivity proof.

`repro/SolverNameCollision.hs` preserves the quantified example, a separate
binder, two distinct declarations, and a valid quantified identity. The
repaired source returns `(No,No,No,Yes)`.

## Checked meaning and source preparation

`SourceSolverNameEncoding` retains the historical exact concatenation equation, token
recovery, character recovery, and injectivity. It does not assume the main
injectivity obligation. `SourceSolverNameEncodingFixpoint` copies the inspected
keyword, prefix, safe-character array bound, escape, and pad branches.
It proves that encoded names pass through that algorithm unchanged. It also
checks the historical collision and the decimal repair's separation.

`SourceSolverNameSemantics` encodes every emitted expression constructor.
It proves exact term values and predicate meaning under an injective name map.
Universal and existential binders retain their order, sorts, and shadowing.
Declarations use the same map. Every original environment has an extension
to encoded names, so satisfiability and unsatisfiability are preserved in
both directions. Surjectivity of the encoding is not required.

`SourceSolverNameCollision` derives the actual historical prepared request,
including the default value declaration. It proves that the old serialized
request can have a correct Unsat response that does not support the original
entailment. The repaired serialized request has a counterexample, and its
correct Sat response supports the source No. This theorem does not assume
that a solver returns a selected response.

`SourceSolverNamePreparation*` derives actual encoded declaration insertion,
first-sort lookup, reserved-name checks, free-symbol collection, duplicate
removal, and complete request equality. Bound names are removed from the
free-symbol set. Rejection and duplicate declaration positions are preserved.
The list model of HashSet iteration remains an explicit storage boundary.

`SourceSolverNamePublic` models actual encoded call occurrences. It proves
exact equality with the preceding call relation under a translated external
check. Correct encoded Sat/Unsat answers derive the original response law.
`public_correct` then proves the independent accepted language, canonical
bounded sequence, distinct size order, and both signed rank inverse laws.
`public_finite` gives finite outcomes from finite external attempts, including
Unknown and raised failures. No stable external reply function is assumed.
Proof checkpoints: `f66aaca2` and `ea951af6`.

## Current validation and boundaries

After the PR #117 refresh, all 641 examples pass in Nix: 289 core, 208 generator,
and 144 refinement. The new upstream collision regression passes. Fourmolu
and active-package cabal-gild pass. The broad gild command also reports
formatting failures in unchanged legacy microecta package files.
Logs: `/tmp/mcfta-producer-refresh-20261014-tests.log`,
`/tmp/mcfta-producer-refresh-20261014-format.log`, and
`/tmp/mcfta-producer-refresh-20261014-active-gild.log`.
The aggregate audit passes 1,327 jobs and 42,214 dependency checks with only
`propext`, `Classical.choice`, and `Quot.sound`.
Log: `/tmp/mcfta-fast-name-refresh-20261014-audit.log`.

The earlier validation record is historical:
The repaired source passes 285 core, 206 generator, and 144 refinement
examples in Nix. The native reproduction passes after those suites.
Log: `/tmp/mcfta-solver-name-repair-20261013-tests.log`.
Fourmolu and cabal-gild pass in Nix.
Log: `/tmp/mcfta-solver-name-repair-20261013-format.log`.
No production test was added. The aggregate audit passes 1,180 targets and
39,689 theorem dependency checks. Only the three standard Lean foundations
are permitted. Log: `/tmp/mcfta-closing-20261014-audit.log`.

The codec proof models Unicode scalar values, decimal rendering, and the
inspected serializer control flow. It does not verify the external Text,
HashSet, Array, symbol interning, SMT theory implementation, process protocol,
or clock. Correct external Sat/Unsat answers and finite external attempts
remain separate contracts. The repair removes the demonstrated name capture;
it does not establish whole external-solver verification.
