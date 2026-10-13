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

## Source repair

Commit `73223201` encodes each name as `microcfta_name_` followed by its
Unicode character codes in decimal, with an underscore after each code.
The prefix starts with an ASCII letter. Each suffix character is a digit or
underscore. The result avoids reserved keywords and additional escaping.
Declarations, variables, function heads, quantified binders, and the default
value name use this same encoding. No public formula name is changed.
The earlier ambient fresh-name rejection remains in effect.

`repro/SolverNameCollision.hs` preserves the quantified example, a separate
binder, two distinct declarations, and a valid quantified identity. The
repaired source returns `(No,No,No,Yes)`.

## Checked meaning and source preparation

`SourceSolverNameEncoding` derives the exact concatenation equation, token
recovery, character recovery, and injectivity. It does not assume the main
injectivity obligation. `SourceSolverNameEncodingFixpoint` copies the inspected
keyword, prefix, safe-character array bound, escape, and pad branches.
It proves that encoded names pass through that algorithm unchanged. It also
checks the historical collision and the repaired separation.

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

## Validation and boundaries

The repaired source passes 285 core, 206 generator, and 144 refinement
examples in Nix. The native reproduction passes after those suites.
Log: `/tmp/mcfta-solver-name-repair-20261013-tests.log`.
Fourmolu and cabal-gild pass in Nix.
Log: `/tmp/mcfta-solver-name-repair-20261013-format.log`.
No production test was added. The aggregate audit passes 1,140 targets and
39,108 theorem dependency checks. Only the three standard Lean foundations
are permitted. Log: `/tmp/mcfta-native-liquid-20261013-audit.log`.

The codec proof models Unicode scalar values, decimal rendering, and the
inspected serializer control flow. It does not verify the external Text,
HashSet, Array, symbol interning, SMT theory implementation, process protocol,
or clock. Correct external Sat/Unsat answers and finite external attempts
remain separate contracts. The repair removes the demonstrated name capture;
it does not establish whole external-solver verification.
