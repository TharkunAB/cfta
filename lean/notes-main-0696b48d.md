# Source main 0696b48d

Main `0696b48d` merges PR #42, preorder-prefix exclusion.
Merge `f780009a` retains the formalization and earlier local equality repair.
The upstream delta has three files: Template.hs, SimpleSpec.hs, and the changelog.
The equality, Sized, constructor, and interned source bodies are unchanged.

## Prefix exclusion

`excludePrefixesFTA` builds a minimal automaton of symbol/arity prefix words.
A product state retains a source state and entry/optional-exit positions.
The source preserves transition annotations and claims one retained copy
for each retained source run.

`SourceCurrentPrefixExclusion` proves the token monitor component.
Rejection is equivalent to completion of a supplied prefix word.
An initial empty word rejects before token consumption.
Missing continuations have the future token behavior of `Free`.
Every nonfree residual step strictly decreases the finite prefix depth.
Actual term tokens retain the symbol and signed child count.
Negative-arity words cannot prefix a finite term.
Successful child traversal has a unique ordered sequence of boundary states.

This residual monitor is not the literal minimized Map/IntMap representation.
The proof does not establish source DAG extraction, physical position IDs,
`endsOf`/`copies`/`walk` completion, or the complete source run-copy bijection.
In particular, `endsOf _ Free` returns `{Free}` even for an unproductive state.
Its results cannot be specified as exact productive end positions without
qualification. The copy proof must use actual child runs and unique boundaries.

## Confirmed template-equivalence domain

The source advertises equivalence with `excludeFTA (map preorderPrefix prefixes)`.
That equivalence needs valid partial tree preorders.
For a singleton leaf `a` and the malformed word `[(a,0),(b,0)]`, the new
operation retains `a`. The template route removes it.
The template parser consumes the complete first tree and ignores the suffix.
The literal word-prefix contract is correct in this example.
No source behavior was changed for this domain caveat.

The exact source comparison is preserved in
`/tmp/mcfta-prefix-exclusion-source-probe-20261016.{hs,sh,log}`.
A separate bounded cyclic binary source probe agrees with literal filtering
for no prefixes, an empty prefix, a continuing binary prefix, and negative arity.
Those finite observations do not prove general source correspondence.

## Validation

The required strict Nix build passes all libraries, executables, tests, and
benchmarks with `-Werror`. All six suites pass 745 examples plus the golden check.
Fourmolu passes both changed Haskell files. Cabal-gild passes all four packages.
No new test file was committed. The source tests came from the upstream merge.
Evidence uses `/tmp/mcfta-memo-shared-haskell-*` and
`/tmp/mcfta-prefix-exclusion-*`.
