# cfta-lean

Use Lean as an LTA solver through the
[Kimina Lean server](https://github.com/project-numina/kimina-lean-server).
The package implements cfta's `Entailment` interface. It does not start a
Lean process. Kimina runs Lean and reuses imported Mathlib environments.

## Queries and answers

`withKimina` takes the server options, declarations, and ambient assumptions.
For each query it closes the implication over its free names. It sends two
complete proofs to `/api/check` in one batch: the implication and its negation.

- A checked implication gives `Yes`.
- A checked negation gives `No`. This proves that a counterexample exists.
- Unsupported formulas, unfinished proofs, failed tactics, timeouts, HTTP
  failures, and malformed responses give `Unknown`.

A failed proof never means `No`. Results must have the two requested IDs.
An accepted Lean response must have an environment ID, no errors, and no
`sorry`. If both propositions appear to pass, the result is `Unknown`.

The fixed tactic portfolio uses `omega`, `norm_num`, `decide`, `nlinarith`,
and `grind`. It also tries the integer witnesses 0, 1, and -1 for negated
implications. This is an incomplete proof search. A satisfiable formula can
still give `Unknown`.

## Use

Start a Kimina server with Mathlib. The default URL is
`http://127.0.0.1:8000`. The client uses HTTP and has no authentication setup.

```haskell
{-# LANGUAGE OverloadedStrings #-}

import Data.CFTA.Formula
import Data.CFTA.Lean
import Data.CFTA.Refinement.Verdict

main :: IO ()
main =
    withKimina defaultOptions [] [] $ \solver -> do
        let positive = Atom Gt (Var "x") (Lit 0)
            nonnegative = Atom Ge (Var "x") (Lit 0)
        entails solver positive nonnegative >>= print
```

To try Z3 first, use both solvers under the same declarations and assumptions:

```haskell
withZ3Assuming declarations assumptions $ \z3 ->
    withKimina defaultOptions declarations assumptions $ \lean ->
        useSolver (fallback z3 lean)
```

`fallback` calls the second solver only after `Unknown` or
`TimeLimitReached`. It preserves fresh bindings. Other exceptions propagate.
The LTA operations use the resulting `Entailment` without an API change.

`optionTimeoutSeconds` sets Kimina's proof timeout. The HTTP timeout also
allows for queueing and imports. The generated proofs have a fixed heartbeat
limit. Set the server's worker and total memory limits separately.

## Formula subset

The translator supports:

- Integer and Boolean values, and fully applied first-order uninterpreted
  functions over these values.
- Every formula connective, comparison, and quantifier. Ordered comparisons
  require integers.
- Integer literals, negation, addition, subtraction, multiplication, and
  conditional terms.
- Integer division and remainder with positive literal divisors. Lean and
  SMT integer division agree on this subset.

Reals, casts, higher-order sorts, and other divisors give `Unknown`.
An undeclared value has integer sort. An undeclared function takes integers
and returns an integer. Invalid sorts and inconsistent arities are rejected.

Fresh bindings copy sorts. They do not equate values. A fresh name cannot
shadow a declaration, the distinguished value name, or a free name in an
ambient assumption. Generated identifiers replace source names, and
quantifiers retain their lexical scope.

`entailmentProposition` exposes the translation as `Either String Text`.
Use it to inspect a query or the reason that a formula is unsupported.
Defined measures and new data sorts remain outside this spike.

## Validation

The existing `lean-tests` suite now checks entailment and LTA integration.
Without `CFTA_KIMINA_URL`, only the live checks are pending. If the variable
is set, a failed connection fails the checks.

On the WSL2 development host, use the shared memory-limited runner:

```sh
CFTA_KIMINA_URL=http://127.0.0.1:8000 \
  ~/Code/heavy-management/bin/heavy --mem 8G --time 20m \
  nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test cfta-lean -j1 --ghc-options=-Werror --test-show-details=direct --test-options="+RTS -M1G -RTS"'
```

The Nix shell supplies Z3. The host compiler path avoids the local Nix
linker's GMP lookup failure. The client does not require a local Lean or
Lake installation.

The previous synthesis and tactic implementation remains in the merged
`lean-spike` history at `3ab4caa6`. Its measurements are historical.
See [the restart notes](../docs/lean-spike.md) for scope and remaining work.
