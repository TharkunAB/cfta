# cfta-lean

Use Lean as an LTA solver through the
[Kimina Lean server](https://github.com/project-numina/kimina-lean-server).
The package implements cfta's `Entailment` interface. It does not start a
Lean process. Kimina runs Lean and reuses imported Mathlib environments.

## Queries and answers

`withKimina` takes the server options, declarations, and ambient assumptions.
For each query it closes the implication over its declared and free values. It sends two
complete proofs to `/api/check` in one batch: the implication and its negation.

- A checked implication gives `Yes`.
- A checked negation gives `No`. This proves that a counterexample exists.
- Unsupported formulas, unfinished proofs, failed tactics, timeouts, HTTP
  failures, and malformed responses give `Unknown`.

A failed proof never means `No`. Results must have the two requested IDs.
An accepted Lean response must have an environment ID, no errors, and no
`sorry`. If both propositions appear to pass, the result is `Unknown`.

The fixed tactic portfolio uses `simp_all` followed by `decide`, `omega`,
`norm_num`, `decide`, `nlinarith`, and `grind`. It also tries the integer witnesses 0, 1, and -1 for negated
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

For the original arithmetic vocabulary, use both solvers under the same
declarations and assumptions:

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

## Typed refinements and solver lowering

`Formula` keeps the shared logical structure. `Predicate Name [Term]` adds a
global predicate application. `NamedSort Name [Sort]` adds a named type.
The formula contains no Lean source. A fixed `Theory` supplies signatures
and interpretations:

```haskell
import qualified Data.CFTA.Lean as Lean

listInt = NamedSort "List" [IntSort]
theory =
    [ ("List", Lean.TypeConstructor 1 "List")
    , ("reverse", Lean.Function [listInt] listInt "List.reverse")
    , ("sorted", Lean.Predicate [listInt]
        "(fun xs : List Int => xs.Pairwise (· ≤ ·))")
    , ("nonnegative", Lean.Defined [("x", IntSort)]
        (Atom Ge (Var "x") (Lit 0)))
    ]
```

`withTheory options theory declarations assumptions` checks these obligations
through Kimina. Native interpretations are trusted Lean expressions. Shared
`Defined` predicates have bodies in the common logic. Definitions refer to
earlier theory entries. Predicate names are global; value substitution changes
only their arguments.

`lower theory declarations formula` validates the original formula and expands
shared predicates without variable capture. It returns `Either String Formula`.
The successful result has the same meaning in the supported SMT fragment.
Native Lean functions, native predicates, and named data sorts are rejected.
This is a partial translation of the shared logic, not a compiler for arbitrary
Lean source. The current shared fragment has integer and Boolean values.

For a typed theory, use `withLowering` before Kimina. Do not pass native
functions directly to `withZ3`: it would assign them uninterpreted meanings.
Use the same context on both sides:

```haskell
Lean.withLowering theory declarations assumptions $ \z3 ->
    Lean.withTheory Lean.defaultOptions theory declarations assumptions $ \lean ->
        useSolver (Lean.fallback z3 lean)
```

Every declared value remains in the Lean proposition, even if simplification
removes its uses. A named Lean type can be empty. Dropping such a binder can
change validity. Solver lowering therefore rejects a context that contains a
named data sort, including an unused declaration.

Replacing native functions with uninterpreted SMT symbols would be an
approximation. A countermodel could violate their definitions. This spike
refuses that translation instead of returning a false `No`.

## Save and reload a language

`Data.CFTA.Lean.Serialization` stores a `Snapshot` with two parts:

- `snapshotLanguage`: the editable language, including ordered productions,
  named facts, and exclusions from `cfta-serialization`.
- `snapshotContext`: the theory, value declarations, and ambient assumptions.

`printSnapshot` writes a `lean-language 1;` envelope. The context uses derived
`Show` and `Read`; the language uses the standard readable language format.
The format preserves named sorts and predicate applications. `parseSnapshot`
checks the language structure without contacting a solver. Native definitions
remain trusted Lean code when the loaded language is queried.

Use the same Lean and Mathlib deployment for replay. Native definitions refer
to that environment. Standard Kimina does not expose its complete identity.
The snapshot does not contain libraries, Haskell functions, solver caches, or
proof results. Server options remain a runtime choice.

## Running example

Find every program in this finite grammar whose result is a sorted permutation
of `[1,2]`:

```text
chunk   ::= [] | [1] | [2] | [1,2] | [2,1]
program ::= chunk | reverse chunk | append chunk chunk
```

There are 35 candidate programs. The saved `Language` gives each production
its exact list value as a refinement. Its `answer` production has two named
facts: `sorted` and `permutation`. The theory interprets these predicates as
Lean's `List.Pairwise (· ≤ ·)` and `List.Perm [1,2]`.

`refinement-logic-spike dump FILE` writes the source and context, reads them
back, and checks exact equality before solving. `reload FILE` queries only
the source and context from the file. It does not rebuild the source from the
Haskell definitions. Both commands use `Language.compileGraph` followed by
`Sized.sizedUpTo`, which keeps the source graph's rank order.

Run from the repository root with a Kimina server on port 8000:

```sh
export XDG_RUNTIME_DIR=/run/user/1000
export DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus
~/Code/heavy-management/bin/heavy --mem 8G --time 20m \
  nix-shell --run 'z3_bin=$(dirname "$(command -v z3)"); export PATH="$z3_bin:/usr/bin:$PATH"; cabal run refinement-logic-spike -- dump /tmp/list-programs.language +RTS -M2G -RTS'
~/Code/heavy-management/bin/heavy --mem 8G --time 20m \
  nix-shell --run 'z3_bin=$(dirname "$(command -v z3)"); export PATH="$z3_bin:/usr/bin:$PATH"; cabal run refinement-logic-spike -- reload /tmp/list-programs.language +RTS -M2G -RTS'
```

The example checks the five accepted programs against a separate Haskell
interpreter. It checks every `(size, class rank)` inverse and 32 uniform
samples with a fixed seed. A small explicit decoder reconstructs programs
from their constructor labels. The decoder and independent checks are part
of the executable; they are not serialized.

The loaded theory also supplies `between`, which lowers to integer comparisons
and runs through Z3 in a separate scalar context. Native list queries use
Kimina. The example checks that `[2,1]` is not sorted and that reversing an
arbitrary list twice returns the original list. Unresolved obligations remain
`Unknown`, and exact enumeration reports an error.

The example uses one observed value type, `List Int`. Mixed observed value
sorts remain outside this spike. See the
[complete snapshot](../docs/lean-spike/list-programs.language) and
[results](../docs/lean-spike-generalized.md).

## Formula subset

The translator supports:

- Integer, Boolean, and named values, and fully applied first-order functions
  over these values. A theory can define functions and predicates.
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

`entailmentProposition` exposes the original translation as `Either String Text`.
`renderEntailment` also takes a theory and returns the definition prefix and
closed proposition. Use these functions to inspect a query or the reason
that a formula is unsupported. For typed theory definitions, use `withTheory`. See the
[generalized refinement spike](../docs/lean-spike-generalized.md) for results
and remaining boundaries.

## Validation

The existing `lean-tests` suite now checks entailment and LTA integration.
Without `CFTA_KIMINA_URL`, only the live checks are pending. If the variable
is set, a failed connection fails the checks.

On the WSL2 development host, use the shared memory-limited runner:

```sh
CFTA_KIMINA_URL=http://127.0.0.1:8000 \
  ~/Code/heavy-management/bin/heavy --mem 8G --time 20m \
  nix-shell --run 'z3_bin=$(dirname "$(command -v z3)"); export PATH="$z3_bin:/usr/bin:$PATH"; cabal test cfta-lean -j1 --ghc-options=-Werror --test-show-details=direct --test-options="+RTS -M1G -RTS"'
```

The Nix shell supplies Z3. The host compiler path avoids the local Nix
linker's GMP lookup failure. The client does not require a local Lean or
Lake installation.

The previous synthesis and tactic implementation remains in the merged
`lean-spike` history at `3ab4caa6`. Its measurements are historical.
See [the restart notes](../docs/lean-spike.md) for scope and remaining work.
