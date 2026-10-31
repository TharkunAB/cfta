# Tune a generator with Loaded Dice

This example tunes an existing recursive list generator toward a requested
length distribution. CFTA sums the probability of each length and its
derivatives. The example then samples ordinary lists and prints ranks that
replay them. A direct `Gen.frequency` baseline shows what to use when the
caller can choose the length before generating the elements.

The executable uses public CFTA APIs. Its small KL objective and gradient
descent implementation are private example code, not a new library API.

## Run and replay

From the repository root, build `cfta-generator:cfta-loaded-dice`. The
commands are `demo`, `check`, `replay cfta RANK`, and `replay direct RANK`.
With no arguments, the executable runs `demo`.

From a repository checkout, use the project's `nix-shell`:

```sh
nix-shell --run 'cabal build cfta-generator:cfta-loaded-dice -j1'
nix-shell --run 'cabal run cfta-generator:cfta-loaded-dice -- demo +RTS -M2G -RTS'
nix-shell --run 'cabal run cfta-generator:cfta-loaded-dice -- check +RTS -M2G -RTS'
```

For an unpacked source package, run the corresponding `cabal` commands
directly in an environment with the package's declared dependencies.
Repository maintainers must also use their usual process memory cap and
serial job workflow. The commands above set a 2 GiB Haskell heap limit.

The demo prints replay lines such as `replay cfta RANK => [...]`. Pass the
printed rank to the same executable, for example by replacing `demo` in
the run command with `replay cfta RANK`. Use a printed integer for `RANK`.
Replay does not train or draw again. `cfta` and `direct` have different rank
spaces. Keep the generator definition, alphabet, and length bound unchanged
when replaying a stored rank. Changing the CFTA weights alone preserves its
ordinary term ranks.

Each method draws 10,000 lists with seed 1729. The CSV compares exact class
probabilities, displayed as rounded decimals, with observed counts. The
same dependency versions reproduce the seeded draw sequences. Rank replay
uses `unrankCompletion` or `Gen.unrank` and does not depend on the random seed.
The weighted-rank sampler uses a different seeded sequence from the earlier
transition-by-transition sampler. Its probabilities and ordinary replay
ranks are unchanged. Weighted sampling tickets are not ordinary replay ranks.

## What the paper example does

The list generator has fuel five. At each positive fuel value, it stops with
probability `sigmoid(logit)` or emits a uniform element from 0 through 9 and
continues with one less fuel. Fuel zero forces a stop. The five logits start
at zero, so the initial length masses are
`1/2, 1/4, 1/8, 1/16, 1/32, 1/32`.

The target assigns mass 0.3 to length 0, 0.2 to length 2, and 0.5 to length 5.
The loss is `KL(target || generated lengths)`. The reference uses 1,000
gradient-descent updates at rate 0.3, with no prior or pseudo counts. Its
expected final loss is approximately `0.010197463842` nats. The final mass
of length five is approximately 0.490855, compared with 0.03125 initially.
These are reference values, not claims about the published bug-finding runs.

`listEvent` compiles one automaton for each length. `completionWeightBy`
evaluates its count table with `Train.Dual` weights to get the event mass
and its gradient. The model sums over element choices without listing all
lists. This keeps the original local stopping parameters. `Train.distill`
instead fits globally normalized symbol weights to a corpus; that is a
different objective and parameterization.

For sampling, `rationalWeights` converts each finite sigmoid result to
`Rational` once and computes `1 - stop` in `Rational`. The two choices then
sum to exactly one. The sigmoid itself was evaluated in `Double`.
After `withWeights`, `weightedTotal` gives an integer ticket count.
`unrankWeighted completions` supplies a decoder that retains its tables.
The example keeps both values outside the draw loop, draws a uniform ticket,
and decodes it. Each term has an interval proportional to its rational
weight. A language with total mass zero returns an error.

## When direct class control is enough

`directGenerator` uses the existing public combinators:

```haskell
listsOfLength n = replicateM n (Gen.elements [0 .. 9])
targeted = Gen.frequency
    [(3, listsOfLength 0), (2, listsOfLength 2), (5, listsOfLength 5)]
```

Each branch draws uniform elements. Its length has the requested probability
exactly, with no training. This is the simpler choice when the caller can
select the class first. Tuning is useful when the existing generator exposes
local choices and must retain that structure. The example compares their
distributions; it does not claim that tuning has a performance advantage.

The complete implementation checks positive target weights, class presence,
and nonempty branches before calling `Gen.frequency`. This check matters:
`Gen.frequency` normally removes empty alternatives and renormalizes the
remaining ones. A missing requested class would otherwise change the target.
For an existing grouped language, `Gen.atKey` selects a class. `Gen.keyed`
can declare known classes without enumeration. `Gen.groupOn` classifies a
finite generator by enumerating its outcomes.

## Customize and check

- Change `requestedWeights` in `ListGenerator.hs` to select other lengths
  and relative frequencies. Omit classes whose target mass is zero. A
  requested class outside the supported bound is an error.
- Change `maximumLength` or `alphabetSize` to change the language. The
  ordinary ranks can change. Update the reference KL assertion in `check`
  when changing the paper's settings or its fixed optimization schedule.
- Keep a label for each probabilistic choice when different paths can
  produce the same output. Sum their masses before computing output
  objectives. CFTA distinct-term counting does not count multiple accepting
  runs as multiple terms. Here the fuel labels are determined by each list;
  the length events sum all lists of that length.

`check` verifies exact rational total mass, the reference KL result, exact
direct class probabilities, missing-class rejection, sampled list bounds,
and both rank replay paths. It also checks weighted interval endpoints and
their exact probabilities. The direct `Gen.pmf` check enumerates its finite
support, which has 100,101 lists at the reference settings. That check can
become expensive when the alphabet or length bound grows. The example does
not compile arbitrary Haskell generators or choose a target from test failures.

## Source and reproduction boundary

The source is Tjoa et al.,
[Tuning Random Generators: Property-Based Testing as Probabilistic Programming](https://web.cs.ucla.edu/~todd/research/oopsla25a.pdf),
OOPSLA 2025. The concrete reference is
[`demo_natlist.jl`](https://github.com/Tractables/Alea.jl/blob/fdc3ab864f4579918f2ef5a527e9c86b6866ab55/pbt/pbt_examples/demo_natlist.jl)
at commit `fdc3ab864f4579918f2ef5a527e9c86b6866ab55`.
The reference repository uses
[Apache-2.0](https://github.com/Tractables/Alea.jl/blob/fdc3ab864f4579918f2ef5a527e9c86b6866ab55/LICENSE).
This Haskell example independently implements that objective and update
schedule. It does not copy Julia source.

The [archived artifact](https://doi.org/10.5281/zenodo.16868014) has not been
run for this example. This is a reproduction of the small list objective
and parameterization, plus a CFTA sampling and replay recipe. It does not
reproduce the full benchmark suite or establish comparative performance.
