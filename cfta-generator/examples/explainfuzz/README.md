# Learn, condition, and sample query tests

`cfta-explainfuzz` is a small consumer example of the existing CFTA training,
intersection, weighted ranking, and sampling APIs. It learns a distribution
from example query ASTs. A separate structural requirement then restricts
the output language. Sampling retains the learned relative weights of the
remaining queries.

## Correspondence with ExplainFuzz

The reference is Baiget et al.,
[ExplainFuzz: Explainable and Constraint-Conditioned Test Generation with Probabilistic Circuits](https://arxiv.org/abs/2604.06559v1),
version 1, 2026-04-08. The paper compiles a bounded CFG into a probabilistic
circuit with production, span, and split structure. It trains that circuit
and supports conditional generation. This example adapts the
learn/inspect/condition/sample workflow to CFTA's finite tree distribution.
It does not reproduce the paper's circuit construction, parse-latent
training, token-span queries, or reported fuzzing results.

The public [artifact](https://github.com/niMgnoeSeeL/ExplainFuzz) was checked
on 2026-10-31. Its [.gitmodules](https://github.com/niMgnoeSeeL/ExplainFuzz/blob/main/.gitmodules)
still names `jjcmoon/cfg2pc` as the circuit compiler and trainer. The GitHub
API returned 404 for that repository. The public wrapper and
[requirements](https://github.com/niMgnoeSeeL/ExplainFuzz/blob/main/requirements.txt)
were available. They include ANTLR, PyTorch, Klay, and domain concretizers.
This example neither installs those dependencies nor claims to validate
the unavailable core implementation.

## The finite language

The query grammar has 45 ASTs and a maximum of eight nodes. A query has an
optional filter and an optional grouping clause. The filter is `active`,
or `salary` above 10, 50, or 100. Grouping uses `department` or `role`, with
optional `HAVING COUNT(*)` above one of those numbers. The grammar permits
`HAVING` only inside grouping. Every AST renders to a distinct SQL statement.

The generated statements target this schema:

```sql
CREATE TABLE employees (
    department VARCHAR,
    role VARCHAR,
    active BOOLEAN,
    salary INTEGER
);
```

The example does not open a database or execute the statements. Its checks
validate the grammar, rendering, and probability calculations. They do not
replace a target database's parser or semantic checks.

`corpus` contains 125 query occurrences from six explicit ASTs. Repetition
expresses frequency. Edit those examples to change the training data. The
example accepts no arbitrary SQL text and contains no SQL parser.
`Train.distill` fits parent and left-sibling potentials with `Reach 1 True`.
The wrapper rejects empty, invalid, and oversized training corpora before
calling the fitter. The fit uses the library's L2 prior and uniform pseudo
terms. It is a numerical fit, not exact maximum-likelihood arithmetic.

## Exact conditioning

Let `w(t)` be the product of the rational node potentials of a labelled term.
Let `Z` be the sum of `w(t)` over the 45 queries. For a structural event `E`:

```text
P(E)     = Z_E / Z
P(t | E) = w(t) / Z_E = P(t) / P(E), for t in E
P(t | E) = 0,                         for t outside E
```

`condition` uses `FTA.intersectWith` to intersect the labelled grammar with
the event grammar. Its symbol callback keeps the original labelled symbol.
The restricted grammar therefore reads the same learned weight map. It does
not fit a new model, reset weights, or use rejection sampling.

The supported requirements are `any`, `grouped`, `filtered`, and
`grouped-filtered`. `impossible` constructs an empty event to demonstrate
the error path. A zero-mass event returns an error and produces no samples.

`Train.withLogWeights` approximates each exponential potential by a rational
number within the library's relative tolerance of `1e-9`. Event masses,
conditional probabilities, and weighted rank intervals are exact for those
rational potentials. They are not exact arithmetic for the original real
exponentials. Displayed probabilities are rounded to nine decimal places.

Sampling draws one uniform integer below `weightedTotal`, then calls a
retained `unrankWeighted` decoder. A fixed seed replays the same sequence
with the same corpus, bound, fitted weights, and QuickCheck version.

## Ambiguous outputs

The query example has one AST per rendered SQL output. It therefore needs
no parse-mass aggregation. That boundary matters: CFTA's completion APIs
count a term once even when several automaton runs accept that same term.
They are not a sum over the grammar's parse derivations.

A separate tiny fixture makes each derivation an explicit tree. Two trees
render to `x` and have masses 2 and 3; one renders to `y` and has mass 1.
It builds those trees with `FTA.fromTerms`, applies their node weights, and
adds probabilities by rendered output. The result is `P(x) = 5/6` and
`P(y) = 1/6`. Removing the duplicate `x` output before summing would lose
probability mass. A general ambiguous CFG consumer must define and preserve
that derivation-to-output mapping; this example supplies no general parser.

## Run and check

Run these commands from the repository root. Use the process memory cap
for your development environment. The checks also set a 2 GiB RTS heap limit.

```sh
nix-shell --run 'cabal build cfta-generator:cfta-explainfuzz'
nix-shell --run 'cabal run cfta-generator:cfta-explainfuzz -- check +RTS -M2G -RTS'
nix-shell --run 'cabal run cfta-generator:cfta-explainfuzz -- sample grouped-filtered 7 12 +RTS -M2G -RTS'
```

The default invocation and `demo` request twelve grouped queries with seed 7.
`sample REQUIREMENT SEED COUNT` accepts seeds 0 through 1,000,000 and counts
1 through 10,000. `sample` writes SQL statements only to standard output, so
a test harness can consume them. `demo` also prints the event probability,
conditional probabilities, and the ambiguous-output fixture.
Unknown requirements, malformed arguments, and impossible
events exit with an error. `--help` prints the usage.

`check` exhausts the 45 ASTs. It checks unique rendered outputs, all four
nonempty event supports, exact conditional ratios, complete weighted
intervals, ordinary and weighted rank round trips, and 64 reproducible valid
draws per event. It also checks invalid input rejection, zero-mass rejection,
nonuniform learned grouping probability, and summed ambiguous-output mass.

Build and runtime results are pending the serialized capped validation.
