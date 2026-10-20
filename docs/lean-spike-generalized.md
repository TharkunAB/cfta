# Generalized refinements: spike

## Aim

Keep the logical skeleton of `Formula`. Let refinements describe typed values
and named predicates that are defined outside the arithmetic fragment.
Use Kimina to check Lean interpretations. Lower an obligation to Z3 only when
the translation preserves its meaning.

## Representation

Add `Predicate Name [Term]` and `NamedSort Name [Sort]`. Keep applications,
connectives, comparisons, and quantifiers. Keep the existing constructor order.
The names of predicates are global references. Value substitution changes their
arguments. It does not rename a predicate.

The Lean theory gives a named type its arity and Lean interpretation. It gives
a function or predicate its signature and Lean interpretation. A predicate can
instead have a body in the shared formula language. The formula stores names
and terms, not raw Lean source. Explicit Lean interpretations are trusted code.
The theory is fixed for an entailment solver and is part of the language's
meaning.

This spike keeps the `Formula` name and its existing automaton interfaces.
It generalizes the vocabulary. It does not parameterize the entire automaton
implementation over arbitrary syntax types.

## Solver lowering

`lower` validates a query, unfolds shared predicate definitions without
variable capture, and returns the supported Z3 fragment. It rejects remaining
native Lean definitions and named data sorts. The original query must be
well typed, even when expansion would remove an argument. Every declared
value remains in the Lean proposition. A named type can be empty, so dropping
an unused binder could change validity. Lowering rejects every named-sort
declaration, including unused ones.

Replacing a defined function with an uninterpreted function is not an exact
lowering. A countermodel could violate the function's definition. This spike
does not use such a countermodel as `No`.

Solver lowering is distinct from the template lowering of language towers.
It translates logical obligations between backend representations.

## Running example

Use list chunks `[]`, `[1]`, `[2]`, `[1,2]`, and `[2,1]`. Interpret the value of
each chunk as a Lean `List Int`. Compose chunks with append and reverse.
Require the final list to be sorted and a permutation of `[1,2]`.

Use actual LTA guards and the existing measured-constructor path. Check
enumeration, rank/unrank, sampling, and repeated-process rank stability.
Compare accepted programs with an independent Haskell interpretation.
Different programs can compute the same list. Their program ranks remain
distinct.

Use a shared arithmetic predicate, such as `between x lo hi`, to demonstrate
exact definition expansion and Z3 lowering. Check a Lean-only list obligation
that the lowering explicitly refuses. Check that a false list obligation is
rejected through a checked proof.

## Boundaries

The example uses one observed value sort, `List Int`. The current LTA evaluator
copies the distinguished value sort to child values. Mixed observed value
sorts need further design.

This is a partial compiler for the shared language and its definitions.
It does not translate arbitrary Lean source or dependent types to SMT.
An undecided query remains `Unknown`. Exact enumeration must report it.
The proof portfolio is incomplete. It simplifies interpreted definitions,
then tries decidable evaluation and the existing arithmetic tactics.

`every` still counts open integer leaves through the arithmetic lattice.
A shared predicate must be expanded before use in that path. The finite
list example does not use `every`. The Haskell evaluator is an independent
check of this example. The library does not prove that a caller's Lean
interpretation agrees with its Haskell constructors.

## Validation

Run builds and tests in `nix-shell` through heavy-management. Use process and
RTS memory caps. Run existing suites and temporary regression probes. Record
measured costs and unresolved boundaries here before closing the spike.

## Results

The executable `refinement-logic-spike` produces:

```text
lowered interval: x >= 0 && x <= 3
interval via Z3: Yes
interval via Kimina: Yes
native list lowering refused: A native Lean function cannot be lowered
native list via lowering: Unknown
unsorted list via Kimina: No
reverse twice on any list: Yes
candidates: 35; accepted: 5
0: Answer (Chunk [1,2]) => [1,2]
1: Answer (Reverse (Chunk [2,1])) => [1,2]
2: Answer (Append (Chunk []) (Chunk [1,2])) => [1,2]
3: Answer (Append (Chunk [1]) (Chunk [2])) => [1,2]
4: Answer (Append (Chunk [1,2]) (Chunk [])) => [1,2]
sample checksum: 1605814441
```

Repeated fresh processes give identical output, ranks, and 32 seeded samples.
The example checks every accepted term's rank inverse. The arbitrary-list
statement is `forall xs : List Int, reverse (reverse xs) = xs`.
The generator's guard checks complete candidate values through LTA entailment.
It does not filter results afterward with the Haskell evaluator.

The strict GHC 9.14.1 build and 762 existing cases pass: 325 core cases,
241 generator cases, 180 refinement cases, and 16 Lean cases. Eighteen
additional temporary cases also pass. They cover capture avoidance, original
argument types, native lowering refusal, ambient assumptions, fresh sorts,
predicate namespaces, and empty types. The temporary cases are not committed.
Their patch is `/tmp/cfta-generalized-regressions.patch` on this host.
Live checks use local Kimina with Lean/Mathlib 4.26.0.

### Existing workload cost

All eight required cells keep their output checksums and remain within the
5% budget. The largest instruction increase is 0.088%. The largest allocation
increase is 0.086%. Both occur in `lta-automaton 4`.
[Full counts](lean-spike/generalized-cost.csv) compare the transport checkpoint
`12273853` with this spike.

| Cell | Instructions | Allocation |
| --- | ---: | ---: |
| `untyped-expression-speed fta 4` | -0.001% | 0.000% |
| `typed-expression-speed ecta 4` | 0.000% | 0.000% |
| `state-machine-trace-speed ranked 20` | +0.001% | 0.000% |
| `state-machine-trace-speed lta-do 20` | +0.027% | +0.023% |
| `state-machine-trace-speed lta-automaton 4` | +0.088% | +0.086% |
| `typed-expression-constraint-cost lta-eq 3` | +0.002% | 0.000% |
| `micro-bench 1` | -0.001% | 0.000% |
| `enumeration-speed 1` | -0.002% | 0.000% |

Both builds use GHC 9.14.1 with `--enable-optimization=2`. Compiler invocations
confirm `-O2`. Native runs use `+RTS -M4G -s -RTS`. Valgrind 3.22.0 counts
instructions with `--tool=cachegrind --cache-sim=no --branch-sim=no`.
The serial job has a 16 GiB process cap and no swap. It runs in `nix-shell`.
The compiler has a 12 GiB RTS cap. No wall-clock comparison is used.

The host-linker PATH workaround selected system Z3 4.8.12 for both benchmark
builds and runs. Cachegrind does not instrument the Z3 child process. These
numbers measure the change to existing client and generator workloads; they
do not measure Kimina proof latency. The corrected restart command below
preserves Nix's Z3 4.15.3. The final integration check uses that version too.

Raw logs, compiler commands, and both plans are in
`/tmp/cfta-generalized-perf`. The runner is `/tmp/cfta-generalized-bench.sh`.
Run each cell once natively for allocation and once under cachegrind for
instructions. Compare every checksum, including each micro/enumeration row.

## Status

Implementation is on `spike/refinement-logic`, based on `12273853`.
The spike and optimized eight-cell cost comparison pass. All 762 existing
cases and 18 temporary probes pass with both system Z3 4.8.12 and Nix Z3
4.15.3. The rebuilt example gives the same ranks and samples with both.
The tracked tests are unchanged. The work remains local; nothing is pushed.

## Restart

The worktree is `~/Code/microecta/lean-kimina`. The transport checkpoint
`12273853` merges cfta main `9769fe3e` with the old `lean-spike` checkpoint
`3ab4caa6`. The generalized refinement spec starts at `1d7adab2`.

Start the local Kimina service on port 8000. Run the example with:

```sh
~/Code/heavy-management/bin/heavy --mem 8G --time 20m \
  nix-shell --run 'z3_bin=$(dirname "$(command -v z3)"); export PATH="$z3_bin:/usr/bin:$PATH"; cabal run refinement-logic-spike -- +RTS -M1G -RTS'
```

Use `CFTA_KIMINA_URL=http://127.0.0.1:8000` for the existing `lean-tests` suite.
Set process and RTS caps for all builds and tests. Read `cfta-lean/README.md`
for the API and unsupported forms.
