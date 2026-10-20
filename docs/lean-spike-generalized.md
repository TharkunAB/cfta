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

Use actual LTA guards in an editable `Language`. Store the language, theory,
value declarations, and ambient assumptions in one readable snapshot. Reload
the snapshot in a separate process. Check enumeration, rank/unrank, sampling,
and repeated-process rank stability. Compile the source graph directly, so
the query uses the same explicit graph before and after reloading.
Compare accepted programs with an independent Haskell interpretation.
Different programs can compute the same list. Their program ranks remain
distinct.

Use a shared arithmetic predicate, such as `between x lo hi`, to demonstrate
exact definition expansion and Z3 lowering. Check a Lean-only list obligation
that the lowering explicitly refuses. Check that a false list obligation is
rejected through a checked proof.

## Persistence on PR #89

Extend the standard language codec with named predicates and named sorts.
The language source retains every production, named fact, and exclusion.
`Data.CFTA.Lean.Serialization` adds a versioned envelope with the theory,
declarations, and assumptions. The context uses derived `Show` and `Read`.
Parsing does not contact a solver or execute native definitions.

`dump FILE` writes the complete source and reads it back before querying.
`reload FILE` uses only the stored source and context to reconstruct queries.
The example decodes program syntax with a small explicit decoder. It does
not serialize Haskell functions, an interned graph, or solver caches.

Native definitions retain references such as `List.reverse`. Their meaning
requires the same external Lean and Mathlib environment. Standard Kimina
does not expose an environment fingerprint. Use a fixed deployment when
replaying snapshots. The file does not contain the Lean toolchain or libraries.

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

The saved [complete example](lean-spike/list-programs.language) contains 35
candidate programs and both named requirements. The executable's `dump` and
fresh-process `reload` commands give identical output, including full annotated
terms. With the verbose term lines omitted, the output is:

```text
snapshot checksum: 1015509708
lowered interval: x >= 0 && x <= 3
interval via Z3: Yes
native list lowering refused: A native Lean function cannot be lowered
native list via lowering: Unknown
unsorted list via Kimina: No
reverse twice on any list: Yes
candidates: 35; accepted: 5
0 (size 2, class 0): Answer (Chunk [1,2]) => [1,2]
1 (size 3, class 0): Answer (Reverse (Chunk [2,1])) => [1,2]
2 (size 4, class 0): Answer (Append (Chunk [1,2]) (Chunk [])) => [1,2]
3 (size 4, class 1): Answer (Append (Chunk [1]) (Chunk [2])) => [1,2]
4 (size 4, class 2): Answer (Append (Chunk []) (Chunk [1,2])) => [1,2]
sample ranks: [0,0,1,4,3,4,3,0,1,3,0,0,3,4,2,0,1,0,0,0,0,1,3,0,2,3,4,3,1,0,4,4]
sample checksum: 1353331935
```

The example checks every accepted term's `(size, class rank)` inverse. It
samples uniformly over the five accepted ranks. The arbitrary-list statement
is `forall xs : List Int, reverse (reverse xs) = xs`. The LTA guards check
complete candidate values through entailment. The Haskell interpreter checks
the result independently; it does not filter the source after enumeration.

The direct graph ranks differ from the previous measured-generator example.
The source representation changed. Dump and reload preserve the ranks of this
source exactly. Both fresh runs used Nix Z3 4.15.3 and local Kimina with
Lean/Mathlib 4.26.0. The observed Mathlib checkout was
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. This is deployment provenance,
not an identity verified by the Kimina API.

After the rebase, the strict GHC 9.14.1 build and all 825 existing cases pass:
347 core, 252 generator, 180 refinement, 22 serialization, 8 Template Haskell,
and 16 Lean cases. Three hundred temporary structural codec cases pass. A
temporary snapshot probe preserves nonempty assumptions, escaped native
definitions, named facts, exclusions, a dead row, and subsequent edits. It
also rejects eight malformed or trailing inputs. The probes are not committed.
Changing only the saved `sorted` definition to `True` changes the reloaded
verdict from `No` to `Yes`, which fails the independent example check as
expected. This verifies that replay uses the stored interpretation.
Formatting, HLint, cabal-gild, package metadata, and source archive checks pass.

Before the rebase, the strict build and 762 existing cases passed, with 18
additional temporary regression cases. The temporary cases cover capture
avoidance, original argument types, native lowering refusal, ambient assumptions,
fresh sorts, predicate namespaces, and empty types. Their patch is
`/tmp/cfta-generalized-regressions.patch` on this host.

### Existing workload cost

Before the rebase on #89, all eight required cells kept their output checksums
and remained within the
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

Implementation is on `spike/refinement-logic`, rebased on PR #89 at `07a3c0f2`.
The source codec supports named predicates and sorts. The Lean snapshot stores
its theory, declarations, and assumptions beside the editable language. The
complete dump/reload example passes in two separate processes. All 825
existing cases and the additional temporary persistence probes pass.

## Restart

The worktree is `~/Code/microecta/lean-kimina`. PR #95 targets
`feature/languages`. The original branch is retained locally as
`backup/refinement-logic-before-pr89-20261020` at `5db7a2a0`. The replay retains
the final transport changes from merge `12273853`, which had joined main
`9769fe3e` and the old `lean-spike` checkpoint `3ab4caa6`.

Start the local Kimina service on port 8000. The complete commands are in
[cfta-lean/README.md](../cfta-lean/README.md#running-example). Use `dump FILE`
to construct and save the example, and `reload FILE` in a separate process.
The tracked snapshot can be passed directly to `reload`.

Use `CFTA_KIMINA_URL=http://127.0.0.1:8000` for the existing `lean-tests` suite.
Set process and RTS caps for all builds and tests. Read `cfta-lean/README.md`
for the API and unsupported forms.
